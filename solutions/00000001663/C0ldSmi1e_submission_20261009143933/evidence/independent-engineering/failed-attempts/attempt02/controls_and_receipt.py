#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,time
BASE=Path(__file__).resolve().parent
SNAP=BASE/'snapshot'; BUILD=BASE/'owned-build'; LOG=BASE/'logs'
RUNTIME=Path('/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64')
LIBRARY=Path('/private/tmp/tlmc-standard-library-419'); LEAN=RUNTIME/'bin/lean'
env_record=json.loads((BASE/'environment.json').read_text())
ENV=os.environ.copy(); ENV['LEAN_PATH']=env_record['LEAN_PATH']; ENV['PATH']=str(RUNTIME/'bin')+os.pathsep+ENV.get('PATH','')
commands=json.loads((BASE/'commands.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(label,args,expect=0,cwd=SNAP,env=ENV):
    start=time.time(); r=subprocess.run(list(map(str,args)),cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (LOG/(label+'.log')).write_text(r.stdout)
    commands.append({'label':label,'command':list(map(str,args)),'cwd':str(cwd),'exit_code':r.returncode,'expected':expect,'seconds':time.time()-start,'log_sha256':sha(LOG/(label+'.log'))})
    (BASE/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    print(label,'exit='+str(r.returncode),flush=True)
    assert (r.returncode==0 if expect==0 else r.returncode!=0),r.stdout
    return r.stdout
assert 'AUDIT_PASS' in (LOG/'independent-audit.log').read_text()
run('lakefile-compile',[LEAN,'-DwarningAsError=true','-o',BASE/'lakefile.olean','lakefile.lean'])
CONTROL=BASE/'controls'; CONTROL.mkdir(exist_ok=True)
CB=CONTROL/'build'; CB.mkdir(exist_ok=True)
CE=ENV.copy(); CE['LEAN_PATH']=str(CB)+os.pathsep+ENV['LEAN_PATH']
fixtures={
 'ControlAdmit':'theorem admitted_false : False := by sorry\n',
 'PoisonOutside':'axiom outsideFalse : False\naxiom outsideType : Type\n',
 'ControlTransitive':'import PoisonOutside\nnoncomputable theorem transitive_false : False := outsideFalse\n',
 'ControlType':'import PoisonOutside\ninductive TypeOnly (x : outsideType) : Prop where\n  | mk : TypeOnly x\n',
 'ControlUnsafe':'unsafe def dangerous : Nat := 3\n',
 'ControlNative':'import Mathlib.Tactic\ntheorem compiler_fact : 1 + 1 = 2 := by native_decide\n',
 'ControlFalseWitness':'import Conjecture1663\nopen Conjecture1663\nexample : editDistance (⊥ : Graph 3) (⊥ : Graph 3) = 1 := by\n  simpa using editDistance_self (⊥ : Graph 3)\n',
 'ControlFalseProof':'example : False := by decide\n',
}
for n,s in fixtures.items(): (CONTROL/(n+'.lean')).write_text(s)
run('control-admit-warnings-error',[LEAN,'-DwarningAsError=true','ControlAdmit.lean'],'nonzero',CONTROL,CE)
# Compile the admitted fixture only to prove that the declaration auditor also catches it.
run('control-admit-permissive-build',[LEAN,'-o',CB/'ControlAdmit.olean','ControlAdmit.lean'],0,CONTROL,CE)
for n in ['PoisonOutside','ControlTransitive','ControlType','ControlUnsafe','ControlNative']:
    run('control-build-'+n,[LEAN,'-DwarningAsError=true','-o',CB/(n+'.olean'),n+'.lean'],0,CONTROL,CE)
template=(BASE/'AuditTemplate.lean.txt').read_text()
for n in ['ControlAdmit','ControlTransitive','ControlType','ControlUnsafe','ControlNative']:
    src=template.replace('__IMPORTS__','import '+n).replace('__OWNED__','#[`'+n+']')
    name='Audit'+n+'.lean'; (CONTROL/name).write_text(src)
    out=run('control-audit-'+n,[LEAN,'-DwarningAsError=true',name],'nonzero',CONTROL,CE)
    assert 'AUDIT_REJECT' in out
for n in ['ControlFalseWitness','ControlFalseProof']:
    run('control-compiler-'+n,[LEAN,'-DwarningAsError=true',n+'.lean'],'nonzero',CONTROL,CE)
audit=(LOG/'independent-audit.log').read_text().splitlines()
for tag,file in [('OWNED','owned-declarations.tsv'),('REACHABLE','reachable-declarations.tsv'),('EDGE','dependency-edges.tsv')]:
    (BASE/file).write_text('\n'.join(x for x in audit if x.startswith(tag+'\t'))+'\n')
mods=sorted({x.split('\t')[1] for x in audit if x.startswith('IMPORTED_MODULE\t')})
package_manifest=json.loads((SNAP/'lake-manifest.json').read_text())
names=[p['name'] for p in package_manifest['packages']]
object_roots=[BUILD]+[LIBRARY/p/'.lake/build/lib/lean' for p in names]+[RUNTIME/'lib/lean']
source_roots=[SNAP]+[LIBRARY/p for p in names]+[RUNTIME/'src/lean',RUNTIME/'src/lean/lake']
fingerprints=[]
for m in mods:
    rel=Path(*m.split('.'))
    objs=[root/rel.with_suffix('.olean') for root in object_roots if (root/rel.with_suffix('.olean')).is_file()]
    srcs=[root/rel.with_suffix('.lean') for root in source_roots if (root/rel.with_suffix('.lean')).is_file()]
    assert len(objs)==1,(m,objs)
    fingerprints.append({'module':m,'object_path':str(objs[0]),'object_sha256':sha(objs[0]),'source_available':bool(srcs),'available_sources':[{'path':str(s),'sha256':sha(s)} for s in srcs]})
(BASE/'imported-module-fingerprints.json').write_text(json.dumps(fingerprints,indent=2)+'\n')
runtime_files=[RUNTIME/'bin/lean',RUNTIME/'bin/lake']+sorted((RUNTIME/'lib/lean').glob('*.dylib'))
(BASE/'runtime-fingerprints.json').write_text(json.dumps([{'path':str(p),'sha256':sha(p)} for p in runtime_files],indent=2)+'\n')
ownedfiles=sorted(p for p in BUILD.rglob('*') if p.is_file())
(BASE/'fresh-owned-object-fingerprints.json').write_text(json.dumps([{'path':str(p.relative_to(BASE)),'sha256':sha(p)} for p in ownedfiles],indent=2)+'\n')
# Source declarations and disallowed syntax are reported separately from metaprogramming auditors.
proof_files=[SNAP/'Conjecture1663.lean',*sorted((SNAP/'Conjecture1663').glob('*.lean')),SNAP/'Verification.lean']
def erase_comments_strings(text):
    out=[]; i=0; nesting=0; string=False
    while i<len(text):
        if nesting:
            if text.startswith('/-',i): nesting+=1; i+=2
            elif text.startswith('-/',i): nesting-=1; i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\': i+=2
            elif text[i]=='"': string=False; i+=1
            else: i+=1
        elif text.startswith('/-',i): nesting=1; i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j==-1 else j
        elif text[i]=='"': string=True; i+=1
        else: out.append(text[i]); i+=1
    return ''.join(out)
banned=re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial|run_cmd|run_elab|implemented_by|extern)\b')
source_scan=[]
for p in proof_files:
    clean=erase_comments_strings(p.read_text())
    hits=[m.group() for m in banned.finditer(clean)]
    assert not hits,(p,hits)
    decls=re.findall(r'\b(?:theorem|def|abbrev|opaque|inductive|structure|instance)\s+([^\s:{(]+)',clean)
    source_scan.append({'path':str(p.relative_to(SNAP)),'sha256':sha(p),'banned_hits':hits,'written_declarations':decls})
(BASE/'source-scan.json').write_text(json.dumps(source_scan,indent=2)+'\n')
input_hashes=json.loads((BASE/'input/SHA256SUMS.json').read_text())
for f,h in input_hashes.items(): assert sha(BASE/'input'/f)==h
snapshot_hashes=json.loads((BASE/'SNAPSHOT_SHA256.json').read_text())
for f,h in snapshot_hashes.items(): assert sha(SNAP/f)==h
summary={'status':'INDEPENDENT_ENGINEERING_PASS','owned_declarations':sum(x.startswith('OWNED\t') for x in audit),'reachable_declarations':sum(x.startswith('REACHABLE\t') for x in audit),'type_value_edges':sum(x.startswith('EDGE\t') for x in audit),'imported_modules':len(mods),'available_module_sources':sum(x['source_available'] for x in fingerprints),'unavailable_module_sources':sum(not x['source_available'] for x in fingerprints),'audit_final':[x for x in audit if x.startswith('AUDIT_PASS')], 'all_input_and_snapshot_hashes_match':True,'limitations':['Cached dependency objects were reused, not rebuilt.','Sources and objects are individually fingerprinted; this does not establish source-to-binary reproducibility.','Lean runtime source files absent where source_available is false.','No publication, eligibility, proof about classical reconstruction, or artifact-format completeness is asserted.']}
(BASE/'RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
