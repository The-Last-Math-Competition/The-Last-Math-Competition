#!/usr/bin/env python3
"""Test the audit's rejection path inside an already independent replay project.
Usage: python3 verify_audit_controls.py PROJECT LEAN_BIN UNUSED_OUTPUT_DIR
"""
import hashlib,json,os,pathlib,subprocess,sys,time
P=pathlib.Path
project,leanbin,out=map(lambda s:P(s).absolute(),sys.argv[1:])
out.mkdir(parents=True,exist_ok=False); fixtures=project/'AuditControls';fixtures.mkdir(exist_ok=False)
build=project/'.lake/build/lib/lean/AuditControls';build.mkdir()
env=os.environ.copy();env['PATH']=str(leanbin)+':'+env.get('PATH','')
for k in ['LEAN_PATH','LEAN_SRC_PATH','LAKE_HOME','LEAN_SYSROOT']:env.pop(k,None)
i=0
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,expected=0):
 global i
 i+=1; t=time.time(); r=subprocess.run(list(map(str,args)),cwd=project,env=env,capture_output=True)
 b=out/f'{i:03d}';b.with_suffix('.stdout').write_bytes(r.stdout);b.with_suffix('.stderr').write_bytes(r.stderr)
 b.with_suffix('.json').write_text(json.dumps({'argv':list(map(str,args)),'cwd':str(project),'exit':r.returncode,'expected':expected,'elapsed':time.time()-t,'source_hashes':{str(p.relative_to(project)):sha(p) for p in fixtures.glob('*.lean')}},indent=2)+'\n')
 assert (r.returncode==0 if expected==0 else r.returncode!=0),(r.stdout.decode(),r.stderr.decode())
 print(i,r.returncode,args[-1],flush=True)
 return r.stdout.decode()+r.stderr.decode()
cases={
 'CustomAxiom':'axiom counterfeit : False\ntheorem impossible : False := counterfeit\n',
 'AuthoredUnsafe':'unsafe def counterfeitUnsafe : Nat := 0\n',
 'NativeDecide':'import Mathlib.Tactic\ntheorem computed : (7 : Nat) + 5 = 12 := by native_decide\n'}
results=[]
for label,src in cases.items():
 (fixtures/(label+'.lean')).write_text(src)
 run([leanbin/'lake','env','lean','-DwarningAsError=true','-o',build/(label+'.olean'),fixtures/(label+'.lean')])
 output=out/(label+'.audit.json')
 check=f'import Verification.ClosureAudit\nimport AuditControls.{label}\n#audit_modules [AuditControls.{label}] "{output}"\n'
 (fixtures/(label+'Check.lean')).write_text(check)
 text=run([leanbin/'lake','env','lean','-DwarningAsError=true',fixtures/(label+'Check.lean')],expected='nonzero')
 audit=json.loads(output.read_text());assert audit['failures']
 if label=='CustomAxiom':assert any('forbidden axiom counterfeit' in x for x in audit['failures'])
 if label=='AuthoredUnsafe':assert any('unsafe dependency counterfeitUnsafe' in x for x in audit['failures'])
 if label=='NativeDecide':assert any('forbidden axiom' in x for x in audit['failures'])
 results.append({'case':label,'expected_rejection':True,'failures':audit['failures']})
 (out/(label+'.lean.txt')).write_text(src)
(out/'summary.json').write_text(json.dumps({'status':'PASS','cases':results},indent=2)+'\n')
print('PASS',flush=True)
