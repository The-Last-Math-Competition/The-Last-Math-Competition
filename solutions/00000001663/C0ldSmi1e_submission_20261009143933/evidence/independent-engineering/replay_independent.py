#!/usr/bin/env python3
"""Independent source replay; writes only under the reviewer evidence directory."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
BASE=Path(__file__).resolve().parent
SNAP=BASE/'snapshot'
RUNTIME=Path('/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64')
LIBRARY=Path('/private/tmp/tlmc-standard-library-419')
LEAN=RUNTIME/'bin/lean'
BUILD=BASE/'owned-build'
LOG=BASE/'logs'
LOG.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((SNAP/'lake-manifest.json').read_text())
packages=[p['name'] for p in manifest['packages']]
if BUILD.exists(): raise RuntimeError('Refusing nonfresh owned build')
BUILD.mkdir()
ENV=os.environ.copy()
ENV['PATH']=str(RUNTIME/'bin')+os.pathsep+ENV.get('PATH','')
paths=[BUILD]+[LIBRARY/p/'.lake/build/lib/lean' for p in packages]
ENV['LEAN_PATH']=os.pathsep.join(map(str,paths))
(BASE/'environment.json').write_text(json.dumps({'runtime':str(RUNTIME),'LEAN_PATH':ENV['LEAN_PATH'],'initial_owned_build_files':list(map(str,BUILD.iterdir()))},indent=2)+'\n')
commands=[]
def run(label,args,expect=0,cwd=SNAP):
    start=time.time()
    result=subprocess.run(list(map(str,args)),cwd=cwd,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (LOG/(label+'.log')).write_text(result.stdout)
    rec={'label':label,'command':list(map(str,args)),'cwd':str(cwd),'exit_code':result.returncode,'expected':expect,'seconds':time.time()-start,'log_sha256':sha(LOG/(label+'.log'))}
    commands.append(rec)
    (BASE/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    print(label, 'exit='+str(result.returncode),flush=True)
    if (expect==0 and result.returncode!=0) or (expect=='nonzero' and result.returncode==0): raise RuntimeError(label+' failed expectation; see log')
    return result.stdout
def compile_module(mod):
    rel=mod.replace('.','/')
    out=BUILD/rel
    out.parent.mkdir(parents=True,exist_ok=True)
    return run('build-'+mod,[LEAN,'-DwarningAsError=true','-o',str(out)+'.olean','-i',str(out)+'.ilean','-c',str(out)+'.c',rel+'.lean'])
run('lean-version',[LEAN,'--version'])
run('lean-githash',[LEAN,'--githash'])
for mod in ['Conjecture1663.Definitions','Conjecture1663.Proof','Conjecture1663.Challenges','Conjecture1663','Verification']:
    compile_module(mod)
template=(BASE/'AuditTemplate.lean.txt').read_text()
auditsrc=template.replace('__IMPORTS__','import Verification').replace('__OWNED__','#[`Conjecture1663.Definitions, `Conjecture1663.Proof, `Conjecture1663.Challenges, `Conjecture1663, `Verification]')
(BASE/'IndependentAudit.lean').write_text(auditsrc)
run('independent-audit',[LEAN,'-DwarningAsError=true',BASE/'IndependentAudit.lean'],cwd=BASE)
run('author-audit',[LEAN,'-DwarningAsError=true','scripts/Audit.lean'])
run('finite-checks',['python3','scripts/finite_checks.py'])
print('FRESH_SOURCE_REPLAY_PASS',flush=True)
