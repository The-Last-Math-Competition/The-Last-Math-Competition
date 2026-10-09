#!/usr/bin/env python3
"""Execute frozen author automation only in the independent reviewer's copy."""
from pathlib import Path
import hashlib,json,os,subprocess,time
BASE=Path(__file__).resolve().parent
COPY=BASE/'author-auxiliary-copy'
LOG=BASE/'logs'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((BASE/'author-auxiliary-snapshot.json').read_text())
for f,h in frozen['files'].items():
 if '__pycache__' not in f and f!='evidence/negative-controls/results.json': assert sha(COPY/f)==h,(f,h)
for f,h in json.loads((COPY/'evidence/DELIVERABLE_HASHES.json').read_text()).items():
 if f!='evidence/negative-controls/results.json': assert sha(COPY/f)==h,f
records=[]
runenv=os.environ.copy(); runenv['PYTHONDONTWRITEBYTECODE']='1'
assert not (COPY/'scripts/__pycache__').exists()
for label,args in [
 ('author-final-replay',['python3','scripts/replay.py']),
 ('author-final-negative-controls',['python3','scripts/negative_controls.py']),
 ('author-final-source-check',['python3','scripts/source_check.py','--packages','/private/tmp/tlmc-standard-library-419']),
]:
 label='source-only-'+label
 start=time.time()
 result=subprocess.run(args,cwd=COPY,env=runenv,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=LOG/(label+'.log'); log.write_text(result.stdout)
 records.append({'label':label,'command':args,'cwd':str(COPY),'exit_code':result.returncode,'elapsed_seconds':time.time()-start,'log_sha256':sha(log)})
 (BASE/'author-automation-commands.json').write_text(json.dumps(records,indent=2)+'\n')
 print(label,'exit='+str(result.returncode),flush=True)
 assert result.returncode==0,result.stdout
 if label=='source-only-author-final-replay':
  receipt=Path(json.loads(result.stdout)['receipt'])
  copied=BASE/'author-fresh-replay-receipt.json'; copied.write_bytes(receipt.read_bytes())
  (BASE/'author-fresh-replay-location.json').write_text(json.dumps({'receipt':str(receipt),'sha256':sha(receipt)},indent=2)+'\n')
for f,h in frozen['files'].items():
 # The negative-control results file is intentionally a newly executed output.
 if f=='evidence/negative-controls/results.json' or '__pycache__' in f: continue
 assert sha(COPY/f)==h,(f,h)
print('ALL_FROZEN_AUTHOR_AUTOMATION_PASS',flush=True)
