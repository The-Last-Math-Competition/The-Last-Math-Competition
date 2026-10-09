#!/usr/bin/env python3
"""Create an exact-inventory, source/log-only reviewer evidence export."""
from pathlib import Path
import hashlib,json,shutil,time
BASE=Path(__file__).resolve().parent
DEST=BASE/'delivery'
assert not DEST.exists()
DEST.mkdir()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,rel):
    assert src.is_file() and not src.is_symlink(),src
    dst=DEST/rel; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,dst)
root_files=[
 'REVIEW.md','RESULT.json','SNAPSHOT_SHA256.json','commands.json','environment.json',
 'package-pins.json','runtime-fingerprints.json','imported-module-fingerprints.json',
 'fresh-owned-object-fingerprints.json','owned-declarations.tsv','classified-owned-inventory.tsv',
 'reachable-declarations.tsv','dependency-edges.tsv','source-scan.json',
 'author-auxiliary-snapshot.json','author-automation-commands.json','author-fresh-replay-receipt.json',
 'author-fresh-replay-location.json','core-final-freeze-comparison.json','python-cache-observation.json',
 'AuditTemplate.lean.txt','replay_independent.py','controls_and_receipt.py','run_author_automation.py','export_review.py',
 'prior-author-automation-commands.json','prior-author-fresh-replay-receipt.json','prior-author-fresh-replay-location.json',
 'prior-run_author_automation.py',
]
for f in root_files: copy(BASE/f,f)
copy(BASE/'IndependentAudit.lean','IndependentAudit.lean.txt')
for folder in ['input','snapshot','logs']:
    for p in sorted((BASE/folder).rglob('*')):
        if p.is_file(): copy(p,str(p.relative_to(BASE)))
fixturemap=[]
for p in sorted((BASE/'controls').glob('*.lean')):
    rel='archived-controls/'+p.name+'.txt'; copy(p,rel)
    fixturemap.append({'executed_source':str(p),'exported_fixture':rel,'sha256':sha(p),'purpose':'Deliberate negative control or control audit; not a build root.'})
for p in sorted((BASE/'failed-attempts').rglob('*')):
    if not p.is_file() or 'owned-build' in p.parts or 'build' in p.parts: continue
    if p.suffix in ['.olean','.ilean','.c','.pyc']: continue
    rel=str(p.relative_to(BASE))
    if p.suffix=='.lean':
        rel+='.txt'; fixturemap.append({'executed_source':str(p),'exported_fixture':rel,'sha256':sha(p),'purpose':'Preserved failed reviewer attempt, not a build root.'})
    copy(p,rel)
(DEST/'control-fixture-map.json').write_text(json.dumps(fixturemap,indent=2)+'\n')
loc=json.loads((BASE/'author-fresh-replay-location.json').read_text())
receipt=Path(loc['receipt'])
def evidence_run(receipt,out):
    r=json.loads(receipt.read_text()); copy(receipt,out+'/receipt.json')
    for rel,h in r['evidence_hashes'].items():
        p=receipt.parent/rel; assert sha(p)==h,(p,h); copy(p,out+'/'+rel)
evidence_run(receipt,'author-automation-evidence/fresh-replay')
neg=BASE/'author-auxiliary-copy/evidence/negative-controls/results.json'
results=json.loads(neg.read_text()); copy(neg,'author-automation-evidence/negative-controls/results.json')
for c in results['controls']:
    if 'receipt' in c: evidence_run(Path(c['receipt']),'author-automation-evidence/negative-controls/fresh-replay')
for p in sorted((BASE/'author-auxiliary-copy/scripts').glob('*')):
    if p.is_file() and p.suffix in ['.py','.lean']: copy(p,'author-automation-sources/'+p.name+('.txt' if p.suffix=='.lean' else ''))
assert not any(p.is_symlink() for p in DEST.rglob('*'))
assert not any(p.suffix in ['.olean','.ilean','.pyc','.dylib'] for p in DEST.rglob('*') if p.is_file())
assert not any(p.name in ['__pycache__','.lake'] for p in DEST.rglob('*'))
result=json.loads((BASE/'RESULT.json').read_text())
receipt_data={'status':'INDEPENDENT_ENGINEERING_PASS','created_unix':time.time(),'author_manifest_sha256':result['author_delivery_manifest_sha256'],'independent_math_freeze_sha256':sha(BASE/'snapshot/evidence/MATH_FROZEN.json'),'independent_audit_sha256':sha(BASE/'logs/independent-audit.log'),'source_only_author_replay_receipt_sha256':sha(receipt),'summary':result,'export_contains_compiled_objects':False,'export_contains_symlinks':False,'export_contains_caches':False,'historical_receipts_omit_referenced_objects':True}
(DEST/'RECEIPT.json').write_text(json.dumps(receipt_data,indent=2)+'\n')
files={str(p.relative_to(DEST)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(DEST.rglob('*')) if p.is_file()}
(DEST/'FILES.json').write_text(json.dumps(files,indent=2)+'\n')
actual={str(p.relative_to(DEST)) for p in DEST.rglob('*') if p.is_file()}
assert actual==set(files)|{'FILES.json'}
for rel,row in files.items(): assert sha(DEST/rel)==row['sha256']
summary={'delivery':str(DEST),'manifest':'FILES.json','manifest_sha256':sha(DEST/'FILES.json'),'files_excluding_manifest':len(files),'total_bytes_excluding_manifest':sum(x['bytes'] for x in files.values()),'receipt_sha256':sha(DEST/'RECEIPT.json'),'review_sha256':sha(DEST/'REVIEW.md')}
(BASE/'DELIVERY_RECEIPT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
