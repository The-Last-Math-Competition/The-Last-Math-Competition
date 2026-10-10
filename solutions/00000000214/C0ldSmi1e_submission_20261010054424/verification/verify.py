#!/usr/bin/env python3
"""Offline independent replay. No network; never writes the submission/stock tree.
Usage: python3 verify.py SUBMISSION STOCK_MATHLIB LEAN_BIN OUTPUT_DIRECTORY
Requires macOS clonefile-capable cp (-cR); use an unused output directory.
"""
import hashlib,json,os,pathlib,re,shutil,subprocess,sys,time
P=pathlib.Path
submission,stock,leanbin,out=map(lambda s:P(s).absolute(),sys.argv[1:])
out.mkdir(parents=True,exist_ok=False)
receipts=out/'receipts'; receipts.mkdir()
project=out/'project'; project.mkdir()
env=os.environ.copy(); env['PATH']=str(leanbin)+':'+env.get('PATH','')
for var in ['LEAN_PATH','LEAN_SRC_PATH','LAKE_HOME','LEAN_SYSROOT']:
    env.pop(var,None)
counter=0
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def save(p,data):p.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def run(args,cwd=project,expected=0):
    global counter
    counter+=1; prefix=receipts/f'{counter:04d}'; start=time.time()
    r=subprocess.run(list(map(str,args)),cwd=cwd,env=env,capture_output=True)
    prefix.with_suffix('.stdout').write_bytes(r.stdout); prefix.with_suffix('.stderr').write_bytes(r.stderr)
    save(prefix.with_suffix('.json'),{'argv':list(map(str,args)),'cwd':str(cwd),'exit_code':r.returncode,
        'expected_exit':expected,'elapsed_seconds':time.time()-start,'stdout_sha256':sha(prefix.with_suffix('.stdout')),
        'stderr_sha256':sha(prefix.with_suffix('.stderr')),'environment_overrides':{'PATH':env['PATH']},
        'lean_source_hashes':{str(p.relative_to(project)):sha(p) for p in project.rglob('*.lean') if '.lake' not in p.relative_to(project).parts}})
    if (expected==0 and r.returncode!=0) or (expected=='nonzero' and r.returncode==0):
        raise RuntimeError(f'Unexpected command exit ({counter}): {r.returncode}: {r.stdout.decode()} {r.stderr.decode()}')
    print(f'{counter:04d} exit={r.returncode} {args[-1]}',flush=True)
    return r.stdout.decode()

manifest=json.loads((submission/'SHA256SUMS.json').read_text())
hash_check={f:{'expected':h,'actual':sha(submission/f)} for f,h in manifest.items()}
save(out/'author-hash-check.json',hash_check)
assert all(x['actual']==x['expected'] for x in hash_check.values()),'Author manifest mismatch'
save(out/'canonical-hashes.json',{f:sha(submission/f) for f in ['SHA256SUMS.json','lake-manifest.json','lakefile.lean','lean-toolchain','TLMC214.lean','CheckAxioms.lean','report.tex',*map(str,[p.relative_to(submission) for p in sorted((submission/'TLMC214').glob('*.lean'))])]})
for name in ['TLMC214','TLMC214.lean','CheckAxioms.lean','lakefile.lean','lake-manifest.json','lean-toolchain']:
    src=submission/name; dst=project/name
    if src.is_dir():shutil.copytree(src,dst)
    else:shutil.copy2(src,dst)
package_manifest=json.loads((project/'lake-manifest.json').read_text())
assert package_manifest['packagesDir']=='.lake/packages'
for x in package_manifest['packages']:
    assert x['type']=='git' and re.fullmatch('[a-f0-9]{40}',x['rev'])
for f in ['lakefile.lean','lake-manifest.json','lean-toolchain']:
    assert not re.search(r'/private/|/Users/|/tmp/|file://|from\s+"', (project/f).read_text())
run([leanbin/'lean','--version'])
run([leanbin/'lake','--version'])
packages=project/'.lake/packages'; packages.mkdir(parents=True)
run(['/bin/cp','-cR',str(stock.resolve())+'/.',packages/'mathlib'])
for x in package_manifest['packages']:
    if x['name']!='mathlib':
        run(['/bin/cp','-cR',packages/'mathlib/.lake/packages'/x['name'],packages/x['name']])
identities=[]
for x in package_manifest['packages']:
    name=x['name']; src=stock if name=='mathlib' else stock/'.lake/packages'/name
    dst=packages/name
    head=run(['git','rev-parse','HEAD'],cwd=src).strip(); assert head==x['rev']
    assert run(['git','status','--porcelain','--untracked-files=no'],cwd=src).strip()==''
    assert run(['git','rev-parse','HEAD'],cwd=dst).strip()==head
    tracked=run(['git','ls-files','-z'],cwd=src).split('\0')
    rows=[]
    for f in filter(None,tracked):
        a,b=src/f,dst/f
        if a.is_file():
            sa,sb=sha(a),sha(b); assert sa==sb
            rows.append({'path':f,'sha256':sa})
    save(out/f'package-{name}-tracked.json',rows)
    identities.append({'name':name,'revision':head,'tracked_file_count':len(rows),
        'tracked_inventory_sha256':sha(out/f'package-{name}-tracked.json')})
save(out/'package-identities.json',identities)
assert not (project/'.lake/build').exists(),'Submission build artifacts must not be reused'
run([leanbin/'lake','build'])
for source in ['TLMC214/PartitionBounds.lean','TLMC214/Sequence.lean','TLMC214/Growth.lean','TLMC214/Disproof.lean','TLMC214.lean','CheckAxioms.lean']:
    run([leanbin/'lake','env','lean','-DwarningAsError=true',source])

# This generic inspector is copied from the exact approved operational-only file,
# and shipped alongside this script so future runs have no old-project dependency.
verification=project/'Verification';verification.mkdir()
shutil.copy2(P(__file__).parent/'ClosureAudit.lean.txt',verification/'ClosureAudit.lean')
(project/'.lake/build/lib/lean/Verification').mkdir()
run([leanbin/'lake','env','lean','-DwarningAsError=true','-o','.lake/build/lib/lean/Verification/ClosureAudit.olean','Verification/ClosureAudit.lean'])
audit='import TLMC214\nimport Verification.ClosureAudit\n#audit_kernel_modules [TLMC214.PartitionBounds, TLMC214.Growth, TLMC214.Sequence, TLMC214.Disproof, TLMC214] "declaration-audit.json"\n'
(project/'Audit.lean').write_text(audit)
run([leanbin/'lake','env','lean','-DwarningAsError=true','Audit.lean'])
shutil.copy2(project/'declaration-audit.json',out/'declaration-audit.json')
a=json.loads((out/'declaration-audit.json').read_text());assert not a['failures']
assert all(not d['unsafe_dependencies'] for d in a['declarations'] if not d['unsafe'])
assert {d['name'] for d in a['declarations']} >= {'TLMC214.disproof','TLMC214.positive_arbitrarily_late','TLMC214.backward_disproof'}

# Bind every external imported .olean and corresponding source to the stock
# identity; built submission modules are separately bound to current sources.
cache_rows=[]
for module in a['imported_modules']:
    rel=P(*module.split('.')); found=[]
    for ident in identities:
        name=ident['name']; dst=packages/name; src=stock if name=='mathlib' else stock/'.lake/packages'/name
        compiled=dst/'.lake/build/lib/lean'/rel.with_suffix('.olean')
        if compiled.is_file():
            original=src/'.lake/build/lib/lean'/rel.with_suffix('.olean')
            digest=sha(compiled);assert digest==sha(original)
            row={'module':module,'package':name,'olean_sha256':digest}
            source=src/rel.with_suffix('.lean')
            if source.is_file():row['source_sha256']=sha(source)
            cache_rows.append(row);found.append(name)
    assert len(found)<=1, f'Ambiguous cached import {module}: {found}'
    if not found and not module.startswith(('TLMC214','Verification')):
        compiled=leanbin.parent/'lib/lean'/rel.with_suffix('.olean')
        assert compiled.is_file(),f'Unbound imported module {module}'
        cache_rows.append({'module':module,'package':'Lean-runtime','olean_sha256':sha(compiled)})
save(out/'import-identities.json',cache_rows)

# Countermodels make the removed assumptions material: constant zero cannot be
# unbounded, and f(n)=n cannot lie below every positive affine slope.
controls={
 'missing_unbounded':'''import TLMC214
example : ∀ C : ℝ, ∃ _n : ℕ, C < (0 : ℝ) := by
  intro C
  exact ⟨0, by norm_num⟩
''',
 'missing_affine':'''import TLMC214
example : ∀ a : ℝ, 0 < a → ∀ b : ℝ, ∃ n : ℕ, (n : ℝ) < b + a * (n : ℝ) := by
  intro a ha b
  exact ⟨0, by nlinarith⟩
''',
 'wrong_sign':'''import TLMC214
example (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ TLMC214.thirdDifference n < 0 := by
  exact TLMC214.positive_arbitrarily_late N
''',
 'missing_growth_hypothesis':'''import TLMC214
example (f : ℕ → ℝ) (hz : ∀ n, 0 ≤ f n)
  (hu : ∀ C : ℝ, ∃ n, C < f n) :
  ¬ ∃ N : ℕ, ∀ n, N ≤ n → f (n+3)-3*f(n+2)+3*f(n+1)-f n < 0 := by
  exact Sequence214.not_eventually_negative_third f hz hu
''',
 'incomplete_proof':'''import TLMC214
example : TLMC214.EventualNegativity := by
  sorry
'''}
controls_dir=project/'Controls';controls_dir.mkdir()
for label,source in controls.items():
    path=controls_dir/(label+'.lean');path.write_text(source)
    run([leanbin/'lake','env','lean','-DwarningAsError=true',str(path.relative_to(project))],expected='nonzero')
(controls_dir/'Countermodels.lean').write_text('''import TLMC214
example : ¬ (∀ C : ℝ, ∃ _n : ℕ, C < (0 : ℝ)) := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  exact (lt_irrefl 0) hn
example : ¬ (∀ a : ℝ, 0 < a → ∀ b : ℝ, ∃ n : ℕ, (n : ℝ) < b + a * (n : ℝ)) := by
  intro h
  obtain ⟨n, hn⟩ := h 1 (by norm_num) 0
  simp at hn
''')
run([leanbin/'lake','env','lean','-DwarningAsError=true','Controls/Countermodels.lean'])

# Lexical findings are divided by executable scope; historical failed snapshots
# remain evidence and are never imported or built.
pattern=re.compile(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b|set_option\s+(?:debug\.skipKernelTC|trustLevel)|Lean\.ofReduceBool')
scan=[]
for p in submission.rglob('*'):
    rel=p.relative_to(submission)
    if not p.is_file() or '.lake' in rel.parts or p.suffix=='.pdf':continue
    try:content=p.read_text()
    except UnicodeDecodeError:continue
    matches=[{'line':i,'text':line} for i,line in enumerate(content.splitlines(),1) if pattern.search(line)]
    if matches:scan.append({'path':str(rel),'scope':'active-lean' if p.suffix=='.lean' and 'evidence' not in rel.parts else 'historical-or-documentation','matches':matches})
save(out/'source-token-audit.json',scan)
assert not [r for r in scan if r['scope']=='active-lean'],'Forbidden token in active source'
assert all(sha(submission/f)==h for f,h in manifest.items()),'Submission changed during verification'
save(out/'summary.json',{'status':'PASS','submission_manifest_sha256':sha(submission/'SHA256SUMS.json'),
    'packages':identities,'import_identity_count':len(cache_rows),'local_declaration_count':a['local_declaration_count'],
    'closure_declaration_count':a['closure_declaration_count'],'audit_failures':a['failures'],
    'runtime_helper_declarations':[d['name'] for d in a['declarations'] if d['unsafe']],
    'negative_controls':list(controls),'limitations':['Dependency compiled imports were checked byte-for-byte against supplied stock cache, not rebuilt from all dependency sources.','Runtime binary is supplied Lean 4.19.0, not independently bootstrapped.','PDF rendering and semantic review are separate.']})
print('PASS',flush=True)
