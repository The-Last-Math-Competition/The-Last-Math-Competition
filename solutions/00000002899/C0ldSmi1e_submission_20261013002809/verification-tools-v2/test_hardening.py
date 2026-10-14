#!/usr/bin/env python3
"""Candidate-independent adversarial tests of the actual verifier methods."""
import importlib.util, json, pathlib, shutil, sys, tempfile
P=pathlib.Path
spec=importlib.util.spec_from_file_location('actual_verifier', P(__file__).with_name('verify.py'))
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
root=P(sys.argv[1]);root.mkdir(parents=True,exist_ok=False)
results=[]
def rejected(name, action, message):
    try: action()
    except AssertionError as e:
        assert message in str(e), (name,str(e))
        results.append({'fixture':name,'rejected':True,'reason':str(e)})
    else: raise AssertionError('Unexpected acceptance: '+name)

r=v.Review.__new__(v.Review)
r.out=root/'evidence';r.out.mkdir()
r.project=root/'project';r.project.mkdir()
r.lib=r.project/'lib';r.lib.mkdir()
r.stock=root/'stock';r.stock.mkdir()
r.leanbin=root/'runtime/bin';r.leanbin.mkdir(parents=True)
runtime=r.leanbin.parent/'lib/lean';runtime.mkdir(parents=True)
r.env={}
packages=root/'packages';packages.mkdir()
# Unexpected generated project modules cannot enter the proof import path.
(r.lib/'Hidden.olean').write_bytes(b'fixture')
rejected('unexpected_owned_output',lambda:r.owned_outputs([], 'unexpected.json'),'Unexpected owned-library module')
(r.lib/'Hidden.olean').unlink()
# Owned output and stock/runtime output for one module is an identity ambiguity.
(r.lib/'Shadow.olean').write_bytes(b'owned')
(runtime/'Shadow.olean').write_bytes(b'runtime')
r.env['LEAN_PATH']=str(r.lib)
rejected('owned_import_shadow',lambda:r.import_identities(['Shadow'], ['Shadow'], {'packages':[]}, packages, {}),'Shadowed or ambiguous')
(r.lib/'Shadow.olean').unlink()
# A package cache entry needs a pinned tracked source and its pre-build cache bytes.
cache=packages/'mathlib/.lake/build/lib/lean';cache.mkdir(parents=True)
stock_cache=r.stock/'.lake/build/lib/lean';stock_cache.mkdir(parents=True)
(cache/'FreshFixture.olean').write_bytes(b'cache')
(stock_cache/'FreshFixture.olean').write_bytes(b'cache')
(r.stock/'FreshFixture.lean').write_text('def fixture : Nat := 0\n')
(r.out/'stock').mkdir()
v.save(r.out/'stock/mathlib.json', [])
manifest={'packages':[{'name':'mathlib'}]}
r.env['LEAN_PATH']=str(r.lib)+':'+str(cache)
pre={'mathlib':{'FreshFixture.olean':v.sha(cache/'FreshFixture.olean')}}
rejected('untracked_package_source',lambda:r.import_identities(['FreshFixture'], [], manifest, packages, pre),'Untracked package module source')
v.save(r.out/'stock/mathlib.json',[{'file':'FreshFixture.lean','sha256':v.sha(r.stock/'FreshFixture.lean')}])
(cache/'FreshFixture.olean').write_bytes(b'changed')
rejected('changed_package_cache',lambda:r.import_identities(['FreshFixture'], [], manifest, packages, pre),'Changed/unrecognized package cache import')
# Review-time mutation of copied frozen source is rejected.
(r.project/'FreshFixture.lean').write_text('changed')
rejected('changed_copied_source',lambda:r.frozen_copy_stability({'FreshFixture.lean':'0'*64}),'Review input copy changed')
# The actual verify entry point rejects a changed supplied pin before loading source.
pins=root/'pins';pins.mkdir();submission=root/'submission';submission.mkdir()
for target in (pins,submission):
    (target/'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
    (target/'lake-manifest.json').write_text('{}\n')
(submission/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
rejected('changed_exact_pin',lambda:r.verify(submission,root/'not-read.json',pins),'Pinned input differs')
# Multiline kernel-bypass directives cannot evade the whole-source token scan.
active=v.code_only('set_option\n debug.skipKernelTC true\n')
assert v.FORBIDDEN.search(active)
assert not v.FORBIDDEN.search(v.code_only('/- axiom /- unsafe -/ sorry -/\n-- admit\ndef s := "native_decide"\n'))
results.append({'fixture':'multiline_forbidden_and_comment_string_controls','passed':True})
v.save(root/'results.json',results)
print(json.dumps(results,indent=2))
