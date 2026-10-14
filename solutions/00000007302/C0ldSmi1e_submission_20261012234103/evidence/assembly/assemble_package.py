#!/usr/bin/env python3
"""Assemble only reviewed local artifacts; no builds, Git operations or network."""
import argparse
import datetime
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

R = Path(__file__).resolve().parent
D = R.parent
E = R/'independent-review/engineering'
TEX_HASH = '8961362dd0255d9a003ac505f1d5af1666ddce9645fe0c2ee88ec0f7d7023f7d'
PDF_HASH = 'db1a2c4b4ecc6f133cd8b0314e2e652a5d2ecbc0da0619c0ef1c19339f7ca2cb'
def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()
def load(path):
    return json.loads(path.read_text())
def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

README = '''# Conjecture 00000007302: the ordinary extreme-point density clause

This submission gives a formal counterexample to ordinary relative density of
the extreme points in a tensor nuclear-norm unit ball. The tensor space is the
actual real algebraic tensor product of three Euclidean two-dimensional spaces.
Its installed norm is proved equal to the infimum of the sums of products of
factor norms over all finite pure-tensor decompositions. The origin belongs to
the closed unit ball and lies outside the closure of its real extreme points.

The exact bilingual original is preserved in `conjecture.md`. Its convex-envelope
definition and additional parameter-space wording are incomplete. The result
addresses the ordinary necessary density clause. It does not reconstruct the
parameter-space clause, or assert a result about density of convex combinations
or density only in the boundary. See `report.pdf` and `report.tex` for the proof
and its interpretation limits.

The final Lean declarations are
`Conjecture7302.nuclear_extremePoints_not_relatively_dense` and
`Conjecture7302.nuclear_ball_counterexample`. This analytic proof needs no
numerical search or auxiliary numerical computation.

The project is pinned to Lean 4.19.0 and Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). All nine package revisions are
fixed in `lean/lake-manifest.json`; independently supplied copies are in
`evidence/expected-pins/`. From the package directory, with the pinned toolchain
and dependencies available:

```sh
cd lean
lake build
lake env lean -DwarningAsError=true DecompositionBridge.lean
lake env lean -DwarningAsError=true GenericExtreme.lean
lake env lean -DwarningAsError=true TensorNuclear.lean
lake env lean -DwarningAsError=true Conjecture7302.lean
lake env lean -DwarningAsError=true AxiomAudit.lean
lake env lean -DwarningAsError=true lakefile.lean
```

`AxiomAudit.lean` prints the axioms of all 21 selected capstones. The four
mathematical modules, this auxiliary, and all three project configuration files
are byte-identical to the independent review snapshot. `lean/.gitignore` excludes
local `.lake/` products. The package contains no dependency cache or compiled
Lean artifact.

`VERIFICATION.md` gives the full verification procedure, measured counts, and
trust limits. All 61 safe declaration roots use only `propext`, `Classical.choice`
and `Quot.sound`. The 15 generated unsafe compiler helpers, including three
unsafe specialization axioms, are explicitly inventoried outside every safe
root's closure. They are not proof assumptions.

`evidence/engineering-records.tar.gz` contains the complete retained raw
engineering records, including all 60 command receipts and their output, the
declaration graph, import identities, pinned-source inventories, controls and
runtime identities. `evidence/engineering-records-manifest.json` lists the path,
size and SHA-256 of every archived file. It excludes the private cloned project,
dependency caches and compiled artifacts. Unchanged generic verifier sources
are in `verification-tools-v2/`; final independent reviews are in
`evidence/reviews/`. The report's build receipt, log and four inspected page
images are in `evidence/report/`.

The source/report reviews and final all-page visual review are incorporated.
`package-preparation.json` records this assembly and its inputs; it is not a
replacement for the final package review or a fresh publication decision.
`SHA256SUMS` covers every package file except itself, including the preparation
record. The preparation record's content inventory excludes itself and
`SHA256SUMS`, preventing a hash cycle. From the package directory:

```sh
shasum -a 256 -c SHA256SUMS
```

The initial and final public-eligibility summaries are dated observations, not
maintainer acceptance. Publication requires the separate final package review
and a decision based on sufficiently current public state.
Historical receipts retain their original local paths for provenance; those
paths are not prerequisites for the portable `lake build` commands above.
'''

VERIFICATION = r'''# Verification of the 00000007302 submission

The independent engineering verdict is PASS. It covers frozen source identity,
fresh compilation of the owned source, package-source provenance, imported
artifact identity, declaration closure, operational controls and manual review
of configuration and auxiliary source. Mathematical interpretation was reviewed
separately. No numerical auxiliary calculation is needed.

| Check | Measured result |
| --- | --- |
| Frozen source/configuration files | 8, checked in 3 copies (24 SHA-256 matches) |
| Mathematical modules | 4 |
| Additional auxiliary module | AxiomAudit, replayed with warnings as errors |
| Lake configuration | Separately replayed with warnings as errors |
| Generic tool identities | 5 SHA-256 matches |
| Runtime binary/library identities | 8 |
| Pinned dependency packages | 9 |
| Pinned tracked package files | 7,507, checked against Git blob identities and private copies |
| Stable stock Git indexes | 9 |
| Unambiguously resolved imported modules | 4,063 |
| Retained command receipts | 60, with exit and stdout/stderr hashes checked |
| Owned declarations | 76 |
| Safe declaration roots | 61 |
| Generated unsafe runtime helpers | 15 (12 definitions and 3 compiler specialization axioms) |
| All reachable graph declarations | 18,364 |
| Declarations reachable from safe roots | 18,340 |
| Required safe capstones | 21 |
| Positive / rejection controls | 1 accepted / 5 rejected as intended |

The imported-module identities comprise 1,272 Lean-runtime modules, 2,540 Mathlib,
130 Aesop, 78 Batteries, 12 Qq, 11 ProofWidgets, 8 Plausible, 4 LeanSearchClient,
2 ImportGraph and 6 owned modules (the five source modules plus the inspector).

The independent stock was cloned from generic pinned stock, without author
compiled outputs. Three missing imports were built from pinned Mathlib source:
`Mathlib.LinearAlgebra.Multilinear.TensorProduct`,
`Mathlib.LinearAlgebra.PiTensorProduct`, and
`Mathlib.Analysis.NormedSpace.PiTensorProduct.ProjectiveSeminorm`.
The receipt is `evidence/stock-preparation/build-receipt.json`. Other imported
dependency artifacts were cached; this review did not rebuild all Mathlib or
bootstrap Lean.

The independent run built a fresh private project with `lake --no-cache --wfail
build`, producing the four mathematical modules. It directly replayed all five
owned Lean modules in dependency order with `-DwarningAsError=true`, including
the nondefault `AxiomAudit.lean`, and separately replayed `lakefile.lean` with
the same warning policy. The sources remained byte-identical to the freeze.
Manual review found declarative Lake configuration, ordinary mathematical
definitions/proofs and `#print axioms` only; no authored IO, initialization,
unsafe declarations, custom axioms or trust-bypass settings were present.

The declaration inspector selects every declaration by originating module,
including generated declarations. It follows constants from types, values
(including opaque values), recursor rules and inductive/constructor relations.
The independent Python checker recomputes all graph closures and trust summaries.
All 61 safe roots and all 21 selected capstones have only the foundational axioms
`propext`, `Classical.choice` and `Quot.sound`, with no unsafe or unavailable
dependency. Source compilation supplies kernel checking; the graph checker is
not another independent proof kernel.

The generated runtime inventory is retained in full. It has 15 unsafe helpers,
including three specialization axioms for `Function.update` and `List.mapTR.loop`.
Its 45 runtime-only findings also mention compiler proof erasure `lcProof` and
four unavailable erased-runtime names. These are explicitly classified in
`evidence/reviews/runtime-helper-classification.json`. None is in any safe-root
closure. The raw run's `PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION` status is
resolved by this separate classification and the engineering verdict. There is
no claim that compiler runtime roots themselves satisfy the mathematical axiom
policy, and no runtime-only computation is used as proof evidence.

The freshly created operational controls checked: an ordinary safe fixture
(accepted), an unrelated custom axiom (rejected), an axiom hidden through an
opaque value (rejected), `sorry` (rejected both by warnings-as-errors and by the
dependency audit), `native_decide` (rejected for `Lean.ofReduceBool` and
`Lean.trustCompiler`), and an explicitly unsafe definition (rejected). All source,
graph, expected-exit and output checks passed. The generic v2 tools are copied
unchanged; their performance-only provenance records contain no prior problem
mathematical source.

The author receipts are separately retained in `evidence/author/verification/`.
They document development checks, not the independent review. The pre-development
`runtime-setup.json` records an earlier Lake-file hash; the later author freeze,
review snapshot and actual independently replayed final Lake file all match.
`evidence/frozen-review-manifest.json` is the authoritative eight-file freeze,
with the author manifest linked by hash. The auxiliary was additionally frozen
from the author's `AxiomAudit.lean`.

## Reproducing the complete independent verifier

The included verifier uses the macOS `/bin/cp -cR` clone workflow. It requires
a prepared stock Mathlib checkout and its eight pinned subdependencies/cached
imports, plus the Lean 4.19.0 `bin` directory. Supply those independently, check
them against the included pins, and use a NEW output directory which does not
exist. No cached dependencies or Lean binaries are distributed in this package.
The Python interpreter must run with assertions enabled (do not use `python -O`).

From this package directory, set the four paths in the shell and run:

```sh
package_dir="$PWD"
stock_dir="/absolute/path/to/pinned-stock"
lean_bin="/absolute/path/to/lean-4.19.0/bin"
new_output="/absolute/path/to/NEW-review-output"
python3 "$package_dir/verification-tools-v2/verify.py" verify \
  "$package_dir/lean" \
  "$package_dir/evidence/frozen-review-manifest.json" \
  "$stock_dir" "$lean_bin" "$new_output" \
  "$package_dir/evidence/expected-pins"
python3 "$package_dir/verification-tools-v2/check_audit_graph.py" \
  "$new_output/declaration-audit.json"
```

This full verifier performs its own strict build, source replay, import binding
and fresh controls. Manually review any generated unsafe helpers in the new
output, as was done for this run. It uses PATH safeguards against network tools
and Git writes; these are not operating-system network isolation. The stock,
Lean runtime and submission inputs are treated as read-only; the fresh output
contains private clones and products.

For the ordinary source check, `README.md` lists `lake build`, strict replay of
each of the five owned source modules and the Lake configuration, and the
axiom-printing command. Dependency acquisition may be needed if the pinned
dependencies are not already available. Preserve the supplied manifest; do not
update its package revisions.

## Inspecting the retained raw records

Extract into a new directory with Python's data extraction filter:

```sh
package_dir="$PWD"
records_dir="/absolute/path/to/NEW-records-directory"
python3 - "$package_dir/evidence/engineering-records.tar.gz" "$records_dir" <<'PY'
import pathlib, sys, tarfile
target = pathlib.Path(sys.argv[2])
target.mkdir(parents=True, exist_ok=False)
with tarfile.open(sys.argv[1], 'r:gz') as archive:
    archive.extractall(target, filter='data')
PY
python3 "$package_dir/verification-tools-v2/check_audit_graph.py" \
  "$records_dir/engineering/declaration-audit.json"
```

The tar members are ordinary files under `engineering/`, in sorted order with
normalized metadata and a zero gzip timestamp. Their hashes and sizes are in
`evidence/engineering-records-manifest.json`. The archive has all 60 receipt
triples, all 18 package source/cache-identity JSON inventories, six control
graphs, the complete declaration graph, frozen/pin/build-output identities,
the copied driver, and the offline safeguard scripts. Actual dependency caches,
the cloned project and compiled artifacts are omitted. Historical review scripts
and receipts retain original paths and are evidence of this run; use the generic
CLI above to reproduce in a different local layout.

## Report and remaining scope

The final report source hash is
`8961362dd0255d9a003ac505f1d5af1666ddce9645fe0c2ee88ec0f7d7023f7d`;
the PDF hash is
`db1a2c4b4ecc6f133cd8b0314e2e652a5d2ecbc0da0619c0ef1c19339f7ca2cb`.
The final native and Tectonic compilations succeeded. The report source's
mathematical content and exact typography-only amendment were independently
reviewed. Root visually inspected all four final PDF pages, including the
Chinese quotation; the checked page images and record are included.

This establishes the stated ordinary relative-nondensity result on the reviewed
source. It does not resolve the original's undefined parameter-space clause,
prove the implementation of Lean correct, rebuild all cached dependencies, or
constitute maintainer acceptance. The included initial eligibility summary and
final public-guard review are dated observations. The latter records 2,806
independently validated checks. Final package review and publication remain
separate decisions; later public changes require a new eligibility check.
'''

def finalize(package, input_rows, archive_manifest, assembled_at):
    frozen = load(R/'frozen-review-manifest.json')
    for name, digest in frozen['files'].items():
        assert sha(package/'lean'/name) == digest
    assert sha(package/'report.tex') == TEX_HASH and sha(package/'report.pdf') == PDF_HASH
    assert sha(package/'conjecture.md') == load(R/'clean-author-input/INPUT_MANIFEST.json')['files']['00000007302.md']
    report_review = load(package/'evidence/reviews/report-review.json')
    visual = load(package/'evidence/report/visual-review.json')
    assert report_review['report_sha256'] == TEX_HASH and report_review['verdict'].startswith('PASS')
    assert visual['tex_sha256'] == TEX_HASH and visual['pdf_sha256'] == PDF_HASH and visual['status'].startswith('PASS')
    for n, digest in visual['pages'].items():
        assert sha(package/'evidence/report'/f'inspected-{n}.png') == digest
    inventory = []
    for path in sorted(package.rglob('*')):
        if path.is_file() and path.name not in {'SHA256SUMS','package-preparation.json'}:
            assert not path.is_symlink()
            inventory.append({'path':path.relative_to(package).as_posix(),'size':path.stat().st_size,'sha256':sha(path)})
    assert not any(Path(r['path']).suffix in {'.olean','.ilean','.o','.a','.so','.dylib'} for r in inventory)
    record = {'status':'ASSEMBLED_WITH_FINAL_REVIEWS_PENDING_ROOT_PACKAGE_REVIEW',
              'candidate':'00000007302', 'assembled_at':assembled_at, 'finalized_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'package_directory':str(package), 'assembly_script_sha256':sha(Path(__file__)),
              'frozen_manifest_sha256':sha(R/'frozen-review-manifest.json'),
              'report_tex_sha256':TEX_HASH,'report_pdf_sha256':PDF_HASH,
              'copied_input_files':input_rows,
              'content_inventory_excluding_this_record_and_SHA256SUMS':inventory,
              'content_file_count':len(inventory),'content_bytes':sum(r['size'] for r in inventory),
              'outer_manifest_rule':'SHA256SUMS hashes every regular package file except SHA256SUMS itself, including this preparation record. This record excludes itself and SHA256SUMS from its own inventory to avoid a cycle.',
              'archive':{'path':'evidence/engineering-records.tar.gz','sha256':sha(package/'evidence/engineering-records.tar.gz'),
                         'size':(package/'evidence/engineering-records.tar.gz').stat().st_size,
                         'manifest_path':'evidence/engineering-records-manifest.json',
                         'manifest_sha256':sha(package/'evidence/engineering-records-manifest.json'),
                         'members':len(archive_manifest['files']), 'uncompressed_member_bytes':sum(r['size'] for r in archive_manifest['files']),
                         'command_receipts':60,'receipt_output_files':120,'stock_inventory_files':18},
              'final_records_incorporated':['engineering verdict and generated-helper classification','independent final source semantic review','root final source semantic review','final report review including typography amendment','final report build receipt and log','all-four-page visual review and exact inspected images','initial root eligibility summary and final independently validated public-guard review'],
              'pending':['Root independent review of this exact assembled package','Separate publication decision and any publication action'],
              'source_or_config_modified':False,'report_regenerated':False,'proof_build_repeated':False,'git_or_network_operation_performed':False,
              'exclusions':['Private cloned project and dependency caches','Compiled Lean artifacts and runtime binaries','Prior problem mathematical source','Public history whole catalog','Failed/intermediate report builds'],
              'notes':['Original absolute paths in historical receipts are retained for provenance.','lean/.gitignore is an added packaging file outside the eight-file proof/configuration freeze.','Package assembly and hashes are engineering evidence, not publication authorization.']}
    save(package/'package-preparation.json',record)
    files = [p for p in sorted(package.rglob('*')) if p.is_file() and p != package/'SHA256SUMS']
    (package/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(package).as_posix()}\n' for p in files))
    return record

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', type=Path, help='Recompute inventory and outer hashes after an explicitly reviewed local amendment; does not recopy artifacts.')
    args = parser.parse_args()
    if args.refresh:
        package = args.refresh.resolve()
        prior = load(package/'package-preparation.json')
        record = finalize(package, prior['copied_input_files'], load(package/'evidence/engineering-records-manifest.json'), prior['assembled_at'])
        print(json.dumps({'status':record['status'],'package':str(package),'files_in_outer_manifest':record['content_file_count']+1},indent=2))
        return
    now = datetime.datetime.now(datetime.timezone.utc)
    package = R/'package'/('C0ldSmi1e_submission_'+now.strftime('%Y%m%d%H%M%S'))
    package.mkdir(parents=True,exist_ok=False)
    input_rows = []
    def copy(source, relative):
        source = source.resolve()
        assert source.is_file() and not source.is_symlink()
        dest = package/relative
        dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,dest)
        assert sha(source)==sha(dest)
        input_rows.append({'source':str(source),'destination':relative,'size':dest.stat().st_size,'sha256':sha(dest)})
    frozen = load(R/'frozen-review-manifest.json')
    assert sha(R/'report/report.tex')==TEX_HASH and sha(R/'report/report.pdf')==PDF_HASH
    for name,digest in frozen['files'].items():
        assert sha(R/'review-source/lean'/name)==digest
        copy(R/'review-source/lean'/name,'lean/'+name)
    copy(R/'author/lean/.gitignore','lean/.gitignore')
    copy(R/'clean-author-input/00000007302.md','conjecture.md')
    for name in ['report.tex','report.pdf']:
        copy(R/'report'/name,name)
    for name in ['frozen-review-manifest.json','verification-readiness.json','root-phase1-semantic-review.json','root-preliminary-semantic-review.json','root-final-semantic-review.json','root-engineering-review.json']:
        copy(R/name,'evidence/'+name)
    for name in ['lean-toolchain','lake-manifest.json']:
        copy(R/'expected-pins'/name,'evidence/expected-pins/'+name)
    for name in ['INPUT_MANIFEST.json','RULES.en.md','RULES.zh.md']:
        copy(R/'clean-author-input'/name,'evidence/clean-author-input/'+name)
    copy(R/'clean-author-input/00000007302.md','evidence/clean-author-input/00000007302.md')
    copy(R/'root-eligibility-review.json','evidence/eligibility/root-eligibility-review.json')
    copy(R/'root-final-public-guard-review.json','evidence/eligibility/root-final-public-guard-review.json')
    for source in sorted((R/'author/verification').iterdir()):
        assert source.is_file()
        copy(source,'evidence/author/verification/'+source.name)
    copy(R/'author/runtime-setup.json','evidence/author/runtime-setup.json')
    copy(R/'independent-stock-preparation.json','evidence/stock-preparation/independent-stock-preparation.json')
    for name,dest in [('receipt.json','build-receipt.json'),('stdout.txt','build-stdout.txt'),('stderr.txt','build-stderr.txt')]:
        copy(R/'independent-stock-build'/name,'evidence/stock-preparation/'+dest)
    for name in ['phase1-semantic-review.txt','final-source-semantic-review.txt','report-review.json','source-config-review.json','engineering-verdict.json','engineering-checks.json','graph-check.json','runtime-helper-classification.json','recheck_engineering.py']:
        copy(R/'independent-review'/name,'evidence/reviews/'+name)
    for name in ['build-receipt.json','build-stdout.txt','build-stderr.txt','report.log','extracted-text.txt','visual-review.json',*[f'inspected-{n}.png' for n in range(1,5)]]:
        copy(R/'report'/name,'evidence/report/'+name)
    readiness = load(R/'verification-readiness.json')
    for name,digest in readiness['tool_hashes'].items():
        assert sha(D/'verification-tools-v2'/name)==digest
        copy(D/'verification-tools-v2'/name,'verification-tools-v2/'+name)
    for source,dest in [
        (D/'1030/independent-review/verifier-v2-review/review.txt','independent-performance-review.txt'),
        (D/'1030/independent-review/verifier-v2-review/differential-results.json','differential-results.json'),
        (D/'1030/independent-review/full-audit-v1-v2-comparison.json','full-run-performance-comparison.json')]:
        copy(source,'evidence/tool-provenance/'+dest)
    copy(Path(__file__),'evidence/assembly/assemble_package.py')
    raw = [p for p in sorted(E.rglob('*')) if p.is_file() and 'project' not in p.relative_to(E).parts]
    assert len(list((E/'receipts').glob('*.json')))==60
    assert len(list((E/'receipts').glob('*.stdout')))==len(list((E/'receipts').glob('*.stderr')))==60
    members = []
    archive = package/'evidence/engineering-records.tar.gz'
    with archive.open('wb') as stream, gzip.GzipFile(filename='',mode='wb',fileobj=stream,mtime=0,compresslevel=9) as compressed:
        with tarfile.open(fileobj=compressed,mode='w',format=tarfile.USTAR_FORMAT) as tar:
            for source in raw:
                assert not source.is_symlink()
                relative = 'engineering/'+source.relative_to(E).as_posix()
                data = source.read_bytes()
                info = tarfile.TarInfo(relative)
                info.size=len(data);info.mtime=0;info.uid=0;info.gid=0;info.uname='';info.gname=''
                info.mode=0o755 if 'offline-bin' in source.relative_to(E).parts else 0o644
                tar.addfile(info,io.BytesIO(data))
                members.append({'path':relative,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
    archive_manifest={'format':'deterministic gzip-compressed USTAR; sorted regular files; mtime=0; uid/gid=0; empty owner names; gzip mtime=0 and filename empty',
                      'source_directory':str(E),'member_count':len(members),'files':members,
                      'excluded':'project/** (private clones, dependency caches, compiled outputs and replay source copies; authoritative source is supplied separately in lean/)'}
    save(package/'evidence/engineering-records-manifest.json',archive_manifest)
    with tarfile.open(archive,'r:gz') as tar:
        assert [m.name for m in tar.getmembers()]==[r['path'] for r in members]
        for member,row in zip(tar.getmembers(),members):
            data=tar.extractfile(member).read()
            assert member.isfile() and len(data)==row['size'] and hashlib.sha256(data).hexdigest()==row['sha256']
    (package/'README.md').write_text(README)
    (package/'VERIFICATION.md').write_text(VERIFICATION)
    record=finalize(package,input_rows,archive_manifest,now.isoformat())
    print(json.dumps({'status':record['status'],'package':str(package),'files_in_outer_manifest':record['content_file_count']+1,'archive':record['archive']},indent=2))

if __name__=='__main__':
    main()
