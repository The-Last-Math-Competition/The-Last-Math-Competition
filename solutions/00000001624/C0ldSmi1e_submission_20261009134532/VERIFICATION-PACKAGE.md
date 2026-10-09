# Conjecture 00000001624: complete submission

The literal real-spectrum claim is false. Every closed real set with empty
interior and positive Lebesgue measure has a bounded complementary component
whose two endpoints belong to the set. Consequently a positive-measure Cantor
spectrum cannot have no internal gaps. The proof covers every potential type,
real spectrum assignment, and additional quasiperiodicity or spectral-measure
predicate.

This addresses absence of **all internal gaps**, as stated in both source
languages. It does not claim to settle a different statement about absence of
a gap only at one selected energy. No numerical approximation is involved.

## Read the argument

- [Complete LaTeX report](report.tex) and [matching three-page PDF](report.pdf).
- [Mathematical explanation, including the exact bilingual source](REPORT.md).
- [Source-to-formalization mapping](SOURCE-MAPPING.md).
- [Lean mathematical core](Conjecture1624.lean) and [eight formal challenge cases](Verification.lean).

The final theorems are `Conjecture1624.no_source_spectrum` and
`Conjecture1624.no_source_potential`. The gap is proved equal to an actual
connected component of the complement, not merely stipulated to be one.

## Reproduce verification

The project pins Lean 4.19.0 and Mathlib v4.19.0, with all nine dependency
commits fixed in `lake-manifest.json`. Install those pinned dependencies or
provide an existing directory containing them. In an expendable copy of this
submission, run:

```sh
python3 scripts/replay.py \
  --lean-bin /path/to/lean-4.19.0/bin \
  --stdlib-root /path/to/nine-pinned-packages

python3 scripts/check_stale_audit_rejection.py \
  --lean-bin /path/to/lean-4.19.0/bin \
  --stdlib-root /path/to/nine-pinned-packages

python3 verification/engineering/tests/test_replay.py --project .
```

The first command rebuilds both owned proof modules, replays sources with
warnings treated as errors, audits every owned/generated declaration and its
transitive dependencies, and fingerprints imported artifacts. It rejects
changed original inputs, altered dependency configuration, failed commands,
warnings, forbidden axioms, and unsafe or partial dependencies. It requires a
newly generated audit report and cannot reuse an old successful report.

The second command deliberately disables audit output in an isolated fixture.
The helper must succeed by observing the exact expected replay rejection;
the no-op Lean audit itself must have compiled successfully. The third command
runs the 20 verifier regression tests. These tests distinguish genuine command
execution from fixtures that isolate driver behavior.

The separate [engineering instructions](verification/engineering/README.md)
also reproduce three real Lean controls: an extra axiom, an unsafe declaration,
and a partial function are each introduced only into a copied project and
rejected by the audit. The partial-function control fails closed on generated
dependency `_obj`; this is not presented as a direct partial-flag classification.
The source is restored and the positive audit is checked again.

For the ordinary Lean commands and archive details, see the [author's build
instructions](README.md). For the report, compile `report.tex` with a standard
LaTeX setup; the delivered PDF was exported with Tectonic 0.17.0 and all three
pages were inspected after rendering with Poppler 26.05.0.

## Recorded results

- Clean builds and warning-as-error replays passed independently for the
  author, the mathematical reviewer, the verification engineer, and the root
  contributor.
- All eight kernel-checked challenge theorems passed. They cover positive
  gapless intervals, singleton measure, exact internal gaps and components,
  nonmaximal omitted intervals, reference-energy scope, closedness, and
  unrestricted extra predicates.
- The final audit covers **24 owned/generated declarations** and **27,632
  transitive declarations**. Its only axioms are `propext`, `Classical.choice`,
  and `Quot.sound`. It reports no forbidden axiom, unsafe dependency, or
  partial dependency. There are no admitted proofs or native decision
  procedures in the proof modules.
- All **20 verifier regression tests** passed. Three earlier driver defects
  were reproduced and fixed: incomplete input-checksum validation, unchecked
  dependency-manifest fields, and possible reuse of stale audit evidence.
- All three real injected-declaration controls were rejected, the restored
  positive audit passed, and the stale-audit integration challenge passed.
- The full report and the exact final PDF passed independent semantic and
  visual review. Every PDF page was inspected.

The complete mathematical dependency graph from the root and independent
reviewer replays equals the author's archived graph. All **3,430 imported
compiled modules** were fingerprinted. The root replay also matched every
imported object and available source hash against the author record.
The pinned standard library was reused, not rebuilt in full from source.
The distribution lacks source files for 1,272 runtime modules; their compiled
objects are all hashed, and the missing source entries are explicitly null.

## Review and evidence

- [Final independent AI review of the frozen author/report package](verification/INDEPENDENT-FINAL-AUTHOR-REPORT-REVIEW.txt).
- [Independent engineering review and reproducible tests](verification/engineering/README.md).
- [Independent full-report and all-page PDF review](verification/INDEPENDENT-REPORT-PDF-REVIEW.txt).
- [Root exact-package replay checks](verification/ROOT-REPLAY-REVIEW.json).
- [Author verification and semantic self-review](VERIFICATION-RESULTS.md).
- [Input independence and library provenance](PROVENANCE.md).

The author manifest preserves the original 65-file author delivery. The
engineering manifest separately binds that review's source snapshots and
evidence. `FINAL-SHA256SUMS.json` binds the assembled submission except itself.
Large audit records are deterministic gzip archives with their uncompressed
content hashes recorded alongside them. Historical failed experiments are
explicitly archival; they are neither proof imports nor successful final tests.

Review stages retain their original scope and timestamps. The final combined
checks are recorded in `verification/FINAL-ROOT-GATE.json`; the bounded
prepublication repository check is recorded in `verification/ELIGIBILITY.json`.
These are local verification and independent AI review records. Maintainer
acceptance is a separate decision.
