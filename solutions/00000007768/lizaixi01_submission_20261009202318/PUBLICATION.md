# Disproof of conjecture 00000007768

Submitted by GitHub user **@lizaixi01**, with OpenAI Codex assistance for
reasoning, formalization, reports, independent semantic review and packaging.
The independent reviewer is a separate AI agent. Organizer acceptance is pending.

## Mathematical result and source conventions

The genuine polynomial f(z)=z^2-6 has algebraic coefficients and degree two. Its actual all-iterate bounded-orbit filled Julia set is closed, and its nonempty Julia boundary is contained in the real axis, giving actual Hausdorff dimension at most one. Polynomial degrees and coefficient identities exclude invertible affine conjugacy to z^d or either sign of the genuine Chebyshev T_d for every natural d. This refutes the necessary nonexceptional dimension>1 conjunct under the explicitly disclosed standard Hausdorff-dimension and affine-conjugacy conventions. No exact dimension, algebraic-arc, transcendence or cusp classification is claimed.

Final target: `TLMC7768.disproves_dimension_clause`.
Read `proof.pdf`, `proof.tex` and `SourceCorrespondence.md` for the complete
argument and correspondence to both languages of the official original.
Known structures and mathematical references are credited in those files and
the copied semantic analysis. No new mathematical discovery is asserted.

## Reproduction

Install the Lean toolchain named in `lean/lean-toolchain` (Lean 4.33.0), enter
`lean/`, and run `lake build +Main`. All local imported modules are included.
The Git-based locks pin Mathlib and its dependencies; do not update the pins.
The publication excludes `.lake` caches and author-produced `.olean` files.
For a fresh official kernel replay, after building run
`lake env leanchecker --fresh --verbose Main` with the pinned toolchain.
The original frozen package passed a clean build, exact theorem-type contracts,
transitive axiom audit and official fresh kernel replay. Only standard Lean
axioms are used; there is no sorry, native_decide or extra axiom.

Compile `proof.tex` with a compatible LaTeX installation. The supplied
2-page PDF is the unchanged compiled original, and every
page was visually checked again for this submission. A cold dependency download
on a separate machine was not tested during this final publication audit.

## Frozen materials and evidence

All 15 frozen package files, including the original problem,
Lean sources/configuration, LaTeX, PDF, correspondence and historical README or
report, are copied byte-for-byte. Added publication files are this note, LICENSE,
the copied evidence and SHA256.json. SHA256.json lists every other public file.
The copied evidence substitutes machine-specific paths; raw originals remain
locally recorded. Historical worker paths in the frozen documents and receipts
describe the local audit. This note supplies the public reproduction command;
external worker logs are not required to compile or read the complete disproof.

Raw local verification SHA256: `ee5ff7140f8552aacec2d09ed04d92d32d5011e173e7c0644ba5ae1c40792b6d`.
Raw final semantic review SHA256: `cd5042c4530d7c732411469f63f4fedbc53cf2c4745c4423bb6d8caa43eefaef`.
The inherited complete mathematical review and packaging addendum are also
included for 7768, whose final review rebinding changed only dependency locators.

## Eligibility snapshot

Official commit: `9b795e7a94a6076e49a65a6489e1caf9153abd23`. Both solved flags are false. The complete
current Git tree contains no solution folder for this ID. All
904 historical PR file sets were checked, including renamed
paths and closed/merged submissions. The large PR #267 was covered by complete
merge-base/head tree comparison beyond the 3,000-file API cap. No matching PR
or solution-folder commit history was found. This checks repository submission
eligibility; it does not establish worldwide mathematical priority.
