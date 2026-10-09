# Disproof of conjecture 00000003825

Submitted by GitHub user **@lizaixi01**, with OpenAI Codex assistance for
reasoning, formalization, reports, independent semantic review and packaging.
The independent reviewer is a separate AI agent. Organizer acceptance is pending.

## Mathematical result and source conventions

The source explicitly defines its monomial crystal as a crystal structure on an alphabet monoid. One fixed two-letter A1 free monoid, with its actual tensor-product word crystal, contains a finite nonempty irreducible subcrystal B(k) for every natural k. The k+1 vertex counts distinguish infinitely many genuine crystal-isomorphism classes. This refutes the necessary fixed-alphabet finiteness conjunct. The proof follows the explicit alphabet-monoid definition in both source languages; no Laurent-monomial model or general dominant-weight classification is assumed.

Final target: `FixedAlphabetA1.fixed_alphabet_finiteness_false`.
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

All 16 frozen package files, including the original problem,
Lean sources/configuration, LaTeX, PDF, correspondence and historical README or
report, are copied byte-for-byte. Added publication files are this note, LICENSE,
the copied evidence and SHA256.json. SHA256.json lists every other public file.
The copied evidence substitutes machine-specific paths; raw originals remain
locally recorded. Historical worker paths in the frozen documents and receipts
describe the local audit. This note supplies the public reproduction command;
external worker logs are not required to compile or read the complete disproof.

Raw local verification SHA256: `b19c4db7fb8c0e79a1ad8ecd3aa40b1620cb6676c2adbdb01dc3e864d8ba7453`.
Raw final semantic review SHA256: `d9d793ffcd7340d67e2a2b1d9bcd55c20fee1b35be153d506196a083329a851d`.

## Eligibility snapshot

Official commit: `9b795e7a94a6076e49a65a6489e1caf9153abd23`. Both solved flags are false. The complete
current Git tree contains no solution folder for this ID. All
904 historical PR file sets were checked, including renamed
paths and closed/merged submissions. The large PR #267 was covered by complete
merge-base/head tree comparison beyond the 3,000-file API cap. No matching PR
or solution-folder commit history was found. This checks repository submission
eligibility; it does not establish worldwide mathematical priority.
