# Disproof of conjecture 00000003849

Submitted by GitHub user **@lizaixi01**, with OpenAI Codex assistance for
reasoning, formalization, reports, independent semantic review and packaging.
The independent reviewer is a separate AI agent. Organizer acceptance is pending.

## Mathematical result and source conventions

The nine-vertex finite A2 crystal B=S disjoint-union S disjoint-union S-dual has centrally symmetric weight support but unequal multiplicities of opposite weights, preventing every weight-preserving isomorphism to its actual dual. All crystal axioms, normal strings, dual operators and the standard GL3-to-A2 weight correspondence are proved. The source says weight set and imposes no connectedness or irreducibility restriction. This refutes the sufficient direction and hence the asserted iff; no polynomial-time theorem is claimed.

Final target: `CrystalCounterexample.original_iff_false`.
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
3-page PDF is the unchanged compiled original, and every
page was visually checked again for this submission. A cold dependency download
on a separate machine was not tested during this final publication audit.

## Frozen materials and evidence

All 12 frozen package files, including the original problem,
Lean sources/configuration, LaTeX, PDF, correspondence and historical README or
report, are copied byte-for-byte. Added publication files are this note, LICENSE,
the copied evidence and SHA256.json. SHA256.json lists every other public file.
The copied evidence substitutes machine-specific paths; raw originals remain
locally recorded. Historical worker paths in the frozen documents and receipts
describe the local audit. This note supplies the public reproduction command;
external worker logs are not required to compile or read the complete disproof.

Raw local verification SHA256: `bf2ba7566d17a296a9328a3824491fa85bfb3c67fddc6e60cd1b6468c76004fb`.
Raw final semantic review SHA256: `fcf4a0cd2a2b217e762194b9e1918dde1b6f36e1f2e9a3afc1cad49be0aa4371`.

## Eligibility snapshot

Official commit: `9b795e7a94a6076e49a65a6489e1caf9153abd23`. Both solved flags are false. The complete
current Git tree contains no solution folder for this ID. All
904 historical PR file sets were checked, including renamed
paths and closed/merged submissions. The large PR #267 was covered by complete
merge-base/head tree comparison beyond the 3,000-file API cap. No matching PR
or solution-folder commit history was found. This checks repository submission
eligibility; it does not establish worldwide mathematical priority.
