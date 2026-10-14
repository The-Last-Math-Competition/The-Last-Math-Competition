# Verification record

Date: 14 October 2026 UTC. This records submission preparation, not competition acceptance.

## Final source-only replay

The original proof file was preserved without changes. Its SHA-256 is:

`2bc23b09ecd7dc366ca52a703be8fc637cc4aab6ce28ecb1b8d78cea9d5ce2e7`

A fresh directory received only the packaged `lean/` source tree. The supplied `verify.sh` was then executed using the existing official Lean 4.31.0 toolchain on PATH. No prior `.olean` files or `.lake` artifacts were copied into that directory.

Results:

1. `lake build`: PASS, exit 0.
2. `lake env lean -DwarningAsError=true Conjecture4091/Basic.lean`: PASS, exit 0.
3. Strict compilation of independent `Audit.lean`: PASS, exit 0.
4. Independent kernel replay with `leanchecker` of `Conjecture4091.Basic`, `Conjecture4091`, and `Audit`: PASS, exit 0 for each. Successful checker output is otherwise silent; the wrapper records each result.
5. Axiom audit of the eight public authored library theorems and the additional audit theorem: standard `propext`, `Classical.choice`, and `Quot.sound` only, as applicable. No custom axioms or `sorryAx`.
6. Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` tokens in authored Lean sources.
7. `empirical.py`: PASS. Exact Fraction elimination gives K2 incidence rank 1 and kernel dimension 0; C4 rank 3 and dimension 1. Exhaustive color search finds chromatic minimum 2 for each. All 1,099 labeled simple graphs of orders 1 through 5 are enumerated; connected graphs of chromatic number 2 exhibit first Betti numbers 0, 1, and 2.
8. Independently authored `review/independent.py`: PASS. It separately checks simple connected witness graphs, actual coloring minima, exact rational incidence ranks, and cycle dimensions.
9. Python syntax parsing and all explicit expected-result assertions: PASS.

See the corresponding files in `evidence/`. The finished package contains no build cache, compiled Lean objects, test scratch file, old failed LaTeX log, or superseded eligibility snapshot.

## Independent source and semantic checks

`lean/Audit.lean` additionally proves the square does not admit a zero-dimensional basis certificate and checks its endpoints and graph sizes. Its axiom audit covers every public library theorem. The independently implemented Python checker is evidence only and is not an input to Lean proof checking.

The complete Lean definitions, mathematical report, source conjecture, and PR 292 review were read in full. The report's proof is valid under the usual topological interpretation, and it credits the prior path/even-cycle observation. `review/INDEPENDENT_REVIEW.md` records the correspondence and formalization boundary. No claim is made that Lean constructs general topological configuration spaces or proves cellular/singular comparison.

## PDF checks

`build_pdf.sh` compiled the final source twice using pdfLaTeX and the existing compatible format on this minimal image. Final PDF: five A4 pages, 11-point main text. Final-pass log contains no overfull-box warnings, undefined citations, or unresolved references. All five final pages were rendered with Poppler and visually inspected for complete text, equations, margins, fonts, and pagination. The reference list begins on its own page. The PDF has no clipped text, overlapping elements, missing math glyphs, or broken tables.

The minimal installation has no default `pdftex.map`; the source explicitly loads the available Latin Modern and AMS symbol maps, and every used font is embedded. The incidental missing-default-map warning does not affect the rendered output. A regular TeX installation can use the same source.

## Eligibility and prior submission

The live 19:46 UTC check finds no solved metadata or current solution directory, but does find closed/unmerged PR 292. That earlier submission was rejected for an arithmetic-only Lean formalization. Its mathematical contribution is credited, its formal gap is explained, and the present graph/color/kernel repair is described in the report and `PRIOR_SUBMISSION.md`. No earlier submission is concealed. Search results are a snapshot and do not establish priority or cover unpublished work. Eligibility must be rechecked immediately before any future publication.

## Package integrity

`SHA256SUMS` lists every packaged file except itself, using relative paths. Validate with `sha256sum -c SHA256SUMS` from this directory. The manifest certifies the frozen bytes, not competition acceptance.
