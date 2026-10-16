# Independent final audit — TLMC 00000003169

Date: 2026-10-16, 19:11 UTC
Verdict: PASS. The audited mathematical proof, Lean certificate and PDF are consistent and suitable for submission, subject to separate eligibility and duplicate-submission checks.

## Source fidelity

Read the current English and Chinese conjecture directly through the GitHub connector. The supplied source.md matches its Git blob hash exactly:

9f5ee54be15ed7207b6565546db1d170cb124678

The report correctly refutes the source's unconditional equality, including its possible complete-intersection qualification. It explicitly distinguishes the false unconditional claim from the valid generic/nondegenerate BKK theorem.

## Mathematical review

Verified the actual cubic witness f=x+y+1 and g=(x+y)^3+x+2y+4, all four ideal-generator identities, the unique complex root (1,-2), nonzero torus coordinates, determinant-one Jacobian, and the regular-sequence/length-one argument. The example is a reduced nonempty complete intersection, so neither multiplicities nor the complete-intersection qualifier removes the counterexample.

Verified the nonzero supports, convex hulls Delta and 3Delta, Minkowski sum 4Delta, Euclidean areas 1/2, 9/2 and 8, and resulting BKK mixed volume 3 and classical mixed area 3/2. Both differ from the root count one. The face degeneracy explanation is correct.

## Formal-code review and reproduction

Independently read Algebra.lean, Geometry.lean, Main.lean and Audit.lean. The generic support-weight convex-hull definition is formally linked to the actual support lists. Root completeness and absence of duplicates are proved over arbitrary commutative rings; the final count has an independent root-carrier parameter, rather than a rational-only root restriction.

Independently ran on the final files:

- Lean 4.31.0 / Std `lake build`: PASS.
- `lake env lean Audit.lean`: PASS; only propext, Classical.choice and Quot.sound reported.
- `lake env leanchecker Algebra`: PASS.
- `lake env leanchecker Geometry`: PASS.
- `lake env leanchecker Main`: PASS.
- Python standard-library `verify.py`: PASS for exact polynomial identities, derivative determinant, actual support convex hulls, Minkowski hull and rational area polarization.

The reproducibility log is 3169-final-verification.log. The code establishes an explicit algebra/convex-hull/determinant-area certificate, not a general algebraic-geometry or measure-theory library theorem. The PDF accurately discloses that complex-number interpretation, ideal/quotient and multiplicity language, and identification of determinant area with Euclidean area use the conventional mathematical arguments supplied in the text. No conclusion-specific axiom hides those boundaries.

## PDF and packaging review

Read all of paper.tex and README.md, independently rendered the final paper.pdf, and visually inspected all three pages:

1. Title, abstract, source scope and ideal identities: legible and correct.
2. Jacobian, complete-intersection proof, Newton polygons, area calculation and conclusion: legible and correct.
3. Formal boundary, verification statements and references: legible and accurate.

No clipped equations, missing glyphs, overflowing text or unreadable references were found. Page numbers and section transitions are consistent. The README's intended submission list contains the proof, reproducibility, PDF/source and relevant log files, and properly excludes scratch probes, candidate-search notes and build caches. No source modification was required during this audit.

## Frozen SHA-256 hashes

- Algebra.lean: a89c968e5d7a9c3de536ffb63f98290299b8f18e98030fc3dabc81117a6193c9
- Geometry.lean: c290c3eb40a091dbe12861a1dfede86d7de8d4a86086190687b7a84ff19ad88d
- Main.lean: 9e17acb287e43ffebf29e8076bfea0ed07a9ef9e7a01a5513d41bea628735f30
- Audit.lean: 7ba9cd0d0fac63a63e525558a2548f4397369d8a3af586d3a8efc1d01ee91b9f
- paper.tex: d2b28757377bd2a78687c43a7abd53af0baba75f1f7e873d609c77236aa5f3af
- paper.pdf: 2605bd787058bdbfd355c30230870bb85dda1dd451f76018960b040f120b0c53
- source.md: ade937d5211e63fb87ec4f242a84a5ff4ae3aefef7b940c17a0becfd419c355f
- README.md: 9e2e0539b08e00c0eaa0b9340b9ec7736928431d1e2edadddfa34360d96d1389
