# Independent review of conjecture 00000005613

Date: 20 October 2026 UTC.
Verdict: PASS for the explicit individual coefficient-minor vanishing claim under the standard subresultant construction. The source's unspecified spectral terminology is not treated as a separately formalized theorem.

## Result and interpretation

For f=X^3-4X and g=X^2-1, the actual first Sylvester submatrix has rows f, Xg, g, in descending coefficient order. Its third-order coefficient minor M_{3,1} is zero, while its leading principal minor M_{3,0} is -3. Both inputs are monic and squarefree, their roots strictly interlace, and Xf+(3-X^2)g=-3 proves mathematical coprimality. Thus the proposed equivalence between vanishing of an individual coefficient minor and vanishing of its corresponding principal minor fails in this standard construction.

This does not mean that the whole first subresultant polynomial vanishes. It is -3X and is nonzero, just as its principal coefficient is nonzero. The example does not refute an equivalence formulated instead for vanishing of the whole polynomial. The final report and README explicitly maintain this distinction.

The conjecture does not define its spectrum, conversion, or correspondence. The review approves the stated conventional coefficient/principal interpretation only, not an invented claim that every possible interpretation has been disproved. This limitation is prominently disclosed in the report and reflected in the final Lean proposition.

## Standard construction and mathematical review

Independently inspected Michael Kerber, Geometric Algorithms for Algebraic Curves and Surfaces (2009), Definitions 2.3.10–2.3.12, printed page 30:

https://www.geometrie.tugraz.at/kerber/kerber_papers/kerber_diss.pdf

These define the rectangular Sylvester submatrix, the M_{k,t} column selector, its leading principal case t=0, and the coefficient-minor subresultant formula. The implementation follows this convention. For degrees 3 and 2 and subresultant index 1, it generates a 3-by-4 matrix, rather than assigning an unrelated numerical table.

Read the complete final Lean source, report source, rendered PDF, README, and supplementary arithmetic checker. Verified the row shifts, descending coefficient exponents, matrix dimensions, Laplace determinant signs, selected columns, exact degree and monicity, both determinant values and subresultant coefficient order. The selected matrices are:

M_{3,0}: rows [1,0,-4], [1,0,-1], [0,1,0], determinant -3.
M_{3,1}: rows [1,0,0], [1,0,0], [0,1,-1], determinant 0.

The factorizations (X+2)X(X-2) and (X+1)(X-1) show all roots, not merely selected roots. Their order is -2 < -1 < 0 < 1 < 2. The explicit nonzero constant Bezout identity excludes a shared nonconstant polynomial factor.

## Formal coverage and scalar-domain boundary

The source proves identities both pointwise over Rat and at the finite coefficient-list level. The coefficient-list products are linked to the actual input coefficient functions. HasDegree includes a nonzero leading coefficient and a zero tail; the final claim includes both monicity and the explicit splitting-based strict-interlacing condition. The final theorem negates the concrete vanishing equivalence for this restricted input class.

Lean's scalar domain is Rat. The formal exact-root theorems and no_common_root quantify over rational inputs, not over a formal Real or Complex type. The coefficient identities transfer mathematically through the usual embeddings of Q into R and C. Together with the elementary displayed factorizations and constant Bezout identity, this yields the written real-root and polynomial-coprimality conclusions. That transfer is not claimed as separately formalized, and the rational no_common_root theorem is not claimed to be a general formal gcd theorem. The final PDF and README explain this boundary accurately.

The determinant and Sylvester constructions are given directly by their conventional explicit definitions. The review does not claim that an external abstract matrix, polynomial or algebraic-closure library was imported or proved equivalent to these definitions.

## Independently executed verification

Used Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, with bundled Std and no third-party Lean dependencies. Began from copied source files without author-supplied olean files or build caches.

All of the following were actually executed and passed:

- Source-only compilation with lean -j1 -DwarningAsError=true -o Subresultant.olean Subresultant.lean: 1.505 seconds, exit 0.
- Independently generated axiom audit of all 22 named theorems: every closure is contained in {propext, Classical.choice, Quot.sound}.
- leanchecker Subresultant on the newly generated object: 0.531 seconds, exit 0. This is Lean's kernel replay, not a separate implementation of the kernel.
- Fresh package-level lake build with the project's warning-as-error configuration: 3 jobs, success.
- Author's exact Python arithmetic checker: success.
- Independently written Python checker, importing no author code: regenerated the generic Sylvester submatrix from the coefficient inputs, recomputed determinants by permutation expansion, checked coefficient products, strict root order, the first subresultant formula and the constant Bezout identity. All checks passed.

There are no admitted proofs, custom axioms, native decision procedures, unsafe declarations or kernel bypasses in the mathematical source. ReviewAudit.lean contains the independent all-theorem audit, and review-verification.log records the successful commands and outputs. The independent Python source and exact result accompany this review.

## Report and PDF quality

Independently rendered the final three-page PDF with Poppler at 140 dpi and visually inspected every page:

1. Standard convention, interpretation limitation and individual-minor distinction.
2. Exact inputs, interlacing, Bezout identity, generated matrix, both determinants and scoped counterexample theorem.
3. Formal theorem coverage, explicit Rat-to-real/complex interpretation boundary and primary reference.

Every page is legible, with no clipped equations, missing glyphs, overlapping text or broken references. The report is semantically consistent with the actual Lean development and does not overstate its scalar-domain coverage.

## Source and eligibility snapshot

Independently fetched the complete bilingual source at:

https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000005613.md

Source Git blob SHA: b659307baec1b29f28ba161e5afb27c468bd7301.

The live metadata row in blob 4796f375e31ccfbbea637a19cbab7cd8bee7f4bc marked both proven and disproven false. Live all-state PR searches for 5613, 00000005613 and subresultant returned no results; the solution-directory contents query returned 404. A separate exact-ID scan of a 1060-entry all-state PR snapshot also found no title/body match. These were actual saved checks on 20 October 2026, not inferred eligibility. They must be refreshed before publication because repository state may change. Raw connector responses and the primary-source PDF are not included in this compact public review bundle.

Exact reviewed-file hashes and the compact review-file hashes are recorded in review-provenance.json. No author artifacts were modified during independent review.
