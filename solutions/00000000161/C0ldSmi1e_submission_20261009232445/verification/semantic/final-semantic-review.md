# Final semantic and report review: conjecture 00000000161

## Decision

**PASS for mathematical semantics, original-statement correspondence, complete report correspondence, and PDF legibility. No corrective finding.**

The frozen Lean proof disproves the source claim under the conventional positive, dimension-only interpretation of `poly(n)`. At the allowed fixed dimension four, for every positive real constant `C`, the claimed event is empty for every prime `p >= 3C`. Its uniform probability is therefore eventually exactly zero. This stronger statement removes any dependence on selecting a particular positive polynomial.

The independent engineering review is separate. I have not received its fresh compiler/axiom results and do not certify them here. The author log was previously read and remains identified as author-generated evidence. Root's reported native LaTeX compilation and PDF-export results are likewise not represented as compilation I personally performed. My report/PDF correspondence review and independent PDF rasterization are complete.

## Materials and integrity

This review supplements, without altering, `source-scope.md` and `proof-semantic-review.md` in this review directory. The complete source/proof assessment and stock-reference analysis remain in the latter.

I independently recomputed the hashes of the original bilingual statement, both rules, the original-input manifest, the proof freeze manifest and all ten frozen deliverables, the frozen archive, the final LaTeX source, the final PDF, and both final page images. Their designated hashes match. All bindings, file sizes, prior review hashes, and review-status limits are recorded in `final-review-bindings.json`.

Key bindings:

- Original bilingual statement: `1c971b03093fe80cb0bcaadeb5eeaf3139f34b846d65e1eae3d4f103c256ec76`.
- Original-input manifest: `3f56a82d2facffacad8e92c98fcaa9576bd1f408246b6386cda52c81c6c48fb8`.
- Frozen proof manifest: `d206561c63c216e68fd9a99847d2ecfb088bbc269d2052f47c79e2c7efd493fe`.
- Final `proof.tex`: `8b2439313ca95dbbb398e60a97b4c3bb0dfa3cfe16482ae84bc051dd4aec7093`.
- Final `proof.pdf`: `f7767186f5d7d966b97a60cc2daa85f5d2dfba0f889c5f22f4810a3f1f562cf7` (43,538 bytes, exactly two US-letter pages).

The separate root PDF-review record was used only to compare its hash bindings. Its claimed visual pass was not substituted for my own reading or page inspection.

## Complete LaTeX and PDF content review

I read the entire final LaTeX source and all content on both PDF pages, including the title, author/disclosure line, date, theorem and proof, scope explanation, formal-definition list, named theorem correspondence, reproduction instructions, verification claims, and provenance/review-status paragraph. I additionally extracted the full text from both PDF pages as a completeness check.

Page 1 accurately states the original claim's fixed-dimension and prime-limit setting, explicitly identifies the positive denominator independent of `p`, and acknowledges that the original does not specify a particular polynomial. Its theorem asserts the exact dimension-four bound proved in Lean. The group-cardinality factorization, all four individual factorizations, Lagrange/Euclid step, and inequality chain are correct. The strict inequality in the original event is preserved, so the non-strict upper bound suffices to make the event empty. The explanation of eventual zero along unbounded primes and exclusion of a simultaneous limit one matches the formal argument. Setting `C = P(4)` is valid and uses an allowed fixed dimension.

Page 2 accurately describes the actual prime subtype and filter, actual matrix unit group over `ZMod p`, actual element order, prime-divisor event, normalized finite counting probability, and declared existential-polynomial reading. It does not replace the formal objects with an unrelated surrogate. The named arithmetic-to-group bridge and final/stronger theorems agree with the previously reviewed source. The report correctly separates the statement's unspecified polynomial wording from the explicit formal definition.

The Lean/Mathlib versions, pinned Mathlib commit, eight additional dependency revisions, fourteen-theorem audit coverage, and claimed standard axiom set match the frozen project and recorded author log. The report explicitly calls the passed verification an author run. Its distinction between internal review, repository eligibility, and maintainer acceptance is appropriate. No numerical experiment is needed or claimed as proof.

The report's references to `conjecture.md`, `AUTHOR_NOTES.txt`, and running the verifier inside `lean/` describe the intended assembled submission layout. Root must ensure those paths exist when packaging; final package assembly was not supplied for this review. This is a packaging check, not a defect in the mathematical report.

## Visual review and independent rendering

I visually inspected every part of the supplied `final-page-1.png` and `final-page-2.png`. All text, theorem notation, fractions, exponents, product limits, factorization equations, inequality signs, bullets, underscores, theorem names, and page numbers are visible. There are no clipped blocks, overlaps, broken glyphs, missing equations, illegible symbols, or empty/unreviewed pages. The long identifiers on page 2 wrap at readable boundaries; the final paragraph and footer remain separated. Page 2 is denser than page 1 but remains legible.

I independently rendered the handed-over PDF with the bundled `pdftoppm -r 120 -png` into this review directory. The resulting page files are byte-for-byte identical by SHA-256 to the two supplied final page images:

- Page 1: `41ef30d085a4d98726496e903076e6b5f063f581e74e788266f1799b6a0e64d9`.
- Page 2: `8695db9c005a6602c8d6c9c4829d7dbcdb5d9949698c041fb338f5ef58c7159b`.

Thus the visually inspected pages are independently tied to the handed-over final PDF, rather than merely assumed to be current screenshots.

## Final scope limits

No proof, report, or layout edits are requested. This semantic review, together with the earlier immutable proof review, covers the entire submitted argument and both complete report pages. No frozen author or report file was modified. I consulted no other solutions, conjectures, selector records, external mathematical material, or thread history/rosters.

Independent fresh Lean compilation/axiom verification, final assembled-directory consistency, repository eligibility, and any publication decision remain with root and the separately assigned engineering review. This pass is an internal review and is not maintainer acceptance.
