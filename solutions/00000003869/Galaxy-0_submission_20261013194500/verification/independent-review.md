# Independent internal review: TLMC 00000003869

Reviewed 2026-10-13 UTC by a separate coordinating AI reviewer, not an official competition reviewer.

## Result
PASS for the stated finite-order combinatorial claim, subject to final frozen-package equality and prepublication eligibility refresh.

## Semantic review
The live bilingual statement concerns matching-indexed terms, crossing signs and polynomial computation of crossings in the beta=1 skew-kernel Fredholm-Pfaffian expansion. The source models canonical lists of oriented pairs with strictly increasing smaller endpoints. The actual endpoint list is required to be a permutation of the entire range of 2n labels. This is the usual complete perfect-matching encoding, rather than a hard-coded predicate selected to force the conclusion. Its bijection to unordered two-element partitions is explained correctly in the report.

The sign is independently defined from the inversion number of the flattened endpoint permutation. Pair analysis proves inversions = crossings + twice nestings, and a separate lemma connects the parity sign to the integer power of -1. The matching enumerator has both an if-and-only-if membership theorem and an independent no-duplicates theorem. The formal expansion equality is before evaluation; arbitrary evaluation allows real or complex kernel entries, not just integers. The instrumented crossing counter is proved correct and its exact pair-test count is quadratic.

The conventional canonical-matching definition of the Pfaffian is explicitly sourced to Jimmy He's Appendix A; this is not a definition by crossing sign followed by a tautological proof. I verified the cited primary sources and bibliographic details. The report correctly applies the finite identity at every order of the Fredholm expansion, separately discloses the J-K factor (-1)^n, and distinguishes combinatorial coefficient sign from numerical sign of a product. It neither needs nor claims universal analytic convergence. The bit-complexity argument accounts for logarithmic-size endpoint labels and counts; the exponential whole-matching enumeration is not called polynomial-time.

## Independent checks actually run
- Read the full Lean source and mathematical LaTeX report.
- Copied source into an isolated review directory and re-elaborated with Lean4.31.0 and warningAsError=true: exit0.
- Separate leanchecker kernel replay: exit0.
- Printed transitive axioms for all27 authored theorems: only propext, Classical.choice, Quot.sound.
- Source-only separate Lake directory build: exit0, 3jobs.
- Independent Python algorithm generated every matching for n=0..6, 11465 total, and checked endpoint coverage, uniqueness, inversion/crossing/nesting identity and parity.
- Independently compared matching sums to recursive Pfaffians on60 integer skew matrices at orders0..5; all passed.
- Rendered and visually read all four pages of the compiled PDF. No clipping, overlapping formulas or missing glyphs. Source/report correspondence passed.

These finite Python checks supplement, never replace, the unbounded Lean proof. The paper explicitly states the classical status of the mathematical identity. Internal AI validation does not establish organizer acceptance.

## Reviewed core hashes
Main.lean SHA256 c8e9c39acda19b8c7280a778b4dc6976e3ea4252810d5f6a00ba777b315aa8b7
main.tex SHA256 8b116de97f5e19929b05d90fcafd3fb7f5e9c46d636e1fa5f9615719097dff42
main.pdf SHA256 00f5325d26d9bcb3051d9695fb8efa0e034e2bc9a44fca5aa448f9be6bd1e242
