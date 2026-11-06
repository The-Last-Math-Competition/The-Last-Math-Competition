# Source and validation review: problem 1104

The actual original statement quantifies over every Coxeter system and every parabolic subset. Taking the empty subset is permitted. The ordinary S5 example at x=12345, w=34512 has polynomial 1+2q and lies outside the claimed affine exception. This is the published example in Woo (2009), Example 1.3, not a claim of a new mathematical discovery.

A source review checked all definitions and proof steps in the final Main.lean (SHA-256 a6ccc38d69d7974ecfd3ec7ba7926cf199b03e3cfbc102d86dfbbfdcff4c715c). The 120 table rows are verified as distinct permutations, swaps are checked, and descents decrease inversion length. Together with the elementary count 5!=120 this gives exhaustive summation. The right-descent recurrence uses the correct c, mu coefficient index and correction exponent.

The finite evaluation is not accepted merely because of an empirical fuel choice. step_congr restricts dependencies to shorter second indices; fuel_next and fuel_above prove stability at the actual length; kl_recurrence proves the complete recurrence; recurrence_unique establishes uniqueness by strong induction; recurrence_counterexample applies the failure to every family satisfying the recurrence. The computed polynomial and nonmonicity proofs have no assumed polynomial values.

A separate fresh copy of the final source was strictly compiled with warningAsError=true and replayed with leanchecker. All 19 named theorems were axiom-audited. Only propext and Quot.sound occur, and no sorryAx, custom axioms or compiler-trust/native-decide dependencies occur. A supplementary independently implemented R-polynomial/bar-inversion calculation also gives 1+2q, with identity, simple reflection, 3412 and longest-element sanity checks. Python is not substituted for the kernel proof.

A further source review checked the standard right-descent formula against Bjorner–Brenti Theorem 5.1.7 and the published Woo example. The final two-page PDF was independently rendered and both page images were actually inspected, with no clipping or unreadable formulas. Identification of the abstract Hecke definition with this finite recurrence, and the empty-parabolic reduction, are explicit standard mathematical theorems rather than hidden Lean axioms. No claim is made to rebuild all abstract Coxeter or Hecke theory in Lean.

These are AI-assisted mathematical and source reviews, not organizer acceptance or human certification.
