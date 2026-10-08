# Verification

Run `lake build` in `lean/` with Lean4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; the manifest pins public transitive dependencies. Local cache junctions are ignored.

The formalization uses genuine real symmetric matrices and Mathlib's algebraic spectrum. It proves the exact spectrum from the determinant, computes its attained maximum and absolute-value supremum, and proves unboundedness and absence of a maximizer across the entire feasible matrix class. The separate majorization theorem covers every descending real pair of sum1 and produces a feasible matrix with its actual strictly dominating spectrum.

Printed theorem audits use only propext, Classical.choice and Quot.sound. No proof placeholders, custom axioms, native-decision shortcuts or unsafe code occur.

The report was compiled with existing Tectonic after the built-in compiler's known platform-directory failure. Every PDF page was rendered and visually inspected. The report explicitly distinguishes unrestricted fixed trace from the positive-semidefinite restriction and identifies the precise standard meanings of spectral maximality being refuted.
