# Verification record

The frozen source passed author and independent clean builds under Lean 4.31.0. All 5 imported proof modules independently passed leanchecker. The strict warning-as-error audit and theorem axiom inventory passed, using only standard Lean axioms. Exact rational geometry passed an independent Python audit. The final four-page PDF was visually inspected.

Run `./verify.sh /path/to/lean/bin` to reproduce Lean build, kernel replay, axiom inventory and exact geometry. Run `./build_pdf.sh` on an ordinary TeX installation.

Read `review/review.md` for the semantic review. Real-facet convexity and the standard topological planar-embedding/Euler bridge are supplied in the paper; this package does not claim a kernel-formalized theory of real topology. The actual finite geometry, field-general no-sphere obstruction, local rotations, and facial-decomposition bound are proved in Lean.

`verification/` records the author checks; `review/logs/` records the independent checks. `eligibility/` is a snapshot, not future publication clearance. No submission was made.
