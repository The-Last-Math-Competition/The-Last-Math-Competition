# Counterexample to 00000008488

The compact space of one-sided binary sequences with at most one `1`, under the continuous left shift, has actual Bowen topological entropy zero. At the fixed first-coordinate entourage its genuine minimum spanning number for `n` iterates is `n+1`. The resulting finite-time values are `log(n+1)/n`, so no eventual `C/n` error bound exists for any constant `C`.

The Lean proof constructs the closed compact subshift, its continuous map and actual iterates, finite covers and separated sets, and a cofinal family of metric entourages. It evaluates Mathlib's native `Dynamics.coverMincard` and `Dynamics.coverEntropy`; the numbers and entropy are not assigned as definitions. The final obstruction is quantified over every real `C` and every starting index `N`.

Here `n` means orbit length and finite-scale value means normalized logarithmic spanning number at a fixed entourage. This refutes the conjecture's harmonic-rate clause under that explicit standard interpretation. It does not challenge classical equivalence of entropy definitions on compact systems or settle the unspecified noncompact boundary and periodic optimality clauses.

See `report.tex` and `report.pdf`, the complete original bilingual `SOURCE.md`, the pinned Lean project in `lean/`, and actual verification receipts and file hashes in `VERIFICATION.md` and `evidence/`.
