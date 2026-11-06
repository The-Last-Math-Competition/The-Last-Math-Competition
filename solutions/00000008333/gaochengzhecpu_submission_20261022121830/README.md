# 00000008333 — Disproof

Under the standard cumulative counting interpretation, let M(X) count distinct positive integers m≤X for which positive integers a,b satisfy a²+b²+m²=3abm. The source asserts M(X)~c√X with c>0. We prove

M(64^n) ≤ 2 + 3(6n+1)²·2^(2n+1),

and hence M(64^n)/8^n→0. This contradicts the asserted positive-constant limit. It does not assume Frobenius uniqueness, count repeated numbers, or claim to settle the source's prime-number or random-walk clauses.

The entire mathematical bridge is formalized: sorted positive Markov triples descend to (1,1,1)/(1,1,2) or the actual tree rooted at (1,2,5); every coordinate is 1,2, or the largest coordinate of an ancestor; growth bounds control the finite word collection; its image bounds the actual finite set of Markov numbers; and the real limit refutes every positive c.

Main Lean theorem: `Markov8333.conjecture_8333_false : ¬Markov8333.SquareRootGrowth`.
`SquareRootGrowth` is exactly existence of c:ℝ with 0<c and the actual count divided by Real.sqrt X tending to c over integer cutoffs X→∞. `arbitrarily_small_ratio` also quantifies every c>0 and every starting index N. An asymptotic at real cutoffs would imply its integer restriction.

Files: `lean/Main.lean`, full proof `main.tex`, exact bilingual `SOURCE.md`, and `verification/` author audit and provenance. Lean 4.19.0, pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Reproduce from `lean/` with `lake env lean -DwarningAsError=true Main.lean`.

Author strict compilation passed. The five printed theorem axiom reports contain only propext, Classical.choice, Quot.sound. No unproved placeholders, custom axioms, or native decision procedure are used. Native fresh build, paper compilation, page inspection and publication are performed separately by the coordinator.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. Review mode: agent development with parent adversarial review; no external independent review. Snapshot source record has no prior PR or upstream solution; coordinator repeats publication checks.
