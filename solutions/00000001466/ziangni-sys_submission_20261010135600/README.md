# Gaussian zero-correction counterexample

Conjecture 00000001466 is false under its ordinary additive triangle-correction reading. The actual normalized unit-variance Gaussian exponential family has log-partition A(theta)=theta²/2. Its Bregman divergence violates the triangle inequality at0,1,2 and requires correction at least1.

Files: proof.tex, proof.pdf, and lean/Main.lean. The report states the reading and distinguishes weighted triangle inequalities. Lean proves normalization, the exponential factorization, genuine log partition, derivative, Bregman formula, and the final contradiction. The report additionally derives the familiar KL equality; that identification is not needed as a formal premise.

Reproduce with Lean4.19.0: cd lean; lake update; lake build. The public Git requirement and manifest pin Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b and its dependencies. Local ignored package junctions are build conveniences only. No sorry/admit/native_decide/custom axioms/unsafe. Axiom audits are printed by the build.
