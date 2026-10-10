# Reproduction

This disproves the vanishing clause under the conjecture's explicit definition of SK_1 as the determinant kernel on GL(R). It does not dispute conventional quotient-based algebraic K-theory SK_1.

The Lean theorem uses Q, actual invertible matrices, and every stabilization diag(U,I_n); Q has zero nilradical. The PDF explains the injective direct-limit passage.

Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned publicly. From lean/, run `lake update` if dependencies are absent, then `lake build`. Main.lean prints standard-axiom audits. Local dependency junctions and generated .lake files are ignored and are not required for reproduction.

Compile proof.tex using Tectonic or another LaTeX engine. No numerical computation or external certificate is used.
