# Reproduction and scope

The binary coordinate shift is a continuous, surjective, shift-commuting cellular automaton with a permutative identity local rule. Its single-site damage travels exactly n lattice sites left after n iterations, so one directional propagation/Lyapunov speed is1. This disproves the zero-speed equivalence. The spatial motion is distinct from Hamming damage count.

Main.lean proves actual product-topology CA properties, exact iteration/damage sites for every configuration, and a sharp half-line front bound. These configuration-independent identities apply under any Bernoulli measure without additional probabilistic assumptions.

From lean/, run `lake update` if dependencies are absent, then `lake build`. Lean4.19.0 and public Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. Build output prints four standard-axiom audits. Local .lake junctions/build files are ignored. Compile proof.tex with Tectonic or LaTeX. No auxiliary numerical computation is needed.
