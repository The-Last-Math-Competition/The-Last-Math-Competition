# Reproduction and scope

The complete2-uniform hypergraph on v vertices has precisely one unordered decomposition into single-edge blocks, for every v and thus arbitrarily large prime v. This admissible block class is not excluded by the bilingual statement, and its constant count disproves double-exponential growth.

Main.lean represents actual two-element subsets of Fin(v), finite edge-set blocks, and unordered finite decomposition families with coverage and disjointness. It proves the unique decomposition, cardinality1, and arbitrarily large prime counterexamples. The PDF describes the block isomorphism class and usual convention.

From lean/, run `lake update` if dependencies are absent, then `lake build`. Public pins: Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints standard-axiom audits. Generated .lake artifacts/local dependency junctions are ignored. Compile proof.tex with Tectonic or another LaTeX engine. No auxiliary computation is used.
