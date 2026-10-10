# Reproduction and scope

The actual commutative PI ring Q[X0,X1,...] has a strict infinite chain of prime substitution kernels, all contained in the same prime M. The standard localization order isomorphism transports this chain to actual prime ideals of Localization.AtPrime M with strictness preserved. Identity UV−VU has degree2; conventional PI degree is1. Both are fixed, so a finite polynomial chain bound fails.

Main.lean formalizes the actual polynomial ring, homomorphisms, kernels, prime proofs, variable witnesses, containment in M, and the actual localized prime chain. The PDF explains the source clause and prime localization correspondence. No assumption of the desired certificate is used.

From lean/, run `lake update` if dependencies are absent, then `lake build`. Public pins: Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints standard-axiom audits. Generated .lake artifacts and local dependency junctions are ignored. Compile proof.tex with Tectonic or another LaTeX engine. No auxiliary computation is used.
