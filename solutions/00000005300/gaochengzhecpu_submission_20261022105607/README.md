# Proof of conjecture 00000005300

Over Z, compare the zero FI module with the module that is Z at the empty set and zero at every nonempty set. Their complete positive-degree restrictions are naturally isomorphic, while a natural isomorphism of the total modules would give Z ≅ 0 at degree zero. Both modules are finitely generated; the nonzero module has one generator in degree zero. Both stable direct limits vanish.

The unspecified phrase “stable groups” is interpreted as eventual values together with transition maps (and consequently the stable direct limit). No claim is made for a separate, undefined invariant that retains unstable information.

## Verification

`lean/Main.lean` defines the finite-set injection category, a bundled category of Z-modules, actual functors and natural isomorphisms. `Conjecture5300.conjecture5300` is the existential claim over these functors. `tailIso` proves natural isomorphism on the entire positive-size subcategory; `not_iso` excludes every full natural isomorphism. `degreeZeroEquiv` and `generated_in_degree_zero` establish the exceptional rank-one value and finite generation.

The direct-limit argument and extension from the standard skeleton to arbitrary finite sets are proved in the paper, not by a Lean colimit construction.

Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. From `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. All five printed axiom audits return only `propext` and `Quot.sound`. No sorry, admit, native_decide, custom axiom or opaque declaration is used.

The proof was developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. Review mode: agent development with parent adversarial review; no external independent review.

Source: `SOURCE.md`, upstream commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. No previous PR was identified in the coordinator's fresh upstream check. Parent agent handles final fresh build, PDF compilation and page inspection.
