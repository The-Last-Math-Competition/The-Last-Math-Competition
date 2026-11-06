# Conjecture 00000005268 — Disproof

Three vortices of nonzero mixed-sign circulation undergo an explicit finite-time total collision. The initial positions are 0, 1, and 3/8 + (7/8)i. All three remain distinct for 0 ≤ t < 1/2 and converge to c = 3/8 − (15/56)i as t approaches 1/2 from the left.

The complete trajectory and actual conventional point-vortex ODE (including 1/(2π)) are formally verified. The proof does not substitute a numeric identity, an assumed ODE solution, or an arbitrary collision endpoint for the dynamics.

- `lean/Main.lean`: vector fields, rational circulations, physical circulation rescaling, exact initial data, differentiable solution, noncollision before T, all three collision limits, and negation of the universal exclusion.
- `main.tex`: complete direct mathematical argument and formalization boundary.
- `SOURCE.md`: frozen bilingual statement.
- `verification/lean-strict.log`: actual warnings-as-errors compiler output and axiom audit.
- `verification/SELF_REVIEW.md`: adversarial self-review.
- `verification/SOURCE_PROVENANCE.md`: exact source commit and SHA-256.

Reproduce from `lean/` with Lean 4.19.0 and the pinned Mathlib dependency:

`lake env lean -DwarningAsError=true Main.lean`

The paper does not claim a classification of collapsing triples or formalize the Hamiltonian reformulation. The explicit ODE and limits suffice to disprove the source's universal collision exclusion. Same-sign collision exclusion is not refuted.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed. No earlier submission on this ID was identified in the coordinator's complete preselection exclusion check.
