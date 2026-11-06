# Conjecture 00000005512 — Disproof

The standard two-choice supermarket mean-field fixed point at load one half has survival tail q_k=2^{-(2^k-1)}, which decays faster than every inverse polynomial in queue length. The actual d-choice fixed-point family has q_d(2)=2^{-(d+1)}, which also decays faster than every inverse polynomial in selection count.

Lean verifies the actual infinite drift equations, the two-choice fixed point and uniqueness, exact closed form, actual nonnegative probability masses of total one, all survival-tail identities, and the infinite asymptotic negations in both variables. The paper openly distinguishes genuine power tails from the correct d-th-power recursion reading and cites the classical model equations. Finite-server stochastic limit results are not claimed as formalized.

From lean/ run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. The pinned Lean and Mathlib revisions are in the project metadata. Principal axiom reports contain only propext, Classical.choice, Quot.sound.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed. The coordinating agent performs fresh build, PDF checks and publication.
