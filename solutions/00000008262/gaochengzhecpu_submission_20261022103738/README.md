# Conjecture 00000008262 — Disproof

For A=diag(3/4,-3/4), H=I and equal unit isotropic noises, the stabilizing
covariance P=diag(2,1/2) has condition number four, contradicting the
claimed bound one.

Lean formalizes actual matrices, positive definiteness, the complete
algebraic Riccati equation, complex-spectrum stability and the true
real-spectrum extremal eigenvalue ratio. The final theorem negates the
universal claimed bound. The paper gives the model interpretation and
an explicit covariance trajectory converging from zero to P.

The Brownian filtering interpretation and time-dependent trajectory are
paper-only. They are not represented as having been formalized.
Run `lake env lean -DwarningAsError=true Main.lean` in `lean/`.
The direct check passed; parent fresh build and PDF review are separate.

Developed by a delegated AI agent with a self-review; the coordinating
agent reviews it separately. No external independent review is claimed.
The parent found no prior submission in its frozen full PR history.
