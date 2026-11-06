# Conjecture 00000008263 — Disproof

Four positive weights (1/8,3/8,1/8,3/8), observable (1,0,1,0), and the
standard systematic ordering yield variance 1/16 versus multinomial
variance 3/64. Both expectations are 1/4, so systematic resampling is
strictly worse. This refutes both exact and at-most variance halving.

Lean uses the actual inverse-CDF algorithm, all real phase outputs via a
generic ordered-field proof, finite probability laws with normalization,
and the product categorical multinomial law on all 256 outcomes. It
computes the actual centered variances and negates the necessary halving
claim over every rational observable on this legal input population.

The elementary identification of continuous uniform phase probabilities
with the two equal-length phase strata is paper-only and explicit.
The known variance-ordering failure is credited to Douc, Cappe, Moulines
(2005), https://arxiv.org/abs/cs/0507025.

Run `lake env lean -DwarningAsError=true Main.lean` in `lean/`.
Parent fresh build and PDF review are separate from delegated development.
Developed by a delegated AI agent with a self-review; the coordinating
agent reviews it separately. No external independent review is claimed.
