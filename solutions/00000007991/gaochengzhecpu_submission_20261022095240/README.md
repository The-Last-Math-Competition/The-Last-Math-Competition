# Disproof of Conjecture 00000007991

Every eventually lower-bounded real function is incompatible with an ordinary derivative tending to minus infinity at plus infinity. An optimal Holder regularity exponent is nonnegative, so the source's stated infinity-endpoint slope is impossible.

## Scope

Refutes the negative-infinite-slope conjunct at p=infinity, hence the conjunction. No actual optimal p-Laplace exponent, PDE estimate, harmonic endpoint or p->1 limit is claimed. An additional exact calculation treats the displayed formula with a fixed real eigenvalue parameter, proving its derivative tends to zero whenever its necessary nonnegativity at p=3 holds; the main contradiction does not depend on that parameter interpretation.

## Formalization

Lean proves the actual real mean value theorem contradiction on a whole real interval for any eventually lower-bounded function. The eventual strictly negative derivative values themselves imply tail differentiability, so no extra smoothness assumption is added. Separate theorems cover nonnegative real and actual NNReal-valued functions, and directly negate existence of a candidate exponent graph. The optional constant-parameter formula is proved equal on an entire open tail to 1/(p-1); its genuine local derivative and filter limit zero are proved. No numerical verifier is needed.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
