# Disproof of Conjecture 00000002854

The genuine single-factor SEM Y = lambda H + E, with independent standard Gaussian latent factor and error and both variances fixed at one, has observed covariance lambda^2 + 1. Its Jacobian is 2 lambda and has full rank outside the proper algebraic set {0}, but every nonzero lambda is observationally indistinguishable from -lambda. Equal complete observed Gaussian laws are also formally proved.

## Scope

Refutes the claimed sufficiency of full generic Jacobian rank for strict global identifiability of labelled real SEM parameters, hence the stated equivalence. The parameter space is all real loadings, with no latent-sign quotient or positive-loading convention. The result does not refute identifiability after such a quotient or restriction, nor a local-identifiability criterion, nor a particular instrumental-variable specification.

## Formalization

Lean defines the actual 1-by-2 loading matrix and fixed 2-by-2 exogenous covariance, computes L Sigma L-transpose, and defines its genuine Jacobian through deriv. It proves generic full determinant rank with exceptional set {0}, covariance noninjectivity and generic sign ambiguity, and negates the universally quantified RankCriterion on the affine single-factor SEM subclass. Separately it constructs the genuine product of two standard Gaussian probability measures and proves equality of their observed pushforward laws under opposite loadings. It does not separately evaluate Gaussian variance integrals; the covariance specification is the standard fixed exogenous covariance of the model. Audited principal theorems use only propext, Classical.choice and Quot.sound.

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
