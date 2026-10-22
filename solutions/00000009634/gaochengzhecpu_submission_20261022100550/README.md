# Disproof of Conjecture 00000009634

An explicit stationary four-symbol Markov process has full infinite word-Hankel rank three, while every normalized nonnegative HMM realization needs at least four states and an actual four-state model attains that bound. Its full positive-probability language has a concrete finite labelled graph presentation.

## Scope

Refutes the first equality between minimal hidden-state count and Hankel rank, hence the source conjunction. No assertion about finite-word learning complexity or geometric isolation is claimed. The process is in fact supported on a four-vertex shift of finite type, and the competing models may have arbitrary finite state count, transitions, emissions and initial distribution.

## Formalization

The all-word Hankel matrix uses actual Mathlib Matrix.cRank, including empty-word rows and columns. An explicit whole-matrix factorization through three real columns gives the upper rank bound, and a genuine invertible 3-by-3 Hankel minor with determinant 1/512 gives the lower bound. Every competing HMM supplies a nonnegative factorization of the actual length-two probability block. Its four positive diagonals and crossed zeros force four distinct hidden indices, proving exact least state count four with the concrete witness. Genuine matrix-product probabilities, stationarity, both all-word consistency identities, state-emission convention bridges and the exact finite labelled support are proved. The exact Fraction verifier is supplementary, not a Lean oracle.

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
