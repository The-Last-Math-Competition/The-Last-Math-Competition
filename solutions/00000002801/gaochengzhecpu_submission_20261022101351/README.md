# Disproof of Conjecture 00000002801

The actual two-state deterministic alternating chain is irreducible. Its full empirical-measure distributions obey a good LDP with unique-zero rate I(pi)=0 and I=+infinity everywhere else, so the rate has no ordinary real Hessian at its stationary zero.

## Scope

Refutes the Hessian-existence clause under the stated irreducibility assumption, hence the conjunction. The unique-zero clause holds in this example. No spectral-gap convention or Fisher-information normalization is chosen. The obstruction occurs along genuine probability vectors in the interior of the two-state simplex, not beyond its boundary.

## Formalization

Lean uses actual PMF transition kernels and an actual full path-law PMF, proving every finite cylinder probability equals the initial law times the actual transition product. The full two-coordinate empirical distribution is the genuine pushforward of that process law, with nonnegative masses summing to one and convergence to the actual unique stationary vector. Full standard all-open-set lower and all-closed-set upper LDP bounds are proved with the observation-count speed and EReal log0=-infinity. The actual rate is lower semicontinuous with compact finite level sets, and its unique zero is proved. Every interior simplex neighborhood contains an infinite-rate point, precluding any local real-valued representative and hence an ordinary Hessian. No numerical or auxiliary verifier is needed.

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
