# Disproof of Conjecture 00000005501

A genuine stationary open M/M/1 queue has mean rho/(1-rho). Along a stable sequence approaching load one, the actual probability captured by every fixed multiple of the proposed inverse-square-root deficit scale tends to zero.

## Scope

Refutes the claimed half-power queue-length scale in the stated class, which includes a single station. Both total population and waiting-only queue conventions are covered. The counterexample is stationary and does not claim a centered fluctuation law, transient approximation, or formula for the additional unspecified prefactor.

## Formalization

Actual PMF arrival/service transitions and all entries of their Poisson-uniformization generator identify the M/M/1 queue. Detailed balance, repeated PMF binds and actual Poisson mixing prove all-time stationarity of the genuine geometric PMF. Its true nonnegative Lebesgue expectation is proved to equal rho/(1-rho). Along rho_k=1-(k+2)^(-2), Lean proves stability, approach to one, the exact square-root deficit, divergent half-power normalized mean, and actual cutoff probabilities tending to zero at every fixed integer multiple of the proposed scale. The actual pushforward waiting-only PMF has the same obstruction. Uniformization is the standard model construction; no independent holding-time path construction or derivative-at-time-zero theorem is claimed.

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
