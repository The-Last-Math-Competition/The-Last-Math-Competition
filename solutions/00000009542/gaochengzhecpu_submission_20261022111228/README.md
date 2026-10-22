# Disproof of Conjecture 00000009542

Three actual qutrit-to-classical-bit CPTP maps have common-input max-min quantum mutual information h(1/3), strictly below their min-max value log2. The compound entanglement-assisted coding theorem identifies the first value with operational capacity, refuting the proposed finite-set formula.

## Scope

Refutes the first capacity formula for a fixed unknown memoryless channel from a finite set. Inputs include every coherent density matrix. No separate claim is made against continuity or the error-exponent assertion. Natural logarithms give nats; conversion to bits rescales both quantities equally.

## Formalization

Lean uses genuine complex PSD trace-one states and actual von Neumann entropy via trace of continuous functional calculus. A spectral/Jensen proof establishes pinching entropy increase. Actual complex-linear Kraus maps satisfy complete positivity for every finite matrix amplification, trace preservation, a genuine Stinespring isometry and both partial-trace formulas. The true entropy-exchange mutual information is bounded for all coherent states and evaluated on explicit attaining diagonal states. Actual real suprema over all density matrices and finite infima over channels give h(1/3)<log2. The operational coding theorem and standard purification equivalence of the entropy-exchange expression are mathematical/public-reference bridges, explicitly not claimed formalized or assumed as custom Lean axioms. An exact rational auxiliary checker verifies all channel matrix units and logarithmic coefficients.

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
