# Disproof of Conjecture 00000002819

Actual iid standard Gaussian coordinates on an infinite product probability space give samplewise additive, hence subadditive, block sums. Their genuine sample-mean laws satisfy a Chernoff bound exp(-N/2) on (1,infinity), incompatible with every affine real-valued LDP rate: nonnegativity forces a constant rate, normalization forces zero, and the open-set lower bound on (1,2) contradicts that exponential tail bound. Every nonempty real interval has positive probability.

## Scope

Refutes universal linearity of the rate as a function of the deviation level, allowing the larger affine class. The speed remains the standard linear speed N; no claim is made against an alternative reading that only the speed is linear. The contradiction is inside the full real support and does not exploit infinity outside a bounded support. The source's separate correlation-length correction is not analyzed.

## Formalization

Lean builds the genuine infinite product of gaussianReal 0 1, proves coordinate Gaussian marginals and independence, actual block-sum additivity/subadditivity, sample-mean pushforward probability laws, the partial-sum MGF, exponential integrability, and the Chernoff probability upper bound. It proves positivity of every nonempty real open interval. HasLDP is a full epsilon exponential formulation with nonnegative lower semicontinuous finite rate and bounds over all open and closed sets; Lean disproves existence of any affine rate satisfying it. A separate computation proves the Legendre transform of the true Gaussian CGF is x^2/2 and is non-affine. The optional paper proof that this quadratic rate itself satisfies the full LDP is not formalized and is unnecessary for the no-affine-rate theorem. Audited principal results use only propext, Classical.choice and Quot.sound.

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
