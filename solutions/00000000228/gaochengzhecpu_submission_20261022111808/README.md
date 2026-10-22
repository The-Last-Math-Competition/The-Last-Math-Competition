# Disproof of Conjecture 00000000228

For the actual uniquely defined Stern sequence, s(n^2)/3^(log_2 n) tends to zero along every positive integer index. Its genuine uniform positive-index empirical laws converge in the CDF sense to the point mass at zero and cannot have a continuous fractal limiting distribution.

## Scope

Refutes the first continuous-fractal distribution assertion under the exact supplied normalization. The full sequence, not just a dyadic subsequence, tends to zero. No definition of the separate spectral-dimension/turning-density clause or alternative Stern normalization is selected.

## Formalization

Lean constructs actual adjacent Stern pairs, proves all four original recurrence rules and uniqueness, positivity, all eight three-bit growth cases and a global inclusive power bound. Actual Real.log and real powers give denominator>=27^m and the all-index bound 25*(25/27)^m on base-eight blocks. A genuine finite uniform PMF is pushed forward through the actual positive-index sequence. Exact tail counts and a finite-set injection give all positive-threshold CDF limits, exact nonpositive CDF values, and actual CDF convergence to Measure.dirac0 away from its discontinuity. A separate theorem excludes every continuous CDF limit. The standard necessary weak-convergence criterion is explained in the paper rather than claimed fully formalized. An independent exact two-algorithm verifier checks the recurrence and block bounds on finite ranges; it is not a Lean oracle.

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
