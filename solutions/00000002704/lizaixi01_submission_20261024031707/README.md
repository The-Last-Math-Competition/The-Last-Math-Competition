# Counterexample to 00000002704

The map `f(z) = -z` on the actual field `Q_5` has the genuine global analytic inverse `g(z) = -z`, nonzero derivative `-1`, and multiplier norm `1`. The actual inverse power series has radius infinity. Yet every positive-radius ball about zero contains a nonzero point whose entire inverse-iteration orbit stays in the ball and does not converge: its even and odd subsequences are the distinct constants `x` and `-x`.

The complete Lean proof uses native `ContinuousLinearMap.fpowerSeries`, `FormalMultilinearSeries.radius`, and `HasFPowerSeriesOnBall`, actual derivatives and the actual 5-adic norm. Small points are genuine powers of `5`; no radii, norms or rates are assigned as numerical definitions.

The original source does not state an attracting multiplier condition. This refutes its unconditional iteration-convergence clause only. It does not contradict the inverse function theorem or a contraction theorem with their hypotheses, and does not assign an undefined convergence-rate constant.

The submission includes the original bilingual source, LaTeX and rendered PDF, the full pinned Lean project, exhaustive namespace axiom checks, exact build/fresh-kernel receipts and file hashes.
