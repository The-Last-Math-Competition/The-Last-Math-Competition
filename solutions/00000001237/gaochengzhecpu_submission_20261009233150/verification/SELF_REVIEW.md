# Author self-review: conjecture 00000001237

Main.lean SHA-256: `b174d28b0c38efbcac398fca764ea05cdc1dff413db3d6970ed0335bfcd888d8`

SOURCE.md SHA-256: `a3649a4e9113defa2dfee8bc50e894e9be3eb05b4f25081bdba601af32c4997e`

1. The update function is the standard chip-firing rule, including its legality threshold and incoming-arc sum; it is not a predeclared cyclic permutation.
2. The graph is an actual directed three-cycle and is strongly connected. All lengths are one, so the lcm is unambiguously one.
3. Unique legality in every single-chip state and agreement with a separately defined single-vertex firing eliminate dependence on parallel versus sequential conventions.
4. Function.minimalPeriod proves the least positive return time, not merely that three is some period.
5. The submission uses configuration return on labeled vertices, as stated in the source; quotienting by rotation or counting laps would be a different quantity.

Numerical support is not needed: all arithmetic and finite cases are checked in Lean. See verification/BUILD.json and its logs for the independently recorded actual commands. This document is an author scope review, not an external review certificate.

Verdict: PASS (author self-review).

Fresh-directory lake build and direct Lean execution passed with warnings as errors. All reported axioms are standard. Native LaTeX compilation succeeded; Tectonic export and Poppler render passed. Both final PDF pages were visually inspected. Parent-agent adversarial review is still a separate required step.
