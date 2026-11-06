# Parent adversarial review: 00000005512

Verdict: PASS

I read the exact bilingual source, the complete final Lean development, the whole paper and the author self-review. The source wording could mean a genuine hyperbolic/polynomial tail or merely the correct d-th-power recurrence. The paper and PR expressly distinguish these interpretations and do not refute the recurrence-only reading. The development handles both queue length at d=2 and selection count d at queue length two, rather than silently switching the asymptotic variable.

The coordinate drift is exactly rho(q_k^d-q_(k+1)^d)-(q_(k+1)-q_(k+2)), with every natural coordinate retained. I verified its source against the primary Budhiraja-Mukherjee-Wu mean-field equations, equation (2.6), and the paper also explains the arrival and service terms directly. The mean-field stochastic limit is accurately cited as model background and is not claimed as formalized.

The two-choice fixed point is an actual infinite tail sequence, not a truncated numerical recursion. Lean proves q0=1, positivity, monotonicity, limit zero, all drift equations, and the exact double-exponential closed form. Uniqueness in the tail class follows from constant flux and its vanishing limit, so an arbitrary choice among multiple equilibria is not substituted for the model's fixed point. Adjacent differences form nonnegative masses whose sum is one; HasSum additionally proves every actual survival-tail identity. Thus these are genuine probabilities with the needed normalization.

The tail-law negation retains an arbitrary positive lower constant and arbitrary eventual cutoff. All integer-weighted tails tend to zero. Any genuine finite real power law implies one of these weaker integer-polynomial lower envelopes by choosing a larger integer exponent; that elementary implication is explained explicitly. The general d-choice family is also stationary, normalized and has actual survival tails. Its exact length-two probability is 2^(-d-1), and the separate selection-count limit rules out a polynomial lower envelope in d. No conclusion about an undefined finite-server stationary model is asserted.

My fresh project build and strict direct Lean check succeeded with only the standard foundational axioms. Native desktop compilation and Tectonic export succeeded. A real overflow in the source paragraph was fixed only by adding emergency paragraph stretch; mathematical text and Lean stayed unchanged. I reran the PDF-only validation, confirmed unchanged Lean hashes, observed native success for the new TeX and inspected all three final pages. There are no remaining TeX warnings, clipped equations, missing text or footer collisions. Final hashes bind this parent review to the corrected PDF. Author self-review and parent adversarial review are separate; no external independent review is claimed.


Reviewed artifact hashes:

- Main.lean: `60cc2d28f49bff3bbb21c0c8ede7e7f78efc4816f70e5256843ea60cc3b6b252`
- main.tex: `95e4ceca875b8e7a069088da48b2974d3ee6783a18062e2f19bae500f220cafa`
- main.pdf: `911906e225346430381f5eaa888eed109460b27639a3c67532ebbe5c8c119d6d`
- SOURCE.md: `4e70f876f349dc4bf7e377687f8d1f2295d13acbc6c440626c87a726ec54570f`
