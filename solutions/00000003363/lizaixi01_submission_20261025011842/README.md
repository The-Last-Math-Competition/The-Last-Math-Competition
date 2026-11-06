# Problem 00000003363: a constant interval of genuine logistic entropy

This submission addresses only a **prominently disclosed canonical reading** of the printed nowhere-monotone clause: real logistic maps `q_a(x) = a*x*(1-x)` on the whole phase interval `[0,1]`, parameters in the full usual domain `[0,4]`, and topological entropy. The source does not specify the family, domain, entropy kind, or dimension correction. No assertion is made about another family, a parameter set restricted to chaos, global Milnor monotonicity, continuity of the entropy function, or the undefined fractal correction.

For every `a` in `[1/4,1/2]`, the actual selfmap has library-native full topological entropy zero. Consequently the actual entropy function is both weakly `MonotoneOn` and `AntitoneOn` the nonempty open parameter interval `(1/4,1/2)`. This contradicts nowhere monotone in its usual weak, non-strict sense under the stated conventions. The maps themselves form a genuinely nonconstant family: evaluating at `1/2` gives `a/4` and separates all parameters. Every local parameter is positive, and the real polynomial has degree two with a unique nondegenerate critical point.

The exact bilingual source is included in `SOURCE.md`. Its original LF SHA-256 is `2fa1885cf289d0420a9d044cc5c6a62209fac07f171d299abcf15578face03a4`, pinned at upstream `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400` (Git blob `d6e3ff00c793105b4c964dd425d2e19a513dceb8`). Eligibility is refreshed before publication; the initial metadata was false/false, the solution tree empty, and the exact-ID all-state searches empty.

## Actual objects and proof

- `Parameter` and `Phase` are real closed-interval subtypes. `maps_phase` proves invariance for every full-domain parameter; `logistic_continuous` proves continuity of each genuine selfmap.
- `quadraticPolynomial`, its evaluation identity, its native `natDegree`, and native real derivatives establish the actual quadratic and nondegenerate-critical-point claims. `family_injective` proves nonconstant parameter dependence without replacing the maps by labels.
- `local_contraction` proves a true `LipschitzWith (1/2)` bound from the factorization of the difference of two logistic values.
- `native_entropy_zero_of_nonexpanding` proves an all-scale entropy theorem from compactness, finite covers, all iterates, and native `Dynamics.coverEntropyEntourage`. It handles the positive finite cover cardinal, ENNReal logarithm, EReal quotient and limit, and supremum over every entourage. No entropy value is assumed or assigned.
- `entropy` is exactly `Dynamics.coverEntropy (logistic a) Set.univ`. The true open interval is proved open and nonempty, and `printed_nowhere_monotone_false` follows from its constant entropy and actual weak monotonicity.

Sebastian van Strien's author PDF, *Milnor's Conjecture on Monotonicity of Topological Entropy: results and questions* (6 July 2012), pp.1-2, supplies the standard model and terminology only. No literature theorem is an extra Lean axiom; the local zero-entropy argument is proved in full.

## Reproduction

The project pins Lean `4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. In `lean/`, run these four separate commands:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

After the separate version check, `bash verify.sh` runs the remaining three commands. `Check.lean` executes ordinary `#print axioms` for every owned namespace declaration, including generated/private names, and verifies the explicitly required names. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. There are no placeholders, `native_decide`, or extra axioms.

The final evidence contains source-bound original four-step logs, command and exhaustive axiom receipts, fresh-kernel output, actual thread-affinity samples, and a SHA-256 manifest. One heavy job runs at a time with CPUs `[0,2]` and two threads. Production timings are diagnostic; this submission is not a controlled efficiency sample or an organizer acceptance claim.
