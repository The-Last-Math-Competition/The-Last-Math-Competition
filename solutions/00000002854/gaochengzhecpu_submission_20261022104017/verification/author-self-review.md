# Conjecture 2854 adversarial self-review

Verdict: PASS for strict global identifiability on the explicitly stated labelled parameter space. Parent fresh build, PDF and independent adversarial check remain pending.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. Read the frozen English and Chinese source. Both explicitly propose global identification iff the generic Jacobian rank deficit is zero. The example attacks the sufficient direction, not the unspecified instrumental-variable correction.
2. Real mathematical model: one latent variable H, one observed Y=lambda H+E; independent centered standard Gaussian H,E. The parameter space is all real lambda. Both variances and the covariance are fixed, avoiding a hidden extra scale parameter.
3. Lean uses rectangular matrices, actual multiplication L Sigma L-transpose, the ordinary derivative of the actual covariance entry, and the determinant of its actual 1-by-1 Jacobian. Generic full rank is witnessed outside finite set {0}, which is a proper algebraic subset. No opaque numeric certificate substitutes for the SEM.
4. Strict global parameter identification is covariance-map injectivity; positive and negative labelled coefficients are distinct. Opposite signs give equal covariance for every parameter, and distinct values at all nonzero parameters. Thus this also defeats generic global identification, not only a singular-point version.
5. Gaussian-law bridge is genuine: Lean constructs gaussianReal 0 1 product gaussianReal 0 1, proves the first-coordinate reflection preserves that measure, and proves equality of the two output pushforward measures. Equal distribution is not merely assumed from a covariance equation.
6. Sign convention risk: some factor-analysis treatments quotient the latent sign or fix a positive loading. Those are different parameter spaces; both the paper and content JSON explicitly exclude them. The source does not impose such a quotient. The proposed unqualified global criterion is false on the ordinary labelled SEM parameter space.
7. Mathematical completeness: fixed covariance Sigma=I is model data. Lean computes its observed covariance and separately proves the full-law ambiguity. It does not calculate Gaussian first/second moment integrals, and the paper says so. No moment computation is needed to trust the observed-law nonidentifiability proof.
8. All four algebraic main results and the full-law sign theorem audit to propext, Classical.choice, Quot.sound. No sorry/admit/axiom/native_decide or hidden numerical approximation. Author strict check 04 passes with warnings as errors.
9. Earlier failures are preserved: 01 and 02 failed only at derivative elaboration; 03 passed algebraic development; 04 adds the Gaussian distribution bridge and passes. Publication must use 04 and the corresponding Main hash.
10. Parent-approved candidates only: 2854 and 2819. Backup785 was rejected due normalization ambiguity and never started.

## Author checks

Strict logs 2854-strict-01.log through 2854-strict-04.log are retained. Check 04 is the final successful strict check. Full project build log will accompany handoff. Parent is responsible for fresh build, TeX/PDF compilation, visual QA and publication.
