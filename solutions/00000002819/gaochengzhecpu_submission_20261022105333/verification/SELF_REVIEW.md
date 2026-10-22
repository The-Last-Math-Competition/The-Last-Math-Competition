# Author-agent adversarial self-review: 00000002819

Verdict: PASS

# Conjecture 2819 adversarial self-review

Verdict: PASS for the standard rate-function-in-deviation-level reading. Parent fresh build, PDF QA and independent adversarial review remain pending.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. **Exact source claim.** Both language versions say the large-deviation rate is always a linear function in the independent subadditive setting. This is read as the usual LDP rate I(x), not the speed N. The paper explicitly says a reading about linear speed alone is not refuted. The source correlation-length correction is not formalized or claimed refuted separately.
2. **Actual random objects.** gaussianProduct is Mathlib's infinitePi of actual gaussianReal 0 1 measures on real sequences. Lean proves the coordinate laws and iIndepFun property, rather than assuming a hypothetical probability model. All coordinates are iid standard Gaussian. Fixed n denotes sample size N=n+1 throughout the means and LDP to avoid division by zero.
3. **Subadditivity is genuine.** blockSum is a true finite block sum. blockSum_add holds for every sample and all block indices, with the corresponding subadditive inequality. An additive process is a legitimate subadditive process. There is no independence correction or anomalous dependence hidden in this example.
4. **Probability bridge.** meanLaw is the actual pushforward of the sample mean. partialSum_mgf is proved from true Gaussian MGFs and independence. Its nonzero integral proves exponential integrability, and Mathlib's Chernoff inequality gives the actual probability upper bound. No numeric proxy or assumed tail inequality replaces the random law.
5. **Full LDP definition.** HasLDP ranges over every open set and every closed set, with nonnegative and lower semicontinuous rate. Lower bounds are pointwise in any x within an open G; upper bounds allow every real uniform lower bound a for I on a closed F. The paper explains equivalence to the usual logarithmic full LDP for finite rates. This is not merely a custom three-axiom necessary-condition package.
6. **Affine contradiction.** Nonnegative affine functions on all R are constant. The closed entire-line LDP upper bound and probability one force constant zero. The lower bound on the actual open interval (1,2), with epsilon 1/4, then exceeds the actual Chernoff upper bound exp(-N/2). The principal theorem quantifies over every pair of real affine coefficients.
7. **No bounded-support loophole.** mean_interval_positive formally proves every nonempty real open interval has positive mean-law probability at each N. The proof uses positive Gaussian interval measure and an actual independent finite-coordinate box event whose sample mean lies inside the interval. Thus (1,2) is genuinely inside the effective support.
8. **Quadratic transform.** coordinate_cgf uses the true Gaussian distribution; cramerTransform is the actual supremum of tx-CGF(t), not a preselected quadratic. Lean proves its IsGreatest bound and value x^2/2, plus non-affinity. The paper's additional Gaussian-density proof that this quadratic is the full LDP rate is paper-only and honestly labelled. Formal exclusion of all affine LDP rates does not need that extra theorem.
9. **Trust audit.** Final principal results have only propext, Classical.choice, Quot.sound. No sorry/admit/axiom/native_decide or approximate decision procedure. Earlier failed elaboration checks are retained separately, and final checks must be identified by hash.
10. **Publication boundary.** Only the assigned new lane and locked draft were written. Parent supplied the permitted Gaussian cache; no Mathlib source or publisher was modified. Parent performs fresh compilation, visual QA, source-alignment adversarial review and single-PR publication.

## Author checks

- strict01: failed due to map elaboration, explicit measure argument, noncomputability annotation and a missing helper name.
- strict02: failed at one map simplification and one scalar factor simplification.
- strict03: principal complete no-affine-LDP counterexample passed.
- strict04: supplementary support/transform additions failed at an ENNReal finite-product positivity instance and beta reduction.
- strict05: all supplemented theorems passed with clean axiom audits.
- strict06: final theorem bundles actual iid Gaussian, block subadditivity and no-affine-rate conclusion; final strict log retained. Full project build accompanies handoff.


Reviewed artifact hashes:

- Main.lean: `0d67792c62505ecde657107c929e86bb1108b9a2690d4d740fa19bc4fdb54005`
- main.tex: `917cf9500ab81da81908581cf5f5390fb520f2dec7f483c5666972b7ff63c3dc`
- main.pdf: `2d016546027223fb989986ff0d24c587dd15b1e300e19dd038ff6a2b52507743`
- SOURCE.md: `8e180c352cf568ffb62f67326c9b455e7b9f27ef1087560ee7708990a424dcad`
