# Conjecture 00000004003 — Disproof on the literal original-process-law reading

**Scope is essential:** this result concerns an original, unaugmented process/path law. It does not concern a probability law on signatures or a tree-like quotient, and does not refute standard uniqueness theorems on those spaces. The source states process distribution without the latter qualifications. Time augmentation and signature-injective path classes are outside the claim proved here.

Take x₁(t) = 4t(1−t) and x₂(t) = 8t(1−t), 0 ≤ t ≤ 1, and their two Dirac laws. Their midpoint values differ (1 versus 2), whereas the actual recursive iterated integrals give the same full signature (1,0,0,...). Both smooth paths start at zero. Their exact supremum norms are 1 and 2, giving all finite norm moments and inverse-even-moment-root Carleman summands 1 and 1/2.

The source does not specify a unique infinite-dimensional Carleman convention. The formal statement uses a genuine radial supremum-norm Carleman condition, which on the family x_A(t)=4At(1−t) is the ordinary amplitude moment condition because the supremum norm and midpoint evaluation equal A. The paper also explains why sampled-coordinate and variation moment readings are harmless for this finite-support family.

- `lean/Main.lean`: actual recursive `intervalIntegral` signatures, all-order formula by FTC, exact supremum norm, smooth based support, genuine probability measures, positive finite norm moments, divergent Carleman series, equal full expected signatures, and unequal laws restricted to [0,1].
- `main.tex`: full proof, interpretation boundary at the outset, and primary references explaining the tree-like/signature-law distinction.
- `SOURCE.md` and `verification/SOURCE_PROVENANCE.md`: frozen bilingual source and provenance.
- `verification/lean-strict.log`: actual warnings-as-errors output and standard-axiom audit.
- `verification/SELF_REVIEW.md`: adversarial self-review.

Reproduce from `lean/` using Lean 4.19.0 and the pinned Mathlib dependency:

`lake env lean -DwarningAsError=true Main.lean`

The Lean proof stores global extensions for differentiating, but the final conclusion compares actual pushforward laws on C([0,1], ℝ). It therefore does not exploit discrepancies outside the observed interval. The variation observation, arbitrary compact amplitude laws, and embedding in higher dimensions are paper-only.

Primary background references, read directly for scope: [Hambly–Lyons](https://arxiv.org/abs/math/0507536), [Chevyrev–Lyons](https://arxiv.org/abs/1307.3580).

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. A sibling agent also read the mathematical interpretation and formal scope, and the relevant limitations are disclosed above. No external independent review is claimed. The coordinator identified no prior submission when reserving the ID.
