# Parent adversarial review: 00000008263

Verdict: PASS

I read both exact source languages, the complete final Lean file, the whole paper and author self-review. The tested variance is the standard conditional variance of the equally weighted empirical observable after one resampling step, with input particles and weights fixed. A universal variance-halving law implies the submitted restricted claim for every rational observable on this legal four-particle population. The counterexample is stronger than a failure of equality: systematic variance exceeds multinomial variance, so an at-most-half interpretation also fails.

The input weights are positive and sum to one: (1/8,3/8,1/8,3/8). The observable (1,0,1,0) can live on four distinct particle states. The inverseCDF uses actual cumulative-weight comparisons, and systematic sampling uses the genuine positions U+k/4. I checked the full phase-selection proof, which quantifies over every phase in the correct interval and every label, for arbitrary ordered fields. For the lower half of the phase interval it selects (0,1,2,3); for the upper half it selects (1,1,3,3). This is not a numerical check of two offsets.

The two phase strata have equal interval lengths, so a uniform real phase induces the finite law with probabilities one half. That elementary continuous-measure identification is explicitly paper-only. Its algorithmic premise is proved for all phases and all observables in Lean, so choosing a representative per stratum loses no distributional information. The finite probability laws include nonnegativity and normalization proofs. The multinomial law is the actual four-fold categorical product on all 256 ordered outcomes; no Bernoulli surrogate or manually assigned variance table replaces it in the formal proof.

Both expectations are computed from the estimators and laws and equal the target one quarter. Their centered-square expectations give systematic variance 1/16 and multinomial variance 3/64. The parent fresh build rechecked the complete exact finite sums through kernel-checked norm_num proofs. The strict inequality 4/64>3/64 is therefore tied to actual algorithmic random variables. Ordering is kept fixed as in the standard algorithm; an added random permutation would be an additional hypothesis absent from the source. The known general phenomenon is properly credited to Douc, Cappe and Moulines rather than claimed novel.

The independent clean build and strict direct Lean command both succeeded, and only the standard foundational axioms occur in the final audit. Native desktop compilation and Tectonic export succeeded. I inspected all three final PDF pages, including inverse-CDF cases, selected-label vectors, variance displays and source/reproduction text. No equations are clipped, text is complete and footers do not overlap. Final source and Lean/TeX hashes agree with the frozen handoff. The general particle-filter evolution is neither needed nor claimed formalized. Parent review and development self-review are separate; no external independent reviewer is claimed.


Reviewed artifact hashes:

- Main.lean: `c6a83bf49bbc08debe762573a25a9ed0a7d36f4e41c1eb7fa4250de1e4908c5f`
- main.tex: `bea8c9ba7e9dfadfcdf71536f5acbd5cf15fc52dafb3070548ef303106a2ec47`
- main.pdf: `06229367ec231ac6f5ee9fb20f965d38134537017c679d639228d094997812fd`
- SOURCE.md: `3dca909e47c8033eb6d908838c9f9da40a24d1449dcb2d6765f8c22ac97e27d3`
