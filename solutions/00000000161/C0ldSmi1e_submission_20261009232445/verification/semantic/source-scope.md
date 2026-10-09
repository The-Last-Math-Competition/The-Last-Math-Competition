# Source-only scope assessment for conjecture 00000000161

This assessment precedes receipt or inspection of any submitted proof. It is not a proof review or an acceptance decision.

## Source integrity and access

I read only the bilingual conjecture and both contribution-rule files supplied in `/private/tmp/tlmc161-author-input`, together with that directory's checksum manifest. The manifest SHA-256 is `3f56a82d2facffacad8e92c98fcaa9576bd1f408246b6386cda52c81c6c48fb8`; the conjecture SHA-256 is `1c971b03093fe80cb0bcaadeb5eeaf3139f34b846d65e1eae3d4f103c256ec76`. Both match the designated handoff. The English and Chinese rules' checksums also match the manifest.

## Exact mathematical scope

The English and Chinese statements agree: for a fixed integer dimension `n >= 2`, as the prime `p` tends to infinity, a uniformly random element of `GL_n(F_p)` is conjectured, with probability tending to one, to have group-theoretic order divisible by a prime strictly greater than `p^(n-1) / poly(n)`.

The following conventions are needed for an exact formal rendering:

1. `p` ranges over primes, not arbitrary natural numbers. The limit must be along primes tending to infinity, or an equivalent nontrivial formulation; values at composite indices cannot establish the claim or its negation.
2. `n` is held fixed in the limit and satisfies `n >= 2`. The conjecture presents no exceptional dimensions.
3. Randomness is the uniform distribution on the finite group of invertible `n`-by-`n` matrices over the field with `p` elements. Sampling all matrices, a conjugacy-class distribution, or another weighting would require a separate equivalence argument.
4. The relevant order is the multiplicative order of the actual invertible matrix. A characteristic-polynomial statistic, matrix-entry bound, or auxiliary group element does not suffice without a proved connection.
5. A prime factor means a positive prime integer dividing that order. The inequality is strict and uses the stated exponent `n-1`.
6. `poly(n)` is unspecified in both languages. Its natural asymptotic reading is a positive polynomial-size denominator depending on `n`, independent of `p`; for fixed `n` it is a fixed positive finite constant. A proof or disproof must declare how it handles this ambiguity. In particular, a disproof valid at an allowed fixed dimension for every positive fixed denominator would cover the natural readings without choosing an arbitrary polynomial.
7. The probability limit is exactly one. A disproof must contradict that limit for an allowed dimension and compatible denominator, rather than merely show individual failures or a negligible exceptional family.

No additional hypotheses such as irreducibility, semisimplicity, a specified characteristic-polynomial type, or restriction to a subfamily of group elements appear in the original statement. Such a subfamily can be relevant only if its relation to the full uniform sample is established.

## Applicable contribution requirements

The rules require a complete proof or disproof, a LaTeX report and PDF, and a Lean 4 project. Reviewer duties include reading the complete report, establishing full compilation and absence of incomplete proof mechanisms, checking correspondence with the conjecture's definitions, and checking any auxiliary computation. Solver submissions must stay within their personal submission directory. The source-only work here does not establish any of those proof-specific conditions, nor does it assess whether another submission already solved the conjecture.

## Pending review

Once root provides the frozen proof path and digest, review must independently check all central definitions, hypotheses, theorem statements, proofs, and relevant stock lemmas for semantic correspondence, including the sampling measure and prime-indexed limit. The entire matching report and all PDF pages remain to be inspected when supplied. Engineering reruns are assigned to root; their outcomes must be treated separately from semantic validity.
