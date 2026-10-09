# Independent semantic review of the frozen proof for conjecture 00000000161

## Status and scope

**No blocking mathematical or source-correspondence issue found in the frozen Lean proof.** The submission proves a disproof of the original claim under its ordinary positive, dimension-only meaning of `poly(n)`. The stronger dimension-four theorem makes the unspecified polynomial harmless: it rules out every fixed positive real denominator.

This is a semantic source review, not an independent compilation certificate and not yet a review of the mandatory LaTeX report or PDF. Root assigned the engineering rerun separately and has not yet handed over the matching report/PDF. Full submission acceptance remains pending those checks.

I inspected all of `Conjecture161.lean`, `Conjecture161/Arithmetic.lean`, `Audit.lean`, `lakefile.lean`, `verify.py`, `AUTHOR_NOTES.txt`, the version pins, `.gitignore`, and the recorded `verification.log`. I consulted only the designated original/rules and stock Mathlib sources needed to interpret the proof. I did not consult other solutions, conjectures, selector records, thread history/rosters, or external mathematical material. No author file was modified.

## Frozen identity

The SHA-256 of `/private/tmp/tlmc161-author/FREEZE_SHA256.json` is `d206561c63c216e68fd9a99847d2ecfb088bbc269d2052f47c79e2c7efd493fe`. I recomputed and matched all ten listed deliverables. The archive SHA-256 is `6fa566d323be3dcc318225b3230bb3b81c44a1ae8fd5457be25f84f9c69f6c5f`, also matching root's handoff.

Central mathematical source digests:

- `Conjecture161.lean`: `a2b59c6cb728fcc8f6b5ff22510254968c5cc64467f6b721bf4b5bcba43c7058`.
- `Conjecture161/Arithmetic.lean`: `aa092fc38992b0ae4a321786c0d0892baef0e947ba0ad14054dd6f5440134b0b`.

## Central objects and quantifiers

`PrimeIndex` is exactly the subtype of natural primes with inherited natural-number order. Its inhabitant is the prime 2. There are no composite inputs, empty index types, changed orderings, or supplied false hypotheses. `primes_tendsto_nat_atTop` uses stock `Nat.exists_infinite_primes` to show the prime values tend to infinity. `prime_index_neBot` is valid because the nonempty linearly ordered subtype is directed; the standard `atTop` filter is therefore nonbottom. The later uniqueness-of-limits argument uses that same standard filter and the ordinary real topology. The stock nonbottom instance is available directly even though the named theorem is not explicitly invoked there.

`GeneralLinear n p` is `Matrix.GeneralLinearGroup (Fin n) (ZMod p)`, which stock Mathlib defines as the units of the square matrix ring. Matrix multiplication is the standard matrix product. For prime `p`, the stock field instance on `ZMod p` is obtained from `Fact p.Prime`, and `ZMod.card` gives precisely `p` elements. Thus the sample space is the actual `GL_n(F_p)`, with a unique matrix inverse rather than multiple representations affecting cardinality.

`LargePrimeFactor` requires a natural prime `r`, divisibility `r ∣ orderOf A`, and the strict real inequality `p^(n-1)/C < r`. `orderOf` is stock multiplicative group order. The exponent uses natural subtraction, which agrees with ordinary `n-1` throughout the asserted domain `n >= 2`. No restriction to irreducible, semisimple, diagonalizable, or selected elements is present.

`successProbability` divides the cardinality of the event subtype by the cardinality of the full group, interpreted in the real numbers. That is exactly uniform counting probability on the finite group. `sampleSpace_card_pos` proves both the finiteness/nonemptiness needed to avoid the infinite-type-zero behavior of `Nat.card` and a strictly positive denominator. The group identity supplies nonemptiness. `successProbability_mem_Icc` additionally verifies the ratio lies in `[0,1]` using the event inclusion. The later zero-probability proof works by actual emptiness of the event, not a zero denominator or a malformed cardinality.

`OriginalClaim` existentially quantifies a real polynomial positive at all integer dimensions at least two, then requires the limit one for every such fixed dimension. This is an explicitly declared interpretation of the source's unspecified `poly(n)`, rather than a quotation of formal quantifiers absent from the original. The submission goes further: for every `C > 0`, dimension four has eventual probability zero, and `no_positive_denominator_function` excludes every positive dimension-only denominator function. Accordingly, allowing a chosen polynomial, different fixed coefficients, or a choice of fixed denominator separately at dimension four does not affect the disproof. A denominator depending on `p`, a nonpositive denominator, or a conjecture asserting only selected dimensions would be different claims; none appears in either original language version.

## Mathematical proof and formal bridges

The arithmetic lemma is valid for every natural `p >= 2` and every prime `r` dividing the standard four-factor order product. Writing `p = 2+q` ensures all needed factors are positive and handles natural subtraction explicitly. Its four identities give

`product_(i=0..3)(p^4-p^i) = p^6 (p-1)^4 (p+1)^2 (p^2+1)(p^2+p+1)`.

The identities and exponent multiplicities are correct. Each use of `Nat.sub_eq_of_eq_add` is justified by a polynomial identity, so truncated natural subtraction does not hide an assumption. `Fin.prod_univ_four` covers all four factors. Euclid's lemma `Nat.Prime.dvd_mul` and `dvd_of_dvd_pow` reduce a prime divisor to one of `p`, `p-1`, `p+1`, `p^2+1`, or `p^2+p+1`. All are positive for `p >= 2`; bounding a divisor by its positive dividend and then by `p^2+p+1` is valid. Primality is essential and is present.

The key group bridge is fully proved at `Conjecture161.lean:81`: `r ∣ orderOf A` is composed with `orderOf_dvd_natCard A`, then stock `Matrix.card_GL_field` and `ZMod.card` replace the actual group cardinality by the exact arithmetic product. This closes the potential gap between a bare number-theoretic product and orders of real matrix-group elements. Stock `card_GL_field` applies to the finite field and counts ordered independent columns; I inspected its whole short source proof and its group-to-columns equivalence. Stock `orderOf_dvd_natCard` is Lagrange's theorem, including its finite-group branch. Although that generic theorem has a trivial infinite-group branch, it is used here on the demonstrably finite group with the positive cardinality above.

`threshold_dominates` correctly proves, for `C > 0`, `x >= 1`, and `x >= 3C`,

`x^2+x+1 <= 3x^2 <= x^3/C`.

The division comparison has the required strict positivity hypothesis. Prime `p >= 2` supplies `x >= 1`. Therefore every prime divisor of every order satisfies `r <= p^3/C`. The original event requires a strict reverse inequality, so equality at the threshold is correctly excluded.

The remaining chain is complete:

| Theorem | Checked meaning and role |
| --- | --- |
| `prime_le_of_dvd_gl4_card_product` | Correct universal arithmetic bound, with actual prime-divisor hypothesis. |
| `primes_tendsto_nat_atTop` | Unbounded prime-valued index sequence/filter via Euclid's theorem. |
| `prime_index_neBot` | Nonvacuous filter used for unique real limits. |
| `sampleSpace_card_pos` | Finite nonempty matrix group and nonzero counting denominator. |
| `successProbability_mem_Icc` | Genuine normalized counting probability. |
| `prime_divisor_order_le` | Actual group order connected to the cardinal-product bound. |
| `threshold_dominates` | Correct sufficient threshold `p >= 3C` for each `C > 0`. |
| `no_largePrimeFactor_four` | Empty source event for every matrix once the threshold holds. |
| `successProbability_four_eq_zero` | Zero probability follows from empty event. |
| `successProbability_four_eventually_zero` | An Archimedean natural bound and prime unboundedness give eventual zero for every fixed `C > 0`. |
| `successProbability_four_tendsto_zero` | Eventual equality with the zero function gives limit zero. |
| `successProbability_four_not_tendsto_one` | Hausdorff uniqueness on a nonbottom filter contradicts simultaneous limit one. |
| `no_positive_denominator_function` | Specializes any purported positive dimension-only denominator to dimension four. |
| `conjecture_false` | Specializes the declared polynomial reading to dimension four, an allowed fixed dimension. |

No additional number-theoretic distribution assumption, matrix classification theorem, numerical experiment, rate estimate, or unproved existence of exceptional matrices is needed. The argument proves that the event is eventually impossible for all matrices.

## Stock references and trust boundary

I inspected the relevant stock source definitions or statements and their local proofs for `Matrix.GeneralLinearGroup`, `Matrix.card_GL_field`, its column equivalence, `ZMod.card`, the prime-field instance on `ZMod`, `orderOf`, `orderOf_dvd_natCard`, `Nat.card_pos`, `Nat.card_le_card_of_injective`, `Nat.exists_infinite_primes`, `Nat.Prime.dvd_mul`, `Nat.Prime.dvd_of_dvd_pow`, the standard `atTop` definition and nonbottom instance, and `tendsto_nhds_unique`. These references have the required hypotheses and the claimed mathematical meanings.

The submitted mathematical files contain ordinary definitions and kernel-checkable proof scripts. There is no submitted custom axiom, `sorry`, `admit`, `native_decide`, unsafe declaration, alternate semantics, or local notation shadowing the central operations. `Audit.lean` enumerates all fourteen submitted theorems and prints the five central definitions. The frozen author log reports only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. This reported result is consistent with source inspection but remains author-generated evidence until the separately assigned fresh engineering rerun confirms it.

`verify.py` is a verification driver, not a mathematical computation used in the proof. I read it in full. It checks the pinned Lean/manifest, dependency revisions and tracked changes, rebuilds the submitted project, performs warning-as-error source checks, and requires exact audit coverage and allowed axiom sets. Its log is evidence of the author's run, not evidence that I independently executed those commands. Root should rerun in an isolated copy because the driver intentionally rewrites `verification.log` and the local generated build directory.

## Findings and remaining work

No semantic correction to the frozen proof is requested. `AUTHOR_NOTES.txt` accurately describes the mathematical argument and declared convention for `poly(n)`. The report should retain that convention and the stronger `for every C > 0 at n=4` result, rather than presenting the existential-polynomial quantifiers as text literally specified in the original.

Pending before a full rules-compliant acceptance: independent compiler/axiom confirmation, full matching LaTeX/PDF inspection, and root's separately handled eligibility/submission-scope checks. This review does not assess external publication eligibility or authorize publication.
