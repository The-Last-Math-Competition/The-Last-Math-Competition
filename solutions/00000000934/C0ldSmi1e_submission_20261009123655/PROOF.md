# A norm-unconditionally convergent, non-absolutely summable series in L¹(T)

## Exact source and convention

Conjecture 00000000934 says: “There exists an unconditionally convergent series Σfₙ in L¹(T) that remains unconditionally convergent after every sign change yet admits no absolute rearrangement (the boundary of Orlicz's theorem).” Its Chinese version is included verbatim in `ORIGINAL.md`.

We prove the assertion using complex scalars. Set T = R/Z and let μ be normalized Haar measure, of mass one. For this circumference-one circle it is also the standard Lebesgue volume. L¹(T) means the Banach space of measurable complex-valued functions modulo equality μ-almost everywhere, with norm ||f||₁ = ∫T |f| dμ. Likewise L² uses the standard integral-square norm. These are exactly Mathlib's `MeasureTheory.Lp` spaces, not spaces of pointwise representatives or a surrogate sequence topology.

Unconditional convergence means convergence in norm of the net of sums over finite subsets of the index set. A sign choice is an arbitrary function ε:N→{−1,1}; there is no finite-support, eventual-constancy, computability, or other restriction. An absolute rearrangement would be a bijection π:N→N such that Σₙ||f_{π(n)}||₁ is finite. The parenthetical reference to Orlicz's theorem is descriptive: the exact source gives no additional numerical endpoint property to prove.

## Construction

For n≥1 put eₙ(x)=exp(2πinx) on R/Z and fₙ=n⁻¹eₙ. Set f₀=0. The exponential is well-defined on R/Z because its values are invariant under adding any integer to x. Adding this initial zero term is immaterial to every convergence assertion. In Lean this same convention follows from the field convention 0⁻¹=0.

We prove the stronger statement allowing every complex unit phase εₙ, |εₙ|=1, in place of signs.

## Unconditional convergence

The exponentials are orthonormal in L²(T):

∫T conjugate(eₘ)eₙ dμ = 1 if m=n, and 0 otherwise.

For m=n the integrand is one. For m≠n the integrand is the nonconstant character e_{n−m}; translating by 1/(2(n−m)) changes its sign, while Haar invariance preserves its integral, so that integral is zero. This is the orthogonality calculation used by the imported, kernel-checked `orthonormal_fourier` theorem.

Fix any infinite unit-phase choice ε. For finite sets F,G⊆N, orthogonality gives

||Σ_{n∈F} εₙfₙ − Σ_{n∈G} εₙfₙ||₂²
= Σ_{n∈F△G, n≥1} 1/n².

Given δ>0, choose M with Σ_{n>M}1/n²<δ². Such M exists by convergence of the p-series with exponent 2. If both finite sets contain {0,…,M}, then their symmetric difference lies above M, so the displayed norm is less than δ. Thus the net of finite sums is Cauchy. Completeness of L² supplies its limit. In Lean the standard theorem `OrthogonalFamily.summable_iff_norm_sq_summable` encapsulates exactly this finite-subset Cauchy argument; the coefficient square summability is proved using `Real.summable_nat_pow_inv` at exponent 2.

By Cauchy–Schwarz and μ(T)=1,

||g||₁ = ∫T |g|·1 dμ ≤ (∫T |g|² dμ)^(1/2) = ||g||₂.

Consequently the identity on a.e. classes defines a bounded linear inclusion L²→L¹, and maps the convergent L² net to a norm-convergent L¹ net. This proves unconditional convergence for every unit-phase choice. Taking εₙ=1 gives the original series; restricting εₙ to ±1 gives every requested termwise sign change.

For a fixed phase choice and every bijection π, the finite prefix sets {π(0),…,π(N−1)} are eventually above every prescribed finite subset. Their sums therefore converge in L¹ norm to the same sum. The formal development separately proves this common-limit assertion, as well as the norm convergence of the entire finite-subset net.

## No absolute rearrangement

Since |eₙ(x)|=1 and μ(T)=1, each n≥1 satisfies ||fₙ||₁=1/n. Multiplication by a unit phase preserves that norm. The harmonic series diverges: each block 2ᵏ≤n<2ᵏ⁺¹ contributes at least 2ᵏ/2ᵏ⁺¹=1/2.

A bijection merely reindexes a nonnegative family and cannot change the supremum of its finite sums. Hence for every unit-phase choice ε and every bijection π,

Σₙ ||ε_{π(n)}f_{π(n)}||₁ = +∞.

Equivalently, no such norm sequence is summable. The formal proof uses the exact norm identity and `Real.not_summable_natCast_inv`, together with `Equiv.summable_iff`. It additionally proves that the ordinary finite partial sums of these norms tend to +∞ for every phase choice and every permutation. Therefore no absolute rearrangement exists, completing the entire existential claim under the stated complex scalar convention.

## Source-to-theorem mapping

All names below are in namespace `Conjecture934` in `Solution.lean`.

| Mathematical content | Lean declaration(s) |
|---|---|
| Circle R/Z and normalized Haar; actual a.e. Lp spaces | `Circle`, `μ`, `L1`, `L2` |
| Agreement of μ with circumference-one Lebesgue volume | `measure_eq_volume` |
| L¹ norm is the integral of the pointwise absolute value | `L1_norm_integral` |
| Identity on a.e. classes is linear and bounded L²→L¹ | `inclusionLinear_exists`, `inclusionLinear`, `inclusionLinear_apply`, `inclusion_norm_le` |
| Continuous linear inclusion with exactly that action | `inclusion_exists`, `inclusion`, `inclusion_apply`, `inclusion_fourier` |
| Concrete sequence and its a.e. representative | `term`, `term_ae`, `representative_on_real` |
| Exact L¹ monomial norm and harmonic term norm | `fourier_L1_norm`, `term_norm` |
| Unconditional convergence in L² for all unit phases | `phase_L2_summable` |
| Unconditional convergence in L¹ for all unit phases | `phase_summable` |
| Original unconditional series | `term_summable` |
| Full infinite sign quantifier and signed convergence | `IsSignChoice`, `sign_summable` |
| No norm-absolute permutation | `no_absolute_rearrangement` |
| No norm-absolute permutation even after any unit phases | `phase_no_absolute_rearrangement` |
| Explicit norm convergence of the finite-subset net | `phase_unconditional_norm` |
| Every permutation converges to the same norm limit for fixed phases | `phase_permutation_norm` |
| Every reordered signed/phase norm series tends to +∞ | `phase_norm_partial_sums_diverge` |
| Exact existential source claim | `conjecture` |
| Stronger existential claim with all complex unit phases in both clauses | `strengthened_conjecture` |

`Summable` is defined in Mathlib as `∃ s, HasSum f s`; `HasSum` is the convergence of the finite-subset sum net to s. Thus its topology is the norm topology of the stated L¹ space. The separately exported norm-limit lemmas remove any dependence on an informal reading of that name.

The chosen inclusion maps are selected from propositions whose witnesses are explicitly constructed. Their action is proved for every input by the apply lemmas. This device prevents Lean from producing irrelevant executable compiler helpers containing erased-proof placeholders; it adds no assumption and changes no mathematical map.

## Certification and scope

Lean 4.19.0 with Mathlib v4.19.0 at the pinned commit verifies the complete development. All 36 owned declarations, including five generated proof/equation helpers, pass the audit. Every owned declaration's full axiom closure is contained in {propext, Classical.choice, Quot.sound}; an additional explicit traversal of 30,946 transitive declarations finds no unsafe constant and no other axiom. There are no admissions, owned axioms, numerical experiments used as proof, or external mathematical assumptions.

This proof is for complex-valued L¹ as explicitly stated. It does not claim a separately formalized real-valued version or any additional endpoint characterization attributed to Orlicz. No mathematical gap remains in the stated theorem. Historical/source-attribution research and submission-eligibility checks are outside this independent author's scope.
