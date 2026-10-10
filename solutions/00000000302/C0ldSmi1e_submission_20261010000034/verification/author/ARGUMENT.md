# Independent argument for conjecture 00000000302

## Statement and source interpretation

The supplied English and Chinese statements are identical mathematically:

> Definition: II_α = {ξ : ∃c > 0, |ξ − p/q| > c/q^{2+α}} (the exponent-badly-approximable set). Conjecture: dim_H(II_{1/3} ∩ II_{1/2}) = dim_H(II_{1/2}).

Both texts leave the domains and quantifiers on p and q implicit. This proof makes the conventional meaning of that named Diophantine set explicit:

II_α = {x ∈ ℝ : ∃c ∈ ℝ, c > 0 and ∀p ∈ ℤ, ∀q ∈ ℕ with q > 0, |x − p/q| > c/q^(2+α)}.

The constant is uniform in p and q. Every positive denominator is included, including nonreduced representations. The inequality remains strict. The exponent is the real power. Hausdorff dimension means the ordinary metric Hausdorff dimension of subsets of ℝ, represented in Lean by Mathlib's global `dimH : Set ℝ → ℝ≥0∞`. No restriction to a unit interval, replacement of the set by a model set, or additional hypothesis on the original parameters is made. The only interpretative limitation is the source's omitted domains and universal quantifiers; if those were intended differently, this proof makes no claim about such an alternative.

## Result

For every α > 0, II_α has full Lebesgue measure and Hausdorff dimension 1. For every α, β > 0, II_α ∩ II_β has full Lebesgue measure and Hausdorff dimension 1. In particular, both sides of the conjectured equality equal 1.

## Measure-theoretic approximation fact

For fixed s > 2 and Lebesgue-almost every x ∈ ℝ, there is no real C such that, for infinitely many positive integers q, some integer p satisfies x ≠ p/q and |x − p/q| < C/q^s.

Here is the usual elementary measure argument. Fix integers m and K ≥ 1. On [m,m+1], define E_q by the existence of p with |x − p/q| < K/q^s. Since q ≥ 1 and s > 2, K/q^s ≤ K. Only integers p between (m−K)q and (m+1+K)q can contribute. Thus there are at most (1+2K)q+1 contributing numerators, and the sum of the lengths of their intervals is at most

2K ((1+2K)q+1) q^(−s).

The sum over q ≥ 1 is finite, since both exponents 1−s and −s are less than −1. The first Borel–Cantelli lemma implies that the set of points in infinitely many E_q has Lebesgue measure zero. Taking a countable union over m ∈ ℤ and K ≥ 1 still gives a null set. Every real constant C is bounded above by some positive integer K, so outside this null set the displayed infinitely-often approximation condition fails for every C. This proves the fact for fixed s. The Lean development uses the stronger stock theorem `ae_not_liouvilleWith`, proved in Mathlib from convergent power-series bounds and Borel–Cantelli. Its predicate is the actual rational approximation condition just displayed, with denominator frequency along the natural numbers tending to infinity.

## Turning the asymptotic estimate into the strict uniform inequality

Fix α > 0 and put s = 2+α. Choose an irrational x for which the approximation fact holds; irrationality also holds almost everywhere because the rationals are countable.

Apply the fact with C=1. Since x is irrational, x ≠ p/q for every integer p and positive integer q. Therefore there exists N ∈ ℕ such that for all q ≥ N and all p ∈ ℤ,

|x − p/q| ≥ 1/q^s.

There is ε > 0 such that |x − p/q| ≥ ε for every integer p and 1 ≤ q ≤ N. Indeed, for each fixed positive q the lattice (1/q)ℤ is closed and does not contain x, so x has positive distance from it; take the minimum over the finitely many denominators. If there are no such denominators, any positive ε suffices. Lean invokes Mathlib's corresponding bounded-denominator separation lemma, which even includes denominator zero under Lean's totalized division; only positive denominators are used in II_α.

Set c = min(1, ε)/2. Then c>0, c<1 and c<ε. For q≥N,

c/q^s < 1/q^s ≤ |x−p/q|.

For 1≤q<N, the inequality q^s≥1 gives

c/q^s ≤ c < ε ≤ |x−p/q|.

Thus x ∈ II_α with the same positive c for every p and positive q, and with the required strict inequality. This establishes that II_α has full Lebesgue measure.

## Hausdorff dimension and the original equality

A full-Lebesgue-measure subset S⊆ℝ agrees almost everywhere with ℝ, so its Lebesgue measure is infinite. On ℝ, one-dimensional Hausdorff measure with Mathlib's normalization equals Lebesgue measure. Consequently dim_H S≥1. Monotonicity and dim_H ℝ=1 give dim_H S≤1, hence dim_H S=1.

The intersection of two full-measure sets has full measure, since its complement is the union of two null sets. Therefore, for α,β>0,

dim_H(II_α∩II_β)=1=dim_H(II_β).

Taking α=1/3 and β=1/2 proves the conjecture.

## Formalization correspondence

`Conjecture302.II` is exactly the quantified set stated above. The seven submitted theorems are:

1. `mem_II_of_not_liouvilleWith`: the strict uniform-constant argument.
2. `ae_irrational`: countability of rational numbers gives almost-everywhere irrationality.
3. `ae_mem_II`: full measure for every α>0.
4. `dimH_eq_one_of_ae_mem`: full measure implies actual Hausdorff dimension one.
5. `dimH_II`: dimension one for each positive parameter.
6. `dimH_inter_II`: dimension one for any two positive parameters.
7. `conjecture`: the exact requested equality at 1/3 and 1/2.

All theorem types and all kernel axiom dependencies are printed by `Audit.lean`. No auxiliary numerical computation is used or needed. The proof is a proof of the conjecture, not a disproof.
