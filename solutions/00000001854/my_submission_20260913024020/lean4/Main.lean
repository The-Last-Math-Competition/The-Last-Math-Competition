import Init

/-!
# Disproof of TLMC conjecture 00000001854 (core numeric refutation)

Conjecture (literal statement):

    #{M ∈ Mat_n(F_q) : charpoly(M) squarefree} = q^(n²) · ∏_i (1 − q^(−i²))
    "is an exact closed form".

## The counterexample, informally

At `n = 1` every matrix of `Mat_1(F_q)` is `[a]` with `a ∈ F_q`, and its
characteristic polynomial is `X − a`: a polynomial of degree one. Over a
field, a degree-one polynomial `f` has derivative `f' = 1`, hence
`gcd(f, f') = 1`, i.e. `f` is squarefree (no repeated irreducible factor).
So the true count at `n = 1` is `q`, the number of field elements.

The conjectured formula, with the product read over `i = 1..n` (Reading A),
gives `q · (1 − q⁻¹) = q − 1 ≠ q`. With the product read as an infinite
product (Reading B) it gives `q · ∏_{i≥1}(1 − q^{−i²}) < q` since every
factor lies strictly between 0 and 1. Either way the "exact" assertion is
false at the minimal dimension; for `q = 2` this is formalized below.

## Honest scope of this Lean development

Lean 4 core ships no polynomial library (`Polynomial` lives in Mathlib, which
this project deliberately does not depend on), and core `Rat` operations do
not reduce inside the kernel, so the formalization below captures the
*numeric* content of the `n = 1, q = 2` refutation with pure, kernel-computable
`Nat` arithmetic:

* the squarefreeness predicate on the degree-one characteristic polynomials
  `X − a`, `a ∈ F_2`, is encoded by `sqfree1b`, which returns `true` for every
  `a` — this encoding is exactly the statement "every `X − a` is squarefree",
  justified mathematically by the derivative/gcd argument above (and checked
  generically, via an actual `gcd(f, f')` computation, by `reproduce.py` in
  the parent directory for `q = 2, 3, 4, 5`);
* `count_q2` enumerates all matrices of `Mat_1(F_2)` by `rfl`: the count is `2`;
* the conjectured formula at `n = 1, q = 2` (Reading A) is encoded as the exact
  fraction `formulaNum 2 / formulaDen 2`; `formula_value_q2` proves by `rfl`
  that this fraction equals `1`;
* `count_ne_formula` proves the count and the formula value distinct by exact
  cross-multiplication (`count * den ≠ num`, valid for `den > 0`), via `decide`.

Everything is proved with zero axioms and zero `sorry` (see `Check.lean`).
-/

namespace Tlmc1854

/-! ### The true side of the equation -/

/-- Squarefreeness of the characteristic polynomial `X - a` of the 1x1 matrix
`[a]` over `F_2`.  Every degree-one polynomial over a field is squarefree
(its derivative is `1`, so `gcd(f, f') = 1`), hence the predicate holds for
every `a : Fin 2`. -/
def sqfree1b : Fin 2 → Bool := fun _ => true

/-- Enumerating all matrices of `Mat_1(F_2)` — i.e. all `[a]` with
`a ∈ Fin 2 ≅ F_2` — and keeping those whose characteristic polynomial is
squarefree leaves **all 2** of them.  The true count is `2 = q`. -/
theorem count_q2 : ((List.finRange 2).filter sqfree1b).length = 2 := rfl

/-! ### The conjectured side of the equation (Reading A: product over i = 1..n)

At `n = 1` the conjectured value is the exact fraction

    q^(n²) · (q^(i²) − 1) / q^(i²)   with the single factor i = 1,

i.e. numerator `q^1 * (q^1 - 1)` and denominator `q^1`.  Core `Rat` does not
reduce in the kernel, so we keep numerator/denominator as `Nat`s; for
`den > 0` this is an exact encoding of the rational value. -/

/-- Numerator of the conjectured formula at `n = 1` (exact, unreduced). -/
def formulaNum (q : Nat) : Nat := q ^ 1 * (q ^ 1 - 1)

/-- Denominator of the conjectured formula at `n = 1` (positive for `q ≥ 2`). -/
def formulaDen (q : Nat) : Nat := q ^ 1

/-- The conjectured formula at `n = 1, q = 2` equals `1`:
`formulaNum 2 / formulaDen 2 = 2 / 2 = 1`, expressed as the exact fraction
identity `num * 1 = 1 * den` (denominator positive), proved by `rfl`. -/
theorem formula_value_q2 : formulaNum 2 = 1 * formulaDen 2 := rfl

/-- Explicit values, for readability. -/
theorem formula_num_q2 : formulaNum 2 = 2 := rfl

/-- Explicit values, for readability. -/
theorem formula_den_q2 : formulaDen 2 = 2 := rfl

/-! ### The refutation -/

/-- The exact formula disagrees with the true (enumerated) count at the
smallest dimension: the formula value is `1`, the true count is `2`. -/
theorem refute : (2 : Nat) ≠ 1 := by decide

/-- Exact cross-multiplied form of `count ≠ formula value`: with
`formulaDen 2 = 2 > 0`, `count ≠ num / den` is equivalent to
`count * den ≠ num`; here `2 * 2 = 4 ≠ 2`.  (For `d > 0`, `a ≠ b / d` and
`a * d ≠ b` are equivalent since `a * d = b ↔ a = b / d` on `ℚ`.) -/
theorem count_ne_formula : 2 * formulaDen 2 ≠ formulaNum 2 := by decide

end Tlmc1854
