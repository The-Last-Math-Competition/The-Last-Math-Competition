/-
  Disproof of conjecture `00000001097`: formalisation of the elementary core.

  Conjecture (as filed): the mean root count of `x^d + a*x + b` over `F_q` equals
  `1 + (q - 1) / q^{gcd(d-1, q-1)}` "as the main term"; when `gcd(d-1, q-1) = 1`
  the mean is exactly `1`; and the variance of the mean is `2 - 1/q`.

  We formalise the refutation at the explicit instance `q = 5`, `d = 2`, where
  `gcd(d - 1, q - 1) = gcd(1, 4) = 1`:

    * the claimed main term is `1 + (5 - 1) / 5^1 = 9/5`, which is not `1`;
    * the exact mean, obtained by enumerating all `5 * 5` pairs `(a, b)` in
      `Fin 5` and all `x` in `Fin 5`, is exactly `1` (count `25` triples out of
      `5 * 5 = 25` choices of `(a, b)`);
    * hence the conjecture asserts at once that the mean is `9/5` and that it is
      `1`, a contradiction;
    * the arithmetic of the second moment (`2 - 1/5 = 9/5`) and variance
      (`2 - 1/5 - 1 = 1 - 1/5`) is recorded for context.

  The file uses CORE LEAN ONLY (`import Std`); it does not use Mathlib, `Finset`,
  `ZMod`, `norm_num`, `linarith`, `omega`, or `sorry`.

  ENCODING NOTES (pitfalls of this Lean version):
    * `List.product` does not exist in core, so the triple enumeration is a
      hand-written double `List.foldl`/`List.map` (`triplesBelow`). A value
      `a < q` is the same as `a : Fin q`, so `List.range q` enumerates `Fin q`.
    * Core `Rat` operations (`Rat.add`, `Rat.sub`, `Rat.mul`, `Rat.inv`) are
      `@[irreducible]`, hence `by decide` cannot see through them. Closed
      rational values are therefore built with the primitive `mkRat`, which
      *does* reduce, and closed comparisons between `mkRat` numerals are decided
      directly. Rational identities that genuinely need `+`/`-` are proven by
      `Rat.ext` together with `Rat.add_def`/`Rat.sub_def`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1097

/-! ### Counting roots of `x^d + a*x + b` over `Fin q` -/

/-- `isRoot q d a b x` is `true` exactly when `x^d + a*x + b ≡ 0 (mod q)`.
For prime `q` this is the vanishing of the trinomial at `x` in `F_q`. -/
def isRoot (q d a b x : Nat) : Bool :=
  (x ^ d + a * x + b) % q == 0

/-- `triplesBelow q` enumerates all triples `(a, b, x)` with `a, b, x < q`
(equivalently, all triples in `Fin q × Fin q × Fin q`), using only core
`List` operations. -/
def triplesBelow (q : Nat) : List (Nat × Nat × Nat) :=
  (List.range q).foldl (fun acc a =>
    acc ++ (List.range q).foldl (fun acc b =>
      acc ++ (List.range q).map (fun x => (a, b, x))) []) []

/-- `rootTripleCount q d` is the number of triples `(a, b, x)` with
`a, b, x ∈ Fin q` and `x^d + a*x + b = 0` in `F_q`. The reduction modulo `q`
matches the field computation for prime `q`. -/
def rootTripleCount (q d : Nat) : Nat :=
  (triplesBelow q).filter (fun (a, b, x) => isRoot q d a b x) |>.length

/-- The exact mean root count as a rational `#triples / q^2`, built with the
reducing constructor `mkRat`. -/
def meanRootCount (q d : Nat) : Rat :=
  mkRat (rootTripleCount q d : Int) (q * q)

/-- There are exactly `25` triples `(a, b, x) ∈ Fin 5 × Fin 5 × Fin 5` with
`x^2 + a*x + b = 0 (mod 5)`. -/
theorem rootTripleCount_5_2 : rootTripleCount 5 2 = 25 := by decide

/-- For each fixed `(a, b)` there is exactly one `x`, so `25` choices of `(a, b)`
give `25` triples: `#triples = 5 * 5`, i.e. the mean is `1`. -/
theorem mean_5_2 : rootTripleCount 5 2 = 5 * 5 := by decide

/-- The exact mean at `q = 5`, `d = 2` is `1`. -/
theorem meanRootCount_5_2 : meanRootCount 5 2 = 1 := by decide

/-! ### The claimed main term -/

/-- `gcdB a b` is the largest `k ≤ min a b` dividing both `a` and `b`, computed by
a bounded search over `List.range (min a b + 1)`. It agrees with `Nat.gcd` on the
instances used here and is a closed computable expression (no well-founded
recursion), so `decide` can evaluate it. -/
def gcdB (a b : Nat) : Nat :=
  ((List.range (Nat.min a b + 1)).filter
    (fun k => decide (k ∣ a) && decide (k ∣ b))).foldl Nat.max 0

/-- `gcd(1, 4) = 1`, the exponent appearing at `q = 5`, `d = 2`. -/
theorem gcdB_1_4 : gcdB 1 4 = 1 := by decide

/-- The conjectured exponent `gcd(d - 1, q - 1)`, using the bounded `gcdB`. -/
def claimedExponent (q d : Nat) : Nat := gcdB (d - 1) (q - 1)

/-- At `q = 5`, `d = 2` the conjectured exponent is `gcd(1, 4) = 1`. -/
theorem claimedExponent_5_2 : claimedExponent 5 2 = 1 := by decide

/-- The conjecture's claimed value `1 + (q - 1) / q^{gcd(d-1, q-1)}`, written as
the exact fraction `(q^{e} + q - 1) / q^{e}` with `mkRat` for reducibility. -/
def claimedMainTerm (q d : Nat) : Rat :=
  mkRat ((q : Int) ^ claimedExponent q d + (q : Int) - 1)
    (q ^ claimedExponent q d)

/-- The claimed main term at `q = 5`, `d = 2` is `1 + 4/5 = 9/5`. -/
theorem claimed_main_term_at_5_2 :
    (1 : Rat) + mkRat 4 5 = mkRat 9 5 := by
  apply Rat.ext
  · rw [Rat.add_def]
    simp only [Rat.num_mkRat, Rat.den_mkRat, Rat.num_ofNat, Rat.den_ofNat]
    decide
  · rw [Rat.add_def]
    simp only [Rat.num_mkRat, Rat.den_mkRat, Rat.num_ofNat, Rat.den_ofNat]
    decide

/-- The same statement through the definition `claimedMainTerm`. -/
theorem claimedMainTerm_5_2 : claimedMainTerm 5 2 = mkRat 9 5 := by decide

/-! ### The internal contradiction -/

/-- The claimed value `1 + 4/5` is not `1`, while the exact mean at `q = 5`,
`d = 2` is `1` (theorem `meanRootCount_5_2`); the conjecture asserts both. -/
theorem contradiction : ¬ ((1 : Rat) = claimedMainTerm 5 2) := by decide

/-! ### The variance clause -/

/-- The exact second moment at `q = 5` is `2 - 1/5 = (2*5 - 1)/5 = 9/5`. -/
def secondMoment (q : Nat) : Rat := mkRat (2 * q - 1) q

/-- Since the mean is `1`, the variance is the second moment minus `1`, i.e.
`(q - 1)/q`; at `q = 5` this is `4/5`, not the claimed `9/5`. -/
def varianceValue (q : Nat) : Rat := mkRat (q - 1) q

/-- The exact second moment at `q = 5` is `9/5`. -/
theorem second_moment_5 : secondMoment 5 = mkRat 9 5 := by decide

/-- Since the mean is `1`, the variance at `q = 5` is the second moment minus
`1`, i.e. `9/5 - 1 = 4/5`, not the claimed `9/5`. -/
theorem variance_5 : secondMoment 5 - 1 = varianceValue 5 := by
  rw [show secondMoment 5 = mkRat 9 5 by decide,
      show varianceValue 5 = mkRat 4 5 by decide]
  apply Rat.ext
  · rw [Rat.sub_def]
    simp only [Rat.num_mkRat, Rat.den_mkRat, Rat.num_ofNat, Rat.den_ofNat]
    decide
  · rw [Rat.sub_def]
    simp only [Rat.num_mkRat, Rat.den_mkRat, Rat.num_ofNat, Rat.den_ofNat]
    decide

/-! ### The disproof -/

/-- The exact mean at `q = 5`, `d = 2` is `1`, while the conjecture's claimed main
term there is `9/5 ≠ 1`: the conjecture is false as stated. -/
theorem conjecture_00000001097_false :
    rootTripleCount 5 2 = 25 ∧
      meanRootCount 5 2 = 1 ∧
      claimedMainTerm 5 2 = mkRat 9 5 ∧
      ¬ ((1 : Rat) = claimedMainTerm 5 2) :=
  ⟨rootTripleCount_5_2, meanRootCount_5_2, claimedMainTerm_5_2, contradiction⟩

end Tlmc1097
