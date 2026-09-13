/-
  Disproof of conjecture `00000002048`: formalisation.

  Conjecture (as filed, for a prime `p`):

    3A := {x + y + z : x, y, z ∈ A} ⊂ F_p.
    If |A| > (p - 1) / 3 then 3A covers F_p \ {0}, and the threshold is
    optimal (attained critically by the cubic-residue set at the threshold).

  We formalise an unconditional counterexample at the smallest non-trivial
  prime and a general family.

  * Concrete witness:  p = 5,  A = {0, 1} ⊂ F_5.
        |A| = 2 > 4/3 = (5 - 1)/3,  yet  3A = {0, 1, 2, 3}  misses 4 ∈ F_5 \ {0}.
    Hence the conjecture's main claim ("3A ⊇ F_p \ {0}") is false, and the
    "exact threshold" claim fails: |A| = 2 is strictly above (p-1)/3 = 4/3.

  * General family:  for every prime p ≡ 2 (mod 3), the set
        A = {0, 1, …, (p - 2)/3}  has  |A| = (p + 1)/3 > (p - 1)/3,
    and its 3-fold sum misses p - 1: every x, y, z ∈ A satisfies
    x + y + z ≤ 3·((p-2)/3) ≤ p - 2, so x + y + z < p and the residue p - 1 is
    never attained. Cauchy–Davenport only gives |3A| ≥ min(p, 3|A| - 2) = p - 1
    at this size, so it does not force coverage either.

  The file uses CORE LEAN ONLY (`import Std`); no Mathlib, `Finset`, `ZMod`,
  `Matrix`, or `sorry`. Residues are plain `Nat`s reduced with `% p`, and the
  finite computations are closed by `decide`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc2048

/-! ## The 3-fold sum -/

/-- `inSum3 p A s` is true exactly when `s` is a residue of the form
`x + y + z (mod p)` with `x, y, z ∈ A`. -/
def inSum3 (p : Nat) (A : List Nat) (s : Nat) : Bool :=
  A.any fun x => A.any fun y => A.any fun z => ((x + y + z) % p == s)

/-- The 3-fold sum `3A = {x + y + z mod p : x, y, z ∈ A}`, as the sorted list
of residues in `{0, …, p-1}` that it contains. -/
def sum3 (p : Nat) (A : List Nat) : List Nat :=
  (List.range p).filter fun s => inSum3 p A s

/-- The conjecture's claim at `(p, A)`: `3A` covers every nonzero residue,
i.e. `F_p \ {0} = {1, …, p-1} ⊆ 3A`. -/
def coversNonzero (p : Nat) (A : List Nat) : Bool :=
  ((List.range (p - 1)).map (fun k => k + 1)).all fun s => inSum3 p A s

/-- Bounded trial-division primality test. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all fun d => decide (d < 2 ∨ n % d ≠ 0)

/-! ## The concrete counterexample: `p = 5`, `A = {0, 1}` -/

/-- The witness set `A = {0, 1} ⊂ F_5`. -/
def witnessA : List Nat := [0, 1]

/-- `3A = {0, 1, 2, 3}`: the 3-fold sum of `{0,1}` in `F_5` is exactly the
interval `{0, 1, 2, 3}`. -/
theorem witness_sum3 : sum3 5 witnessA = [0, 1, 2, 3] := by decide

/-- `3A = {0, 1, 2, 3} = List.range 4`, so the only residue it misses is `4`. -/
theorem witness_sum3_eq_range : sum3 5 witnessA = List.range 4 := by decide

/-- The missing residue `4` is nonzero in `F_5`. -/
theorem witness_four_nonzero : (4 % 5) ≠ 0 := by decide

/-- `4 ∉ 3A`, the heart of the counterexample. -/
theorem witness_misses_four : (sum3 5 witnessA).contains 4 = false := by decide

/-- Equivalently, `4` is not a sum of three elements of `A` modulo `5`. -/
theorem witness_inSum3_four : inSum3 5 witnessA 4 = false := by decide

/-- `|A| = 2`. -/
theorem witness_card : witnessA.length = 2 := by decide

/-- The size hypothesis of the conjecture holds strictly: `|A| = 2 > 4/3`,
written without division as `3·|A| > p - 1`, i.e. `6 > 4`. -/
theorem witness_threshold : 3 * witnessA.length > 5 - 1 := by decide

/-- The conjecture's claim `3A ⊇ F_5 \ {0}` fails at `p = 5`, `A = {0,1}`. -/
theorem conjecture_00000002048_false : coversNonzero 5 witnessA = false := by decide

/-- The negation form of the counterexample. -/
theorem conjecture_00000002048_not_holds :
    ¬ (coversNonzero 5 witnessA = true) := by decide

/-- The counterexample package: `p = 5`, `A = {0,1}` has `|A| = 2 > 4/3`,
`3A = {0,1,2,3}`, misses the nonzero residue `4`, and therefore does not cover
`F_5 \ {0}`. This is a direct disproof of conjecture `00000002048`. -/
theorem witness_refutes_conjecture :
    sum3 5 witnessA = [0, 1, 2, 3] ∧ witnessA.length = 2 ∧
    3 * witnessA.length > 5 - 1 ∧ (sum3 5 witnessA).contains 4 = false ∧
    coversNonzero 5 witnessA = false :=
  ⟨witness_sum3, witness_card, witness_threshold, witness_misses_four,
    conjecture_00000002048_false⟩

/-! ## The general family: `p ≡ 2 (mod 3)`, `A = {0, …, (p-2)/3}` -/

/-- The general-family set `A = {0, 1, …, (p - 2)/3}` as a list. -/
def familyA (p : Nat) : List Nat := List.range ((p - 2) / 3 + 1)

/-- Key mechanism: no sum of three elements of `familyA p` is congruent to
`p - 1` modulo `p`. Indeed each element is at most `(p-2)/3`, so the sum is at
most `3·((p-2)/3) ≤ p - 2 < p`; the residue is the sum itself and it is
`≤ p - 2 < p - 1`. -/
theorem family_misses_pred (p : Nat) (hp : 2 ≤ p) :
    inSum3 p (familyA p) (p - 1) = false := by
  rw [inSum3, familyA]
  apply List.any_eq_false.mpr
  intro x hx
  rw [Bool.not_eq_true]
  apply List.any_eq_false.mpr
  intro y hy
  rw [Bool.not_eq_true]
  apply List.any_eq_false.mpr
  intro z hz
  rw [Bool.not_eq_true]
  have hx' : x ≤ (p - 2) / 3 := Nat.lt_succ_iff.mp (List.mem_range.mp hx)
  have hy' : y ≤ (p - 2) / 3 := Nat.lt_succ_iff.mp (List.mem_range.mp hy)
  have hz' : z ≤ (p - 2) / 3 := Nat.lt_succ_iff.mp (List.mem_range.mp hz)
  have hdiv : 3 * ((p - 2) / 3) ≤ p - 2 := by
    have := Nat.div_mul_le_self (p - 2) 3
    omega
  have hsum : x + y + z ≤ p - 2 := by omega
  have hmod : (x + y + z) % p = x + y + z :=
    Nat.mod_eq_of_lt (by omega)
  have hne : x + y + z ≠ p - 1 := by omega
  simp only [hmod]
  exact beq_eq_false_iff_ne.mpr hne

/-- The general family never covers `F_p \ {0}`: the nonzero residue `p - 1` is
missing from the 3-fold sum. -/
theorem family_not_cover (p : Nat) (hp : 2 ≤ p) :
    coversNonzero p (familyA p) = false := by
  rw [coversNonzero, List.all_eq_false]
  refine ⟨p - 1, ?_, ?_⟩
  · rw [List.mem_map]
    refine ⟨p - 2, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega
  · rw [Bool.not_eq_true]
    exact family_misses_pred p hp

/-- At the general-family size, the hypothesis `|A| > (p-1)/3` holds:
`3·|A| > p - 1` whenever `p ≡ 2 (mod 3)`. Indeed `3·|A| = p + 1`. -/
theorem family_threshold (p : Nat) (hp : p % 3 = 2) :
    3 * (familyA p).length > p - 1 := by
  rw [familyA, List.length_range]
  omega

/-- Cauchy–Davenport at the threshold. For a prime `p ≡ 2 (mod 3)`, the
general-family size is `ℓ = (p+1)/3`, and the lower bound
`|3A| ≥ min(p, 3ℓ - 2)` evaluates to exactly `p - 1`: the bound is too weak to
force `|3A| = p`, which is consistent with the counterexample. -/
theorem cauchy_davenport_at_threshold (p : Nat) (hp : p % 3 = 2) :
    min p (3 * ((p + 1) / 3) - 2) = p - 1 := by
  omega

/-- The general family refutes the conjecture whenever `p ≡ 2 (mod 3)`,
`p ≥ 2`: the size hypothesis is satisfied but `F_p \ {0}` is not covered. -/
theorem general_family_refutes (p : Nat) (hp2 : 2 ≤ p) (hp3 : p % 3 = 2) :
    3 * (familyA p).length > p - 1 ∧ coversNonzero p (familyA p) = false :=
  ⟨family_threshold p hp3, family_not_cover p hp2⟩

/-! ## The listed prime instances `p = 5, 11, …, 89` -/

/-- The primes `p ≡ 2 (mod 3)` for which the family was checked. -/
def familyPrimes : List Nat :=
  [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89]

/-- Every listed prime is prime by the bounded test. -/
theorem family_primes_prime : familyPrimes.all primeB = true := by decide

/-- Every listed prime satisfies `p ≡ 2 (mod 3)`. -/
theorem family_primes_mod : familyPrimes.all (fun p => p % 3 == 2) = true := by
  decide

/-- The machine check for the listed primes: each is prime, each is `2 mod 3`,
each satisfies the size hypothesis `3·|A| > p - 1`, and for each the residue
`p - 1` is missing from the 3-fold sum. (Full non-coverage follows for all
`p ≥ 2` from `family_not_cover`.) -/
def familyCheck : Bool :=
  familyPrimes.all fun p =>
    primeB p && (p % 3 == 2) &&
    decide (3 * (familyA p).length > p - 1) && !(inSum3 p (familyA p) (p - 1))

/-- The check passes for all twelve listed primes, including `p = 5`, `11`,
`17`. -/
theorem general_family_verified : familyCheck = true := by decide

/-- The twelve listed primes, packaged: all are prime, all are `2 mod 3`, and
for each the general family satisfies the conjecture's size hypothesis while
the residue `p - 1` is absent from the 3-fold sum. -/
theorem listed_family_refutes :
    familyPrimes.all primeB = true ∧
    familyPrimes.all (fun p => p % 3 == 2) = true ∧
    familyCheck = true :=
  ⟨family_primes_prime, family_primes_mod, general_family_verified⟩

end Tlmc2048
