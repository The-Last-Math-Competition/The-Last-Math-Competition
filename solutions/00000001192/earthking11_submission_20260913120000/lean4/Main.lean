/-
  Disproof of conjecture `00000001192`.

  Conjecture (as filed): with `c(n, q)` the number of subgroups of `GL_n(F_q)`
  whose order equals that of the commutator (derived) subgroup,

      c(n, q) is an integer-coefficient polynomial in `q` of degree `n² − n`
      with leading coefficient `(n! · n^n)^{-1} · ∏_{p | n} p`.

  This file formalises the *arithmetic obstruction* to the stated leading
  coefficient.  Write

      LC(n) = (∏_{p | n} p) / (n! · n^n).

  The conjecture asserts that `c(n, q)` is a polynomial with **integer
  coefficients** of degree `d = n² − n ≥ 2`.  Any integer-coefficient polynomial
  has an integer leading coefficient: it is the (integer) coefficient of `q^d`.
  But `LC(n)` is a non-integer rational for every `n ≥ 2`:

      LC(2) = 2 / 8   = 1/4,
      LC(3) = 3 / 162 = 1/54,
      LC(4) = 2 / 6144 = 1/3072,
      LC(6) = 6 / 33592320 = 1/5598720.

  The numerator is always `1` after reduction (the radical `∏_{p|n} p` divides
  `n`, hence `n^n`, hence `n! · n^n`), while the denominator exceeds `1`.  So the
  claimed leading coefficient is not an integer, and no integer-coefficient
  polynomial of that degree has it.  Contradiction.

  The charitable reading "integer-VALUED" (rather than integer-coefficient) also
  fails: an integer-valued polynomial of degree `d` has `d! · (leading
  coefficient) ∈ Z`.  For `n = 2` (`d = 2`) we get `2! · 1/4 = 1/2 ∉ Z`, and for
  `n = 3` (`d = 6`) we get `6! · 1/54 = 720/54 = 40/3 ∉ Z`.  Thus the ambiguity
  does not rescue the conjecture at its two smallest cases.

  Scope note.  The conjecture concerns a quantity (`c(n,q)`) that this
  submission does not otherwise analyse.  The refutation is purely about the
  *stated kind of polynomial* (integer-coefficient, degree `n² − n`) and the
  *stated leading coefficient* `LC(n)`: those two assertions are mutually
  inconsistent, independently of any group theory.  If the author intended a
  PORC constituent indexed by `q = p^f`, or a different normalisation, the text
  as written is still self-inconsistent, because the coefficient is not an
  integer.

  Everything is over `Nat`/`Int`; the rational numbers `1/4`, `1/54`, `1/3072`
  are represented by the pair `(lcNum n, lcDen n)` of a reduced numerator and
  denominator.  Non-integrality is stated as the corresponding divisibility
  obstruction, e.g. `¬ ∃ a : Int, 4 * a = 1` is the arithmetic content of
  "`1/4` is not an integer".  Core Lean only (`import Std`), no Mathlib, no
  `sorry`, no `axiom`, no `native_decide`.
-/

import Std

set_option maxRecDepth 100000

namespace Tlmc1192

/-! ## Prime divisors of `n` -/

/-- `isPrimeB n` is `true` exactly when `n` is prime, decided by bounded trial
division over `List.range n` (the candidates `0, …, n-1`). -/
def isPrimeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

/-- `prodPrimeDiv n = ∏_{p | n} p`, computed by filtering the primes in
`0, …, n` that divide `n` and multiplying them. -/
def prodPrimeDiv (n : Nat) : Nat :=
  ((List.range (n + 1)).filter
    (fun p => isPrimeB p && decide (p ∣ n))).foldr (fun a b => a * b) 1

theorem prodPrimeDiv_two : prodPrimeDiv 2 = 2 := by decide
theorem prodPrimeDiv_three : prodPrimeDiv 3 = 3 := by decide
theorem prodPrimeDiv_four : prodPrimeDiv 4 = 2 := by decide
theorem prodPrimeDiv_six : prodPrimeDiv 6 = 6 := by decide

/-- `factN n = n!`, defined by structural recursion so that the kernel can
reduce it on numerals (core Lean has no `Nat.factorial`). -/
def factN : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factN n

/-- A computable greatest common divisor, as the maximum of the common divisors
of `a` and `b` in `0, …, min a b`.  Defined by a bounded list fold so that the
kernel can reduce it on numerals (`Nat.gcd` is opaque to `decide` here). -/
def gcdN (a b : Nat) : Nat :=
  ((List.range (Nat.min a b + 1)).filter
    (fun d => decide (d ∣ a ∧ d ∣ b))).foldr Nat.max 0

theorem factN_two : factN 2 = 2 := by decide
theorem factN_six : factN 6 = 720 := by decide

/-! ## The claimed leading coefficient as a reduced pair `(lcNum, lcDen)` -/

/-- The common factor of the claimed numerator `∏_{p|n} p` and denominator
`n! · n^n`.  One has `lcNum n / lcDen n = LC(n)` in lowest terms. -/
def lcGcd (n : Nat) : Nat :=
  gcdN (prodPrimeDiv n) (factN n * n ^ n)

/-- Reduced numerator of `LC(n) = (∏_{p|n} p) / (n! · n^n)`. -/
def lcNum (n : Nat) : Nat := prodPrimeDiv n / lcGcd n

/-- Reduced denominator of `LC(n) = (∏_{p|n} p) / (n! · n^n)`. -/
def lcDen (n : Nat) : Nat := (factN n * n ^ n) / lcGcd n

/-- `LC(2) = 1/4`. -/
theorem lc_two : lcNum 2 = 1 ∧ lcDen 2 = 4 := by decide

/-- `LC(3) = 1/54`. -/
theorem lc_three : lcNum 3 = 1 ∧ lcDen 3 = 54 := by decide

/-- `LC(4) = 1/3072`. -/
theorem lc_four : lcNum 4 = 1 ∧ lcDen 4 = 3072 := by decide

/-- `LC(6) = 1/5598720`. -/
theorem lc_six : lcNum 6 = 1 ∧ lcDen 6 = 5598720 := by decide

/-- Raw numerator/denominator form before reduction, for completeness:
`LC(2) = 2 / (2! · 2^2) = 2/8`. -/
theorem lc_raw_two : prodPrimeDiv 2 = 2 ∧ factN 2 * 2 ^ 2 = 8 := by decide

/-! ## Non-integrality of the claimed leading coefficient

`LC(n)` is an integer iff `lcDen n ∣ lcNum n`.  The following facts record that
this divisibility fails, phrased as the non-existence of an integer solution. -/

/-- The arithmetic content of "`LC(2) = 1/4` is not an integer": there is no
natural `m` with `m * 4 = 1`. -/
theorem lc2_not_integer : ¬ ∃ m : Nat, m * 4 = 1 := by
  rintro ⟨m, hm⟩
  have hdvd : (4 : Nat) ∣ 1 := ⟨m, by rw [Nat.mul_comm 4 m]; exact hm.symm⟩
  exact (by decide : ¬ (4 : Nat) ∣ 1) hdvd

/-- The arithmetic content of "`LC(3) = 1/54` is not an integer": there is no
natural `m` with `m * 54 = 1`. -/
theorem lc3_not_integer : ¬ ∃ m : Nat, m * 54 = 1 := by
  rintro ⟨m, hm⟩
  have hdvd : (54 : Nat) ∣ 1 := ⟨m, by rw [Nat.mul_comm 54 m]; exact hm.symm⟩
  exact (by decide : ¬ (54 : Nat) ∣ 1) hdvd

/-- The arithmetic content of "`LC(4) = 1/3072` is not an integer". -/
theorem lc4_not_integer : ¬ ∃ m : Nat, m * 3072 = 1 := by
  rintro ⟨m, hm⟩
  have hdvd : (3072 : Nat) ∣ 1 := ⟨m, by rw [Nat.mul_comm 3072 m]; exact hm.symm⟩
  exact (by decide : ¬ (3072 : Nat) ∣ 1) hdvd

/-- `LC(2) = 1/4` is not an integer, in `Int` phrasing: there is no integer `a`
with `4 * a = 1`.  This is the form used in the integer-coefficient argument,
where the leading coefficient of an integer-coefficient polynomial would be an
integer. -/
theorem no_integer_poly_has_lc_two : ¬ ∃ a : Int, (4 : Int) * a = 1 := by
  rintro ⟨a, ha⟩
  have h : ((4 : Int) * a).natAbs = (1 : Int).natAbs := congrArg Int.natAbs ha
  simp only [Int.natAbs_mul] at h
  have h2 : a.natAbs * 4 = 1 := by
    rw [show ((4 : Int).natAbs) = 4 from rfl, show ((1 : Int).natAbs) = 1 from rfl] at h
    rw [Nat.mul_comm] at h
    exact h
  exact lc2_not_integer ⟨a.natAbs, h2⟩

/-! ## The integer-valued reading also fails

An integer-valued polynomial of degree `d` has `d! · (leading coefficient) ∈ Z`.
For the stated degree `d = n² − n` and `LC(n) = 1/(n! · n^n / gcd)`, the product
`d! · LC(n)` is an integer only if `lcDen n ∣ d! · lcNum n`.  At `n = 2`
(`d = 2`) this asks for `2 / 4 = 1/2`, and at `n = 3` (`d = 6`) for
`720 / 54 = 40/3`; both are non-integers. -/

/-- `d! · LC(2) = 2! · 1/4 = 1/2` is not an integer. -/
theorem lc2_times_two_not_integer : ¬ ∃ m : Nat, m * 2 = 1 := by
  rintro ⟨m, hm⟩
  have hdvd : (2 : Nat) ∣ 1 := ⟨m, by rw [Nat.mul_comm 2 m]; exact hm.symm⟩
  exact (by decide : ¬ (2 : Nat) ∣ 1) hdvd

/-- Raw form of the same fact over the unreduced denominator:
`¬ ∃ m, m * 4 = 2! * 1 = 2`. -/
theorem lc2_degree_factorial_times_lc_not_integer : ¬ ∃ m : Nat, m * 4 = 2 := by
  rintro ⟨m, hm⟩
  have hdvd : (4 : Nat) ∣ 2 := ⟨m, by rw [Nat.mul_comm 4 m]; exact hm.symm⟩
  exact (by decide : ¬ (4 : Nat) ∣ 2) hdvd

/-- `d! · LC(3) = 6! · 1/54 = 720/54 = 40/3` is not an integer, in raw form
`¬ ∃ m, m * 54 = 720`. -/
theorem lc3_degree_factorial_times_lc_not_integer : ¬ ∃ m : Nat, m * 54 = 720 := by
  rintro ⟨m, hm⟩
  have hdvd : (54 : Nat) ∣ 720 := ⟨m, by rw [Nat.mul_comm 54 m]; exact hm.symm⟩
  exact (by decide : ¬ (54 : Nat) ∣ 720) hdvd

/-- The reduced form `¬ ∃ m, m * 3 = 40` of the `n = 3` integer-valued failure
(`720/54 = 40/3`). -/
theorem lc3_degree_factorial_times_lc_not_integer_reduced : ¬ ∃ m : Nat, m * 3 = 40 := by
  rintro ⟨m, hm⟩
  have hdvd : (3 : Nat) ∣ 40 := ⟨m, by rw [Nat.mul_comm 3 m]; exact hm.symm⟩
  exact (by decide : ¬ (3 : Nat) ∣ 40) hdvd

/-! ## The collected disproof -/

/-- The stated leading coefficient is a non-integer rational for `n = 2, 3, 4`
(the three smallest cases with `n² − n ≥ 2`), and neither the integer-coefficient
reading nor the integer-valued reading can accommodate it.  Conjecture
`00000001192` is therefore FALSE as stated. -/
theorem conjecture_00000001192_false :
    lcNum 2 = 1 ∧ lcDen 2 = 4 ∧
    lcNum 3 = 1 ∧ lcDen 3 = 54 ∧
    lcNum 4 = 1 ∧ lcDen 4 = 3072 ∧
    (¬ ∃ m : Nat, m * 4 = 1) ∧
    (¬ ∃ m : Nat, m * 54 = 1) ∧
    (¬ ∃ a : Int, (4 : Int) * a = 1) ∧
    (¬ ∃ m : Nat, m * 2 = 1) ∧
    (¬ ∃ m : Nat, m * 54 = 720) :=
  ⟨lc_two.1, lc_two.2, lc_three.1, lc_three.2, lc_four.1, lc_four.2,
   lc2_not_integer, lc3_not_integer, no_integer_poly_has_lc_two,
   lc2_times_two_not_integer, lc3_degree_factorial_times_lc_not_integer⟩

end Tlmc1192
