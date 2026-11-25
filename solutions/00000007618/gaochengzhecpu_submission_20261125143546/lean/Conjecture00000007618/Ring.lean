/-
  Conjecture 00000007618 — Commutative Ring Foundations & Modular Parity Arithmetic
  Core Lean 4.19.0 only (zero external dependencies).

  Provides:
    1. Minimal commutative ring typeclass `CRing R` and complete `Int` instance;
    2. Parity sign homomorphism `ringParitySign : Nat → R` (`(-1)^m`) and `paritySign : Nat → Int`;
    3. Exact modular parity laws governing projective subspace dimensions, codimensions,
       and the double-star intersection exponent `k(n - k) ≡ (r + s)(n - 1) (mod 2)`.
-/

namespace Conjecture00000007618

/-- Minimal commutative unital ring interface in Core Lean 4. -/
class CRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

namespace CRing

section RingLemmas
variable {R : Type} [CRing R]

theorem add_zero (a : R) : add a zero = a := by
  rw [add_comm, zero_add]

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem mul_one (a : R) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem right_distrib (a b c : R) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : add a b = zero) : b = neg a := by
  apply add_left_cancel (a := a)
  rw [h, add_right_neg]

theorem neg_zero : neg (zero : R) = zero := by
  symm
  exact neg_eq_of_add_eq_zero (zero_add zero)

theorem neg_neg (a : R) : neg (neg a) = a := by
  symm
  exact neg_eq_of_add_eq_zero (add_left_neg a)

theorem neg_add (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← add_assoc, add_assoc a b (neg a), add_comm b (neg a), ← add_assoc a (neg a) b,
      add_right_neg, zero_add, add_right_neg]

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_right_neg, mul_zero]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

/-- Sign `(-1)^m` in any commutative ring `R`. -/
def ringParitySign (m : Nat) : R :=
  if m % 2 = 0 then one else neg one

theorem ringParitySign_of_mod_eq {a b : Nat} (h : a % 2 = b % 2) :
    ringParitySign (R := R) a = ringParitySign (R := R) b := by
  unfold ringParitySign
  rw [h]

theorem ringParitySign_even {m : Nat} (h : m % 2 = 0) :
    ringParitySign (R := R) m = one := by
  unfold ringParitySign
  rw [if_pos h]

theorem ringParitySign_odd {m : Nat} (h : m % 2 = 1) :
    ringParitySign (R := R) m = neg one := by
  unfold ringParitySign
  have hne : m % 2 ≠ 0 := by omega
  rw [if_neg hne]

theorem ringParitySign_add (a b : Nat) :
    ringParitySign (R := R) (a + b) = mul (ringParitySign (R := R) a) (ringParitySign (R := R) b) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · have hab : (a + b) % 2 = 0 := by omega
    rw [ringParitySign_even ha0, ringParitySign_even hb0, ringParitySign_even hab, one_mul]
  · have hab : (a + b) % 2 = 1 := by omega
    rw [ringParitySign_even ha0, ringParitySign_odd hb1, ringParitySign_odd hab, one_mul]
  · have hab : (a + b) % 2 = 1 := by omega
    rw [ringParitySign_odd ha1, ringParitySign_even hb0, ringParitySign_odd hab, mul_one]
  · have hab : (a + b) % 2 = 0 := by omega
    rw [ringParitySign_odd ha1, ringParitySign_odd hb1, ringParitySign_even hab,
        neg_mul_neg, one_mul]

theorem ringParitySign_sq (m : Nat) :
    mul (ringParitySign (R := R) m) (ringParitySign (R := R) m) = one := by
  rw [← ringParitySign_add]
  apply ringParitySign_even
  omega

end RingLemmas

end CRing

/-! ### Complete `CRing Int` Instance -/

instance instCRingInt : CRing Int where
  zero := 0
  one := 1
  add := Int.add
  neg := Int.neg
  mul := Int.mul
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

/-- Integer parity sign `(-1)^m ∈ {+1, -1}`. -/
def paritySign (m : Nat) : Int :=
  CRing.ringParitySign (R := Int) m

theorem paritySign_eq_one_or_neg_one (m : Nat) :
    paritySign m = 1 ∨ paritySign m = -1 := by
  unfold paritySign CRing.ringParitySign
  by_cases h : m % 2 = 0
  · rw [if_pos h]; exact Or.inl rfl
  · rw [if_neg h]; exact Or.inr rfl

theorem int_one_ne_neg_one : (1 : Int) ≠ (-1 : Int) := by
  decide

/-! ### Exact Modular Parity Laws for Projective Dimensions & Double-Star Exponents -/

theorem nat_mul_mod_two (a b : Nat) : (a * b) % 2 = ((a % 2) * (b % 2)) % 2 :=
  Nat.mul_mod a b 2

/-- Universal Dimension-Sum Parity Equivalence:
    1. Projective flat dimension sum `(r - 1) + (s - 1)` has the same parity as `r + s` (`r, s ≥ 1`);
    2. Subspace codimension sum `(n - r) + (n - s)` has the same parity as `r + s` (`r, s ≤ n`). -/
theorem proj_dim_sum_mod_two {r s : Nat} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((r - 1) + (s - 1)) % 2 = (r + s) % 2 := by
  omega

theorem codim_sum_mod_two {n r s : Nat} (hr : r ≤ n) (hs : s ≤ n) :
    ((n - r) + (n - s)) % 2 = (r + s) % 2 := by
  omega

/-- For every `n, k : Nat` with `k ≤ n`:
      `(k * (n - k)) % 2 = (k * (n - 1)) % 2`. -/
theorem k_mul_n_sub_k_mod_two {n k : Nat} (hk : k ≤ n) :
    (k * (n - k)) % 2 = (k * (n - 1)) % 2 := by
  rw [nat_mul_mod_two k (n - k), nat_mul_mod_two k (n - 1)]
  have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hn2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hk2 with hk0 | hk1 <;> rcases hn2 with hn0 | hn1
  · rw [hk0]; simp
  · rw [hk0]; simp
  · have hnk : (n - k) % 2 = 1 := by omega
    have hn1' : (n - 1) % 2 = 1 := by omega
    rw [hk1, hnk, hn1']
  · have hnk : (n - k) % 2 = 0 := by omega
    have hn1' : (n - 1) % 2 = 0 := by omega
    rw [hk1, hnk, hn1']

/-- Master Parity Reduction for the Forward Three-Star Intersection Exponent:
    For `r ≤ n`, `s ≤ n`, `n ≤ r + s`, and `k = r + s - n`:
      `(k * (n - k)) % 2 = ((r + s) * (n - 1)) % 2`. -/
theorem intersection_double_star_mod_two {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s) :
    ((r + s - n) * (n - (r + s - n))) % 2 = ((r + s) * (n - 1)) % 2 := by
  have hk_le : r + s - n ≤ n := by omega
  rw [k_mul_n_sub_k_mod_two hk_le]
  rw [nat_mul_mod_two (r + s - n) (n - 1), nat_mul_mod_two (r + s) (n - 1)]
  have hn2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn2 with hn0 | hn1
  · have hsub : (r + s - n) % 2 = (r + s) % 2 := by omega
    rw [hsub]
  · have hn1_mod : (n - 1) % 2 = 0 := by omega
    rw [hn1_mod]; simp

/-- Even Ambient Vector Dimension (`n = 2m`, `m ≥ 1`, i.e., `ℙ^{2m-1}`):
    the double-star intersection exponent reduces modulo 2 to the dimension sum `r + s`. -/
theorem even_dim_intersection_mod_two {m r s : Nat}
    (hm : 1 ≤ m) (hr : r ≤ 2 * m) (hs : s ≤ 2 * m) (hrs : 2 * m ≤ r + s) :
    ((r + s - 2 * m) * (2 * m - (r + s - 2 * m))) % 2 = (r + s) % 2 := by
  rw [intersection_double_star_mod_two hr hs hrs]
  rw [nat_mul_mod_two (r + s) (2 * m - 1)]
  have hodd : (2 * m - 1) % 2 = 1 := by omega
  rw [hodd]
  omega

/-- Odd Ambient Vector Dimension (`n = 2m + 1`, i.e., `ℙ^{2m}`):
    the double-star intersection exponent is ALWAYS EVEN (`0 mod 2`), independent of `r, s`. -/
theorem odd_dim_intersection_mod_two_zero {m r s : Nat}
    (hr : r ≤ 2 * m + 1) (hs : s ≤ 2 * m + 1) (hrs : 2 * m + 1 ≤ r + s) :
    ((r + s - (2 * m + 1)) * ((2 * m + 1) - (r + s - (2 * m + 1)))) % 2 = 0 := by
  rw [intersection_double_star_mod_two hr hs hrs]
  have hsub : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hsub, nat_mul_mod_two (r + s) (2 * m)]
  have heven : (2 * m) % 2 = 0 := by omega
  rw [heven]
  simp

end Conjecture00000007618
