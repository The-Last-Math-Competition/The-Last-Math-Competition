/-
  Conjecture 00000007616 — Commutative Ring Foundations & Exact Arithmetic Lemmas
  Core Lean 4.19.0 only (zero external dependencies).
-/

namespace Conjecture00000007616

/-- Lightweight commutative ring typeclass in Core Lean 4. -/
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

section BasicLemmas
variable {R : Type} [CRing R]

theorem add_zero (a : R) : add a zero = a := by
  rw [add_comm, zero_add]

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem mul_one (a : R) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem right_distrib (a b c : R) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : add a c = add b c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_zero : neg (zero (R := R)) = zero := by
  apply add_left_cancel (a := zero)
  rw [add_right_neg, add_zero]

theorem neg_neg (a : R) : neg (neg a) = a := by
  apply add_left_cancel (a := neg a)
  rw [add_right_neg, add_left_neg]

theorem neg_add (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  apply add_left_cancel (a := add a b)
  rw [add_right_neg]
  calc
    zero = add a (add (neg a) zero) := by rw [add_zero, add_right_neg]
    _ = add a (add (neg a) (add b (neg b))) := by rw [add_right_neg]
    _ = add a (add b (add (neg a) (neg b))) := by
          rw [← add_assoc (neg a) b (neg b), add_comm (neg a) b, add_assoc b (neg a) (neg b)]
    _ = add (add a b) (add (neg a) (neg b)) := by rw [add_assoc]

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply add_left_cancel (a := mul a b)
  rw [← left_distrib, add_right_neg, mul_zero, add_right_neg]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem add_add_add_comm (a b c d : R) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, add_assoc, ← add_assoc b c d, add_comm b c, add_assoc c b d]

end BasicLemmas

/-- Canonical `CRing Int` instance using Core Lean 4 `Int` theorems. -/
instance instCRingInt : CRing Int where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

end CRing

/-!
  ### Exact Number-Theoretic Non-Square Lemma (`6` is not a rational square or negative square)
  Used to prove that on the positive-definite rational quadratic space
  `Q(x₁, x₂) = 2x₁² + 3x₂²` over `ℚ`, NO volume blade `(a/b) e₁ ∧ e₂` has
  norm `+1` or `-1`.
-/

/-- Modulo-3 square lemma: if `(b * b) % 3 = 0`, then `b % 3 = 0`. -/
theorem mod3_sq_zero (b : Nat) (h : (b * b) % 3 = 0) : b % 3 = 0 := by
  have hlt : b % 3 < 3 := Nat.mod_lt b (by decide)
  have hmul : (b * b) % 3 = ((b % 3) * (b % 3)) % 3 := Nat.mul_mod b b 3
  rw [hmul] at h
  match hr : b % 3 with
  | 0 => rfl
  | 1 => rw [hr] at h; contradiction
  | 2 => rw [hr] at h; contradiction
  | k + 3 => rw [hr] at hlt; omega

/-- Modulo-3 double-square lemma: if `(2 * (a * a)) % 3 = 0`, then `a % 3 = 0`. -/
theorem mod3_two_mul_sq_zero (a : Nat) (h : (2 * (a * a)) % 3 = 0) : a % 3 = 0 := by
  have hlt : a % 3 < 3 := Nat.mod_lt a (by decide)
  have hmul1 : (2 * (a * a)) % 3 = ((2 % 3) * ((a * a) % 3)) % 3 := Nat.mul_mod 2 (a * a) 3
  have hmul2 : (a * a) % 3 = ((a % 3) * (a % 3)) % 3 := Nat.mul_mod a a 3
  rw [hmul1, hmul2] at h
  match hr : a % 3 with
  | 0 => rfl
  | 1 => rw [hr] at h; contradiction
  | 2 => rw [hr] at h; contradiction
  | k + 3 => rw [hr] at hlt; omega

/-- Modulo-3 infinite descent: if `6 * a² = b²` in `Nat`, then `a = 0` and `b = 0`. -/
theorem nat_six_mul_sq_eq_sq_imp_zero :
    ∀ n : Nat, ∀ a b : Nat, a + b ≤ n → 6 * (a * a) = b * b → a = 0 ∧ b = 0
  | 0, a, b, hle, _ => by
      omega
  | n + 1, a, b, hle, h => by
      by_cases hb0 : b = 0
      · subst hb0
        cases a with
        | zero => exact ⟨rfl, rfl⟩
        | succ k =>
          have hpos : 0 < (k + 1) * (k + 1) := Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos k)
          omega
      · have hmod : (b * b) % 3 = 0 := by
          rw [← h]
          omega
        have hb3 : b % 3 = 0 := mod3_sq_zero b hmod
        let b' := b / 3
        have hb_eq : b = 3 * b' := by
          have := Nat.div_add_mod b 3
          omega
        have h1 : 6 * (a * a) = 9 * (b' * b') := by
          calc
            6 * (a * a) = b * b := h
            _ = (3 * b') * (3 * b') := by rw [hb_eq]
            _ = 9 * (b' * b') := by
                calc
                  (3 * b') * (3 * b') = 3 * (b' * (3 * b')) := Nat.mul_assoc 3 b' (3 * b')
                  _ = 3 * ((3 * b') * b') := by rw [Nat.mul_comm b' (3 * b')]
                  _ = 3 * (3 * (b' * b')) := by rw [Nat.mul_assoc 3 b' b']
                  _ = (3 * 3) * (b' * b') := by rw [← Nat.mul_assoc 3 3 (b' * b')]
                  _ = 9 * (b' * b') := rfl
        have h2 : 2 * (a * a) = 3 * (b' * b') := by omega
        have hamod : (2 * (a * a)) % 3 = 0 := by
          rw [h2]
          omega
        have ha3 : a % 3 = 0 := mod3_two_mul_sq_zero a hamod
        let a' := a / 3
        have ha_eq : a = 3 * a' := by
          have := Nat.div_add_mod a 3
          omega
        have h3 : 18 * (a' * a') = 3 * (b' * b') := by
          have haa : 2 * (a * a) = 18 * (a' * a') := by
            calc
              2 * (a * a) = 2 * ((3 * a') * (3 * a')) := by rw [ha_eq]
              _ = 2 * (3 * (a' * (3 * a'))) := by rw [Nat.mul_assoc 3 a' (3 * a')]
              _ = 2 * (3 * ((3 * a') * a')) := by rw [Nat.mul_comm a' (3 * a')]
              _ = 2 * (3 * (3 * (a' * a'))) := by rw [Nat.mul_assoc 3 a' a']
              _ = 2 * ((3 * 3) * (a' * a')) := by rw [← Nat.mul_assoc 3 3 (a' * a')]
              _ = (2 * (3 * 3)) * (a' * a') := by rw [← Nat.mul_assoc 2 (3 * 3) (a' * a')]
              _ = 18 * (a' * a') := rfl
          rw [← haa]
          exact h2
        have h_desc : 6 * (a' * a') = b' * b' := by omega
        have hle' : a' + b' ≤ n := by omega
        have ⟨ha'0, hb'0⟩ := nat_six_mul_sq_eq_sq_imp_zero n a' b' hle' h_desc
        omega

theorem int_natAbs_mul_self (z : Int) : Int.ofNat (z.natAbs * z.natAbs) = z * z := by
  cases z <;> rfl

/-- For all integers `a, b` with `b ≠ 0`, `6 * a² ≠ b²` and `6 * a² ≠ -b²`.
    Equivalently, over `ℚ`, for every rational `λ = a / b`, `6 * λ² ∉ {1, -1}`. -/
theorem int_six_mul_sq_ne_pm_sq (a b : Int) (hb : b ≠ 0) :
    6 * (a * a) ≠ b * b ∧ 6 * (a * a) ≠ -(b * b) := by
  constructor
  · intro heq
    have hnat_int : Int.ofNat (6 * (a.natAbs * a.natAbs)) = Int.ofNat (b.natAbs * b.natAbs) := by
      calc
        Int.ofNat (6 * (a.natAbs * a.natAbs))
            = 6 * Int.ofNat (a.natAbs * a.natAbs) := rfl
        _ = 6 * (a * a) := by rw [int_natAbs_mul_self a]
        _ = b * b := heq
        _ = Int.ofNat (b.natAbs * b.natAbs) := (int_natAbs_mul_self b).symm
    have hnat : 6 * (a.natAbs * a.natAbs) = b.natAbs * b.natAbs := Int.ofNat.inj hnat_int
    have ⟨_, hb0⟩ := nat_six_mul_sq_eq_sq_imp_zero (a.natAbs + b.natAbs) a.natAbs b.natAbs (Nat.le_refl _) hnat
    exact hb (Int.natAbs_eq_zero.mp hb0)
  · intro heq
    have ha_nonneg : (0 : Int) ≤ 6 * (a * a) := by
      have h0 : (0 : Int) ≤ Int.ofNat (6 * (a.natAbs * a.natAbs)) :=
        Int.ofNat_le.mpr (Nat.zero_le _)
      have heq6 : Int.ofNat (6 * (a.natAbs * a.natAbs)) = 6 * (a * a) := by
        calc
          Int.ofNat (6 * (a.natAbs * a.natAbs)) = 6 * Int.ofNat (a.natAbs * a.natAbs) := rfl
          _ = 6 * (a * a) := by rw [int_natAbs_mul_self a]
      rw [heq6] at h0
      exact h0
    have hb_pos : (0 : Int) < b * b := by
      have hne : b.natAbs ≠ 0 := fun h0 => hb (Int.natAbs_eq_zero.mp h0)
      have hpos : 0 < b.natAbs * b.natAbs := Nat.mul_pos (Nat.pos_of_ne_zero hne) (Nat.pos_of_ne_zero hne)
      rw [← int_natAbs_mul_self b]
      exact Int.ofNat_lt.mpr hpos
    omega

end Conjecture00000007616
