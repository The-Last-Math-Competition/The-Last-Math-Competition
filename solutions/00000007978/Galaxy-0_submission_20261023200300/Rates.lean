import PIR
set_option autoImplicit false
namespace PIR

theorem nat_succ_le_two_pow (k : Nat) : k + 1 ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem linear_le_scaled_pow (d k : Nat) : d+k ≤ 2^k*(d+1) := by
  have hlin : d+k ≤ (k+1)*(d+1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  exact Nat.le_trans hlin (Nat.mul_le_mul_right (d+1) (nat_succ_le_two_pow k))

theorem power_information_bound (n d : Nat) (hd : d ≤ n) :
    n * 2^d ≤ 2^n * (d+1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
  subst n
  have h := Nat.mul_le_mul_right (2^d) (linear_le_scaled_pow d k)
  simpa only [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

-- The answer alphabet bound converts to a bit-length lower bound.
theorem bits_of_alphabet_bound (L d : Nat)
    (h : (2^L)*(2^L*(2^L)) ≤ 2^d) : 3*L ≤ d := by
  have he : (2^L)*(2^L*(2^L)) = 2^(3*L) := by
    simp only [show 3*L = L+(L+L) by omega, Nat.pow_add]
  rw [he] at h
  apply Nat.le_of_not_gt
  intro hn
  have hh := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (show d < 3*L by omega)
  omega

theorem zero_error_bits_bound {L d : Nat} {Seed Query : Type}
    (p : Scheme (2^L) (2^d) Seed Query) (r : Seed) : 3*L ≤ d := by
  exact bits_of_alphabet_bound L d (answer_alphabet_bound (Nat.pow_pos (by decide)) p r)

-- A rational rate greater than one third has a fixed positive margin.
-- This natural-number version avoids assuming real-number limit libraries.
theorem rate_margin_excluded (L d a b : Nat) (ha : b < 3*a)
    (hlarge : a < (3*a-b)*L) (hdownload : 3*L ≤ d+1)
    (hrate : a*d ≤ b*L) : False := by
  have hmul := Nat.mul_le_mul_left a hdownload
  have hdis : a*(d+1) = a*d+a := by simp [Nat.mul_add]
  have hthree : a*(3*L) = 3*a*L := by simp [Nat.mul_comm,Nat.mul_left_comm]
  have hsplit : (3*a-b)*L + b*L = 3*a*L := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  omega
end PIR

namespace PIR
/-- An expected-download bound with total error at most 1/6 excludes a whole
neighbourhood of 1/2, not merely a scheme that attains 1/2 exactly. -/
theorem expected_cost_gap (L R download : Nat) (hL : 4 ≤ L)
    (h : 15*(L*R) ≤ 6*(download+R)) :
    9*(L*R) ≤ 4*download := by
  have hsize := Nat.mul_le_mul_right R hL
  omega

theorem rational_rate_gap (L R download a b : Nat) (hLR : 0 < L*R)
    (hgap : 9*(L*R) ≤ 4*download) (hab : 4*b < 9*a)
    (hrate : a*download ≤ b*(L*R)) : False := by
  have h1 := Nat.mul_le_mul_left a hgap
  have h2 := Nat.mul_le_mul_left 4 hrate
  have h3 := Nat.mul_lt_mul_of_pos_right hab hLR
  have he1 : a*(9*(L*R)) = (9*a)*(L*R) := by simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have he2 : a*(4*download) = 4*(a*download) := by simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have he3 : 4*(b*(L*R)) = (4*b)*(L*R) := by simp [Nat.mul_assoc]
  rw [he1,he2] at h1
  rw [he3] at h2
  omega

theorem four_ninths_lt_one_half : 4*2 < 1*9 := by decide
end PIR
