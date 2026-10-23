import Approx
set_option autoImplicit false
namespace PIR

/-- Uniform coupled seeds represent random queries; the hypothesis bounds the
sum of the three actual error probabilities by 1/6, not an untested oracle. -/
theorem small_error_expected_gap {L R : Nat} {Q : Type}
    (p : CoupledScheme (2^L) R Q) (hL : 4 ≤ L)
    (herr : 6*errorTotal (Nat.two_pow_pos L) p ≤ R*2^(3*L)) :
    9*(L*R) ≤ 4*downloadTotal p := by
  let N := 2^(3*L)
  let G := goodTotal (Nat.two_pow_pos L) p
  let E := errorTotal (Nat.two_pow_pos L) p
  let D := downloadTotal p
  have hu : R*N ≤ G+E := by
    simpa only [binary_database_card] using total_union_bound (Nat.two_pow_pos L) p
  have he : 6*E ≤ R*N := herr
  have hg : 5*(R*N) ≤ 6*G := by omega
  have hi : (3*L)*G ≤ N*(D+R) := expected_information_bound p
  have hfull : N*(15*(L*R)) ≤ N*(6*(D+R)) := by
    calc
      N*(15*(L*R)) = (3*L)*(5*(R*N)) := by
        change N*((3*5)*(L*R)) = (3*L)*(5*(R*N))
        ac_rfl
      _ ≤ (3*L)*(6*G) := Nat.mul_le_mul_left (3*L) hg
      _ = 6*((3*L)*G) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ ≤ 6*(N*(D+R)) := Nat.mul_le_mul_left 6 hi
      _ = N*(6*(D+R)) := by ac_rfl
  have hcancel : 15*(L*R) ≤ 6*(D+R) := Nat.le_of_mul_le_mul_left hfull (Nat.two_pow_pos (3*L))
  exact expected_cost_gap L R D hL hcancel

theorem rejects_half_neighborhood {L R a b : Nat} {Q : Type}
    (p : CoupledScheme (2^L) R Q) (hL : 4 ≤ L) (hR : 0 < R)
    (herr : 6*errorTotal (Nat.two_pow_pos L) p ≤ R*2^(3*L))
    (hab : 4*b < 9*a) (hrate : a*downloadTotal p ≤ b*(L*R)) : False := by
  exact rational_rate_gap L R (downloadTotal p) a b
    (Nat.mul_pos (by omega) hR) (small_error_expected_gap p hL herr) hab hrate

end PIR
