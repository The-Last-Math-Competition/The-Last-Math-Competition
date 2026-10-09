import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Conjecture161

/-- Every prime divisor of the usual order product for `GL(4, p)` is at most
`p² + p + 1`, for every natural number `p ≥ 2`. -/
theorem prime_le_of_dvd_gl4_card_product {p r : ℕ} (hp : 2 ≤ p)
    (hr : r.Prime) (hdvd : r ∣ ∏ i : Fin 4, (p ^ 4 - p ^ i.val)) :
    r ≤ p ^ 2 + p + 1 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have h0 : (2 + q) ^ 4 - 1 = (q + 1) * (q + 3) * ((2 + q) ^ 2 + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h1 : (2 + q) ^ 4 - (2 + q) =
      (2 + q) * (q + 1) * ((2 + q) ^ 2 + (2 + q) + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h2 : (2 + q) ^ 4 - (2 + q) ^ 2 = (2 + q) ^ 2 * (q + 1) * (q + 3) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h3 : (2 + q) ^ 4 - (2 + q) ^ 3 = (2 + q) ^ 3 * (q + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have hprod : (∏ i : Fin 4, ((2 + q) ^ 4 - (2 + q) ^ i.val)) =
      (2 + q) ^ 6 * (q + 1) ^ 4 * (q + 3) ^ 2 *
        ((2 + q) ^ 2 + 1) * ((2 + q) ^ 2 + (2 + q) + 1) := by
    rw [Fin.prod_univ_four]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    change ((2 + q) ^ 4 - 1) * ((2 + q) ^ 4 - (2 + q)) *
      ((2 + q) ^ 4 - (2 + q) ^ 2) * ((2 + q) ^ 4 - (2 + q) ^ 3) = _
    rw [h0, h1, h2, h3]
    ring
  rw [hprod] at hdvd
  simp only [hr.dvd_mul] at hdvd
  rcases hdvd with (((h | h) | h) | h) | h
  · have hle := Nat.le_of_dvd (by omega : 0 < 2 + q) (hr.dvd_of_dvd_pow h)
    nlinarith
  · have hle := Nat.le_of_dvd (by omega : 0 < q + 1) (hr.dvd_of_dvd_pow h)
    nlinarith
  · have hle := Nat.le_of_dvd (by omega : 0 < q + 3) (hr.dvd_of_dvd_pow h)
    nlinarith
  · have hle := Nat.le_of_dvd (by omega : 0 < (2 + q) ^ 2 + 1) h
    omega
  · exact Nat.le_of_dvd (by omega) h

end Conjecture161
