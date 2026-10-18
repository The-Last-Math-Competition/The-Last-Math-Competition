import Std

/-!
Arithmetic core for the disproof of conjecture 00000000114.
A positive integer-valued gap cannot lie in the real interval (1/4, 1/2):
a hypothetical value, scaled by four, would be an integer strictly between 1 and 2.
The real-analysis and weak-convergence bridge is supplied in the paper.
-/

/-- No natural number lies strictly between one and two. -/
theorem no_nat_strictly_between_one_and_two (n : Nat)
    (hlo : 1 < 4 * n) (hhi : 4 * n < 2) : False := by
  omega

/-- Scaled arithmetic form of the empty interval (1/4, 1/2) on the naturals. -/
theorem no_nat_in_quarter_half_interval :
    ¬ ∃ n : Nat, 1 < 4 * n ∧ 4 * n < 2 := by
  rintro ⟨n, hlo, hhi⟩
  exact no_nat_strictly_between_one_and_two n hlo hhi

#print axioms no_nat_strictly_between_one_and_two
#print axioms no_nat_in_quarter_half_interval
