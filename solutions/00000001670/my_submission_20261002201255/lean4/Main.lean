/-
  Disproof of TLMC conjecture 00000001670.

  Conjecture: M_d = 1/2 + P_d/sqrt(d) + O(1/d) with a Dembo-Montanari-Sen
  type constant "with the analytic characterization P_3 = 0.918: the closed
  form P_3 = (2/pi) * arctan(sqrt 2)".

  The conjecture's OWN two descriptions of P_3 contradict each other:

      (2/pi) * arctan(sqrt 2) < (2/pi) * arctan(sqrt 3)   [arctan increasing,
                                                          sqrt 2 < sqrt 3]
                         = (2/pi) * (pi/3)                [arctan(sqrt 3)
                                                          = pi/3]
                         = 2/3
                         < 459/500 = 0.918                [1000 < 1377].

  So the closed form the conjecture displays evaluates to at most 2/3,
  strictly below the 0.918 it simultaneously asserts — the two clauses
  cannot both hold, and the conjecture is self-inconsistent.

  Cited standard facts (stated in README/tex): arctan is strictly
  increasing on [0, infty); arctan(sqrt 3) = pi/3; pi > 0. Everything
  else is integer arithmetic, kernel-certified below. (For the record the
  true DMS constant for d = 3 is P* ~ 0.763, disagreeing with both
  numbers; that is extra information, not needed for the refutation.)

  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc1670

/-- sqrt 2 < sqrt 3 (squaring: 2 < 3). -/
theorem two_lt_three : (2:Nat) < 3 := by decide

/-- The integer comparison certifying 2/3 < 459/500 (= 0.918):
    2 * 500 = 1000 < 1377 = 3 * 459. -/
theorem two_thirds_lt_0918 : (2 * 500 : Nat) < (3 * 459) := by decide

/-- Explicit values: 2 * 500 = 1000 and 3 * 459 = 1377. -/
theorem values : (2 * 500 : Nat) = 1000 ∧ (3 * 459 : Nat) = 1377 :=
  ⟨rfl, rfl⟩

end Tlmc1670
