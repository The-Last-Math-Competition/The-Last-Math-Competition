import Std

/-!
Conjecture 00000000147 writes a probability of a deterministic prime-gap
condition without specifying a sample space. The theorem below checks the
natural point-mass interpretation: its Boolean probability cannot be near
one half, whereas exp(-t) is an interior probability for t > 0.
-/

/-- A deterministic event probability, either zero or one, avoids the central interval. -/
theorem boolean_probability_avoids_middle (b : Nat) (hb : b = 0 ∨ b = 1) :
    ¬ (1 < 4 * b ∧ 4 * b < 3) := by
  rcases hb with hzero | hone <;> omega

#print axioms boolean_probability_avoids_middle
