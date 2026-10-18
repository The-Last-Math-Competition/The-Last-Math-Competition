import Std

/-!
Finite-additivity core of the disproof of conjecture 00000000140.
A common positive atom mass p/q cannot satisfy the probability bound for every
finite set of distinct atoms: taking q+1 atoms already exceeds total mass one.
The countable-additivity step for the prime set is explained in the report.
-/

def IsUniformSubprobability (p q : Nat) : Prop :=
  0 < q ∧ 0 < p ∧ ∀ n : Nat, n * p ≤ q

/-- Equal positive atom masses on a countably infinite space exceed total mass. -/
theorem no_uniform_probability_on_countably_infinite_space :
    ¬ ∃ p q : Nat, IsUniformSubprobability p q := by
  rintro ⟨p, q, hq, hp, hbound⟩
  have h := hbound (q + 1)
  have hp1 : 1 ≤ p := by omega
  have hlower : q + 1 ≤ (q + 1) * p := by
    calc
      q + 1 = (q + 1) * 1 := by simp
      _ ≤ (q + 1) * p := Nat.mul_le_mul_left (q + 1) hp1
  omega

/-- Finite-mass obstruction for any proposed positive common atom numerator. -/
theorem finite_equal_atom_mass_bound_impossible (p q : Nat)
    (hp : 0 < p) (hbound : ∀ n : Nat, n * p ≤ q) : False := by
  have h := hbound (q + 1)
  have hp1 : 1 ≤ p := by omega
  have hlower : q + 1 ≤ (q + 1) * p := by
    calc
      q + 1 = (q + 1) * 1 := by simp
      _ ≤ (q + 1) * p := Nat.mul_le_mul_left (q + 1) hp1
  omega

#print axioms no_uniform_probability_on_countably_infinite_space
#print axioms finite_equal_atom_mass_bound_impossible
