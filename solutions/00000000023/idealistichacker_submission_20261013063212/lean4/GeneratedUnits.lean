import Final
import Mathlib.Algebra.Group.Subgroup.Basic

namespace SUnit23

def unitGroup (S : Finset ℕ) : Subgroup ℚˣ :=
  Subgroup.closure {u | u = -1 ∨ ∃ p ∈ S, (u : ℚ) = (p : ℚ)}

theorem bounded_integer_in_unit_group (B k : ℕ) (hk : 0 < k) (hB : k ≤ B) :
    ∃ u : ℚˣ, (u : ℚ) = (k : ℚ) ∧ u ∈ unitGroup (Nat.primesLE B) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      exact ⟨1, by simp, (unitGroup _).one_mem⟩
    · let p := k.minFac
      have hp : p.Prime := Nat.minFac_prime hk1
      obtain ⟨j, hj⟩ := Nat.minFac_dvd k
      have hjpos : 0 < j := by nlinarith
      have hjlt : j < k := by nlinarith [hp.two_le]
      obtain ⟨v, hv, hvmem⟩ := ih j hjlt hjpos (by omega)
      let u : ℚˣ := Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)
      have hu : (u : ℚ) = (p : ℚ) := rfl
      have hpB : p ≤ B := by
        have hpk : p ≤ k := Nat.le_of_dvd hk (Nat.minFac_dvd k)
        omega
      have humem : u ∈ unitGroup (Nat.primesLE B) :=
        Subgroup.subset_closure (Or.inr ⟨p, Nat.mem_primesLE.mpr ⟨hpB, hp⟩, hu⟩)
      refine ⟨u * v, ?_, (unitGroup _).mul_mem humem hvmem⟩
      simp only [Units.val_mul, hu, hv]
      exact_mod_cast hj.symm

def GeneratedSolutions (S : Finset ℕ) : Set (ℚ × ℚ) :=
  {xy | ∃ u v : ℚˣ, u ∈ unitGroup S ∧ v ∈ unitGroup S ∧
    (u : ℚ) = xy.1 ∧ (v : ℚ) = xy.2 ∧ xy.1 + xy.2 = 1}

theorem fractions_in_generated_group {N a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ N) (hbN : b ≤ N) :
    splitFraction a b ∈ GeneratedSolutions (Nat.primesLE (2 * N)) := by
  obtain ⟨u, hu, hU⟩ := bounded_integer_in_unit_group (2 * N) a ha (by omega)
  obtain ⟨v, hv, hV⟩ := bounded_integer_in_unit_group (2 * N) b hb (by omega)
  obtain ⟨d, hd, hD⟩ := bounded_integer_in_unit_group (2 * N) (a + b) (by omega) (by omega)
  refine ⟨u / d, v / d, (unitGroup _).div_mem hU hD, (unitGroup _).div_mem hV hD, ?_, ?_, ?_⟩
  · simp [splitFraction, hu, hd]
  · simp [splitFraction, hv, hd]
  · dsimp [splitFraction]
    have hden : ((a : ℚ) + b) ≠ 0 := by positivity
    field_simp

theorem witness_generated_solutions (N : ℕ) :
    ↑(witnessSolutions N) ⊆ GeneratedSolutions (Nat.primesLE (2 * N)) := by
  intro xy hxy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hxy
  have h := CoprimePairs.mem_coprimePairs.mp hab
  exact fractions_in_generated_group (by omega) (by omega) h.2.1 h.2.2.2.1

def GeneratedUniformBound : Prop :=
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
    ∀ T : Finset (ℚ × ℚ), ↑T ⊆ GeneratedSolutions S →
      (T.card : ℝ) ≤ C * (S.card : ℝ) ^ 2

theorem no_generated_unit_quadratic_bound : ¬GeneratedUniformBound := by
  rintro ⟨C, h⟩
  obtain ⟨m, _, hm⟩ := every_constant_is_exceeded C
  have hupper := h (SUnitPrimeBound.primeSet m)
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (witnessSolutions (SUnitPrimeBound.N m))
    (witness_generated_solutions (SUnitPrimeBound.N m))
  exact (not_lt_of_ge hupper) hm

end SUnit23

#check SUnit23.bounded_integer_in_unit_group
#check SUnit23.fractions_in_generated_group
#check SUnit23.no_generated_unit_quadratic_bound
#print axioms SUnit23.bounded_integer_in_unit_group
#print axioms SUnit23.fractions_in_generated_group
#print axioms SUnit23.witness_generated_solutions
#print axioms SUnit23.no_generated_unit_quadratic_bound
