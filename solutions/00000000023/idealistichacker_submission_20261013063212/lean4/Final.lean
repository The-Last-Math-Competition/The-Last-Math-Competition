import CoprimePairs
import RatBridge
import PrimeBound

namespace SUnit23

def witnessSolutions (N : ℕ) : Finset (ℚ × ℚ) :=
  (CoprimePairs.coprimePairs N).image (fun ab => splitFraction ab.1 ab.2)

theorem witness_card (N : ℕ) :
    (witnessSolutions N).card = (CoprimePairs.coprimePairs N).card := by
  unfold witnessSolutions
  apply Finset.card_image_of_injOn
  intro ab hab cd hcd h
  rcases ab with ⟨a, b⟩
  rcases cd with ⟨c, d⟩
  have hab' := CoprimePairs.mem_coprimePairs.mp hab
  have hcd' := CoprimePairs.mem_coprimePairs.mp hcd
  have heq := fraction_injective (by omega) (by omega) (by omega) (by omega)
    hab'.2.2.2.2 hcd'.2.2.2.2 h
  exact Prod.ext heq.1 heq.2

theorem witnesses_are_actual_solutions (N : ℕ) :
    ↑(witnessSolutions N) ⊆ Solutions (Nat.primesLE (2 * N)) := by
  intro xy hxy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hxy
  have h := CoprimePairs.mem_coprimePairs.mp hab
  exact actual_sunit_solutions (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2

theorem witness_lower_bound (N : ℕ) : N ^ 2 ≤ 4 * (witnessSolutions N).card := by
  rw [witness_card]
  exact CoprimePairs.coprimePairs_card_lower_bound N

theorem every_constant_is_exceeded (C : ℝ) :
    ∃ m : ℕ, 0 < m ∧
      C * ((SUnitPrimeBound.primeSet m).card : ℝ) ^ 2 <
        ((witnessSolutions (SUnitPrimeBound.N m)).card : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (144 * max C 0 + 1)
  have hm0 : 0 < m := by
    have hreal : (0 : ℝ) < m := by nlinarith [le_max_right C 0]
    exact_mod_cast hreal
  refine ⟨m, hm0, ?_⟩
  let N := SUnitPrimeBound.N m
  let s := (SUnitPrimeBound.primeSet m).card
  let t := (witnessSolutions N).card
  change C * (s : ℝ) ^ 2 < (t : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast SUnitPrimeBound.N_positive m
  have hcount : (N : ℝ) ^ 2 ≤ 4 * (t : ℝ) := by
    exact_mod_cast witness_lower_bound N
  have hprimes : (m : ℝ) * (s : ℝ) ≤ 6 * (N : ℝ) := by
    exact_mod_cast SUnitPrimeBound.cardinal_bound m
  have hsquare : (m : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ 36 * (N : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) * s) hprimes 2
    nlinarith only [hs]
  have hmlarge : 144 * max C 0 < (m : ℝ) ^ 2 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    nlinarith only [hm, hm1]
  by_contra h
  have ht : (t : ℝ) ≤ C * (s : ℝ) ^ 2 := le_of_not_gt h
  have ht' : (t : ℝ) ≤ max C 0 * (s : ℝ) ^ 2 :=
    ht.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg _))
  have hlow := mul_le_mul_of_nonneg_left hcount (sq_nonneg (m : ℝ))
  have hmid := mul_le_mul_of_nonneg_left ht' (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2)
  have hhigh := mul_le_mul_of_nonneg_left hsquare
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_max_right C 0))
  have hstrict : 144 * max C 0 * (N : ℝ) ^ 2 < (m : ℝ) ^ 2 * (N : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hmlarge (sq_pos_of_pos hN)
  nlinarith only [hlow, hmid, hhigh, hstrict]

def UniformQuadraticBound : Prop :=
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
    ∀ T : Finset (ℚ × ℚ), ↑T ⊆ Solutions S → (T.card : ℝ) ≤ C * (S.card : ℝ) ^ 2

theorem no_uniform_quadratic_bound : ¬UniformQuadraticBound := by
  rintro ⟨C, h⟩
  obtain ⟨m, _, hm⟩ := every_constant_is_exceeded C
  have hupper := h (SUnitPrimeBound.primeSet m)
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (witnessSolutions (SUnitPrimeBound.N m))
    (witnesses_are_actual_solutions (SUnitPrimeBound.N m))
  exact (not_lt_of_ge hupper) hm

end SUnit23

#check SUnit23.every_constant_is_exceeded
#check SUnit23.no_uniform_quadratic_bound
#print axioms SUnit23.witness_card
#print axioms SUnit23.witnesses_are_actual_solutions
#print axioms SUnit23.witness_lower_bound
#print axioms SUnit23.every_constant_is_exceeded
#print axioms SUnit23.no_uniform_quadratic_bound
