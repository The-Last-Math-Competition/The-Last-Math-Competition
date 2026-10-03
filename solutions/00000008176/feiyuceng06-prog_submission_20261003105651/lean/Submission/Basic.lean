import Mathlib

/-!
# Conjecture 00000008176: the "non-Wieferich" zero/nonzero criterion fails

For an integer `q`, let `δ_A(q)` be the density, relative to the primes, of the set of
primes `p` modulo which `q` is a primitive root. The second claim of Conjecture
00000008176 is that whether `δ_A(q)` is zero or nonzero is decided by the criterion

  `q ≢ 1 (mod p²)` for every prime `p`.

This fails, whichever way the criterion is matched with "zero" and "nonzero":

* `q = 4` satisfies the criterion (`4 - 1 = 3` is squarefree), yet `δ_A(4) = 0`;
* `q = 9` violates it (`9 ≡ 1 (mod 4)`), yet `δ_A(9) = 0`.

Both are perfect squares. For every integer `s`, the square `s²` is a primitive root
modulo no odd prime `p`: if `p ∣ s` its residue is `0`, and otherwise
`(s²)^((p-1)/2) = s^(p-1) = 1` by Fermat's little theorem, so its order is at most
`(p-1)/2 < p - 1`. Hence the set of such primes is contained in `{2}`, and its relative
density is `0`, unconditionally.
-/

namespace Submission00000008176

open Filter Topology

/-- The primes `p` modulo which `q` is a primitive root: the residue of `q` in `ZMod p` is a
primitive `(p-1)`-th root of unity, i.e. it generates the cyclic group `(ℤ/p)ˣ`. -/
def artinSet (q : ℤ) : Set ℕ :=
  {p | p.Prime ∧ IsPrimitiveRoot ((q : ZMod p)) (p - 1)}

/-- The set `S` of primes has density `d` relative to the primes:
`#(S ∩ [0, x]) / π(x) → d` as `x → ∞`. -/
def HasPrimeDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun x : ℕ => ((S ∩ Set.Iic x).ncard : ℝ) / (Nat.primeCounting x : ℝ)) atTop (𝓝 d)

/-- The criterion of the conjecture: `q ≢ 1 (mod p²)` for every prime `p`. -/
def NonWieferich (q : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ q ≡ 1 [ZMOD (p : ℤ) ^ 2]

/-- Second claim of the conjecture: `δ_A(q)` is nonzero exactly when the criterion holds. -/
def ClassificationNonzero : Prop :=
  ∀ q : ℤ, ¬ HasPrimeDensity (artinSet q) 0 ↔ NonWieferich q

/-- The same claim with "nonzero" read as "has a nonzero density". -/
def ClassificationNonzero' : Prop :=
  ∀ q : ℤ, (∃ d : ℝ, d ≠ 0 ∧ HasPrimeDensity (artinSet q) d) ↔ NonWieferich q

/-- The reversed matching: `δ_A(q)` is zero exactly when the criterion holds. -/
def ClassificationZero : Prop :=
  ∀ q : ℤ, HasPrimeDensity (artinSet q) 0 ↔ NonWieferich q

/-- A perfect square is a primitive root modulo no prime other than possibly `2`. -/
theorem artinSet_sq_subset (s : ℤ) : artinSet (s ^ 2) ⊆ {2} := by
  rintro p ⟨hp, hprim⟩
  by_contra hp2
  have hp2' : p ≠ 2 := hp2
  have := Fact.mk hp
  have hodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with h | h
    · exact absurd ((Nat.Prime.even_iff hp).1 h) hp2'
    · exact Nat.odd_iff.1 h
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcast : ((s ^ 2 : ℤ) : ZMod p) = ((s : ZMod p)) ^ 2 := by push_cast; ring
  rw [hcast] at hprim
  by_cases hs : (s : ZMod p) = 0
  · have h1 := hprim.pow_eq_one
    rw [hs, zero_pow (by norm_num), zero_pow (by omega)] at h1
    exact zero_ne_one h1
  · have hpow : ((s : ZMod p) ^ 2) ^ ((p - 1) / 2) = 1 := by
      rw [← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hs
    have hdvd := hprim.dvd_of_pow_eq_one _ hpow
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- For every integer `s`, `δ_A(s²) = 0`. -/
theorem hasPrimeDensity_sq (s : ℤ) : HasPrimeDensity (artinSet (s ^ 2)) 0 := by
  unfold HasPrimeDensity
  have hcard : ∀ x : ℕ, ((artinSet (s ^ 2) ∩ Set.Iic x).ncard : ℝ) ≤ 1 := by
    intro x
    have : (artinSet (s ^ 2) ∩ Set.Iic x).ncard ≤ ({2} : Set ℕ).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_left.trans (artinSet_sq_subset s))
        (Set.finite_singleton 2)
    rw [Set.ncard_singleton] at this
    exact_mod_cast this
  have hup : Tendsto (fun x : ℕ => (1 : ℝ) / (Nat.primeCounting x : ℝ)) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun x => ?_)
    (fun x => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (hcard x) (Nat.cast_nonneg _)

/-- `4` satisfies the criterion: `p² ∣ 4 - 1 = 3` is impossible for a prime `p`. -/
theorem nonWieferich_four : NonWieferich 4 := by
  intro p hp h
  have hdvd : ((p : ℤ) ^ 2) ∣ 3 := by
    have := (Int.modEq_iff_dvd.1 h.symm)
    simpa using this
  have hle := Int.le_of_dvd (by norm_num) hdvd
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  nlinarith

/-- `9` violates the criterion: `9 ≡ 1 (mod 2²)`. -/
theorem not_nonWieferich_nine : ¬ NonWieferich 9 :=
  fun h => h 2 Nat.prime_two (by decide)

theorem hasPrimeDensity_four : HasPrimeDensity (artinSet 4) 0 := by
  simpa using hasPrimeDensity_sq 2

theorem hasPrimeDensity_nine : HasPrimeDensity (artinSet 9) 0 := by
  simpa using hasPrimeDensity_sq 3

/-- **The second claim fails**: `δ_A(4) = 0` although `4` satisfies the criterion. -/
theorem not_classificationNonzero : ¬ ClassificationNonzero :=
  fun h => (h 4).2 nonWieferich_four hasPrimeDensity_four

/-- The same with "nonzero" read as "has a nonzero density": densities are unique limits. -/
theorem not_classificationNonzero' : ¬ ClassificationNonzero' := by
  intro h
  obtain ⟨d, hd, hdens⟩ := (h 4).2 nonWieferich_four
  exact hd (tendsto_nhds_unique hdens hasPrimeDensity_four)

/-- The reversed matching fails too: `δ_A(9) = 0` although `9` violates the criterion. -/
theorem not_classificationZero : ¬ ClassificationZero :=
  fun h => not_nonWieferich_nine ((h 9).1 hasPrimeDensity_nine)

/-- **Conjecture 00000008176 is false**: its second claim fails. Whatever the first, third and
fourth claims (`P`, `Q`, `R`) mean, the conjunction is false. -/
theorem conjecture_00000008176_false (P Q R : Prop) :
    ¬ (P ∧ ClassificationNonzero ∧ Q ∧ R) :=
  fun h => not_classificationNonzero h.2.1

end Submission00000008176

#print axioms Submission00000008176.conjecture_00000008176_false
#print axioms Submission00000008176.not_classificationNonzero'
#print axioms Submission00000008176.not_classificationZero
