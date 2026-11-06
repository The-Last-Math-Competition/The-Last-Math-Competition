import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace PrimePell259

theorem positive_coprime_square_factor {a b c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hsq : a * b = c ^ 2) :
    ∃ u v : ℤ, a = u ^ 2 ∧ b = v ^ 2 := by
  obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcop hsq
  obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcop.symm (by rwa [mul_comm])
  refine ⟨u, v, ?_, ?_⟩
  · rcases hu with h | h
    · exact h
    · nlinarith [sq_nonneg u]
  · rcases hv with h | h
    · exact h
    · nlinarith [sq_nonneg v]

theorem adjacent_prime_square_split {a b c p : ℤ} (hp : Prime p) (hp0 : 0 < p)
    (ha : 0 < a) (hba : b = a + 1) (hprod : a * b = p * c ^ 2) :
    (∃ u v : ℤ, a = p * u ^ 2 ∧ b = v ^ 2) ∨
    (∃ u v : ℤ, a = u ^ 2 ∧ b = p * v ^ 2) := by
  have hb : 0 < b := by omega
  have hcop : IsCoprime a b := ⟨-1, 1, by linarith⟩
  have hdiv : p ∣ a * b := ⟨c ^ 2, hprod⟩
  rcases hp.dvd_mul.mp hdiv with hpa | hpb
  · obtain ⟨A, hA⟩ := hpa
    have hA0 : 0 < A := by
      apply (mul_pos_iff_of_pos_left hp0).mp
      rwa [← hA]
    have hAb : IsCoprime A b := by
      rw [hA] at hcop
      exact hcop.of_mul_left_right
    have hsq : A * b = c ^ 2 := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (A * b) = (p * A) * b := by ring
        _ = a * b := by rw [hA]
        _ = p * c ^ 2 := hprod
    obtain ⟨u, v, hu, hv⟩ := positive_coprime_square_factor hA0 hb hAb hsq
    exact Or.inl ⟨u, v, by simpa [hu] using hA, hv⟩
  · obtain ⟨B, hB⟩ := hpb
    have hB0 : 0 < B := by
      apply (mul_pos_iff_of_pos_left hp0).mp
      rwa [← hB]
    have haB : IsCoprime a B := by
      rw [hB] at hcop
      exact hcop.of_mul_right_right
    have hsq : a * B = c ^ 2 := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (a * B) = a * (p * B) := by ring
        _ = a * b := by rw [hB]
        _ = p * c ^ 2 := hprod
    obtain ⟨u, v, hu, hv⟩ := positive_coprime_square_factor ha hB0 haB hsq
    exact Or.inr ⟨u, v, hu, by simpa [hv] using hB⟩

theorem pell_mod_four_parity {p x y : ℤ} (hp : p % 4 = 1)
    (heq : x ^ 2 - p * y ^ 2 = 1) : x % 2 = 1 ∧ y % 2 = 0 := by
  have hm := congrArg (fun z : ℤ => z % 4) heq
  have hx0 : 0 ≤ x % 4 := Int.emod_nonneg _ (by decide)
  have hxl : x % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  have hy0 : 0 ≤ y % 4 := Int.emod_nonneg _ (by decide)
  have hyl : y % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  rw [Int.sub_emod, Int.mul_emod p (y ^ 2) 4, pow_two, pow_two] at hm
  rw [Int.mul_emod x x 4, Int.mul_emod y y 4, hp] at hm
  interval_cases hx : x % 4 <;> interval_cases hy : y % 4
    <;> norm_num [hx, hy] at hm <;> omega

theorem negative_pell_of_prime_one_mod_four (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ x y : ℤ, x ^ 2 - (p : ℤ) * y ^ 2 = -1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp4Z : (p : ℤ) % 4 = 1 := by exact_mod_cast hp4
  obtain ⟨s, hs⟩ := Pell.IsFundamental.exists_of_not_isSquare hp0 hpZ.not_isSquare
  have hxs : 1 < s.x := hs.1
  have hpar := pell_mod_four_parity hp4Z s.prop
  let a : ℤ := (s.x - 1) / 2
  let b : ℤ := (s.x + 1) / 2
  let c : ℤ := s.y / 2
  have hxa : s.x = 2 * a + 1 := by dsimp [a]; omega
  have hba : b = a + 1 := by dsimp [a, b]; omega
  have hyc : s.y = 2 * c := by dsimp [c]; omega
  have ha : 0 < a := by omega
  have hprod : a * b = (p : ℤ) * c ^ 2 := by
    have heq := s.prop
    rw [hxa, hyc] at heq
    rw [hba]
    nlinarith only [heq]
  rcases adjacent_prime_square_split hpZ hp0 ha hba hprod with hleft | hright
  · obtain ⟨u, v, hu, hv⟩ := hleft
    have hnew : v ^ 2 - (p : ℤ) * u ^ 2 = 1 := by omega
    have hpos : 1 < |v| := by
      have hsq : 1 < v ^ 2 := by omega
      exact (one_lt_sq_iff_one_lt_abs v).mp hsq
    let t : Pell.Solution₁ (p : ℤ) := Pell.Solution₁.mk |v| |u| (by simpa only [sq_abs] using hnew)
    have hsmall : |v| < s.x := by nlinarith only [ha, hpos, hxa, hv, hba, sq_abs v]
    have hminimal : ∀ {q : Pell.Solution₁ (p : ℤ)}, 1 < q.x → s.x ≤ q.x := hs.2.2
    have hmin := hminimal (show 1 < t.x from hpos)
    change s.x ≤ |v| at hmin
    omega
  · obtain ⟨u, v, hu, hv⟩ := hright
    exact ⟨u, v, by omega⟩

end PrimePell259
