import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace SUnit23

def IsSUnit (S : Finset ℕ) (x : ℚ) : Prop :=
  x ≠ 0 ∧ x.num.natAbs.primeFactors ⊆ S ∧ x.den.primeFactors ⊆ S

def Solutions (S : Finset ℕ) : Set (ℚ × ℚ) :=
  {xy | IsSUnit S xy.1 ∧ IsSUnit S xy.2 ∧ xy.1 + xy.2 = 1}

def splitFraction (a b : ℕ) : ℚ × ℚ :=
  ((a : ℚ) / (a + b), (b : ℚ) / (a + b))

theorem reduced_num {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : Nat.Coprime a b) :
    ((a : ℚ) / (a + b)).num = (a : ℤ) := by
  have hs : (0 : ℤ) < (a + b : ℕ) := by exact_mod_cast (show 0 < a + b by omega)
  have hcop : Nat.Coprime (a : ℤ).natAbs ((a + b : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.coprime_self_add_right.mpr hc
  simpa only [Int.cast_natCast, Nat.cast_add, Int.cast_add] using (Rat.num_div_eq_of_coprime hs hcop)

theorem reduced_den {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : Nat.Coprime a b) :
    ((a : ℚ) / (a + b)).den = a + b := by
  have hs : (0 : ℤ) < (a + b : ℕ) := by exact_mod_cast (show 0 < a + b by omega)
  have hcop : Nat.Coprime (a : ℤ).natAbs ((a + b : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.coprime_self_add_right.mpr hc
  have h := Rat.den_div_eq_of_coprime hs hcop
  have h' : (((a : ℚ) / (a + b)).den : ℤ) = ((a + b : ℕ) : ℤ) := by
    simpa only [Int.cast_natCast, Nat.cast_add, Int.cast_add] using h
  exact Int.ofNat_inj.mp h'

theorem small_integer_support {N k : ℕ} (hk : k ≠ 0) (hle : k ≤ N) :
    k.primeFactors ⊆ Nat.primesLE N := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h.2.1).trans hle, h.1⟩

theorem actual_sunit_solutions {N a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ N) (hbN : b ≤ N) (hc : Nat.Coprime a b) :
    splitFraction a b ∈ Solutions (Nat.primesLE (2 * N)) := by
  have hsum : 0 < a + b := by omega
  have hden : ((a : ℚ) + b) ≠ 0 := by exact_mod_cast hsum.ne'
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hX : IsSUnit (Nat.primesLE (2 * N)) ((a : ℚ) / (a + b)) := by
    refine ⟨div_ne_zero haQ hden, ?_, ?_⟩
    · rw [reduced_num ha hb hc]
      simp only [Int.natAbs_natCast]
      exact small_integer_support ha.ne' (by omega)
    · rw [reduced_den ha hb hc]
      exact small_integer_support hsum.ne' (by omega)
  have hY : IsSUnit (Nat.primesLE (2 * N)) ((b : ℚ) / (b + a)) := by
    refine ⟨div_ne_zero hbQ (by simpa [add_comm] using hden), ?_, ?_⟩
    · rw [reduced_num hb ha hc.symm]
      simp only [Int.natAbs_natCast]
      exact small_integer_support hb.ne' (by omega)
    · rw [reduced_den hb ha hc.symm]
      exact small_integer_support (by omega) (by omega)
  refine ⟨hX, by simpa [splitFraction, add_comm] using hY, ?_⟩
  dsimp [splitFraction]
  field_simp

theorem fraction_injective {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h : splitFraction a b = splitFraction c d) : a = c ∧ b = d := by
  have hX : (a : ℚ) / (a + b) = (c : ℚ) / (c + d) := congrArg Prod.fst h
  have hn := congrArg Rat.num hX
  rw [reduced_num ha hb hab, reduced_num hc hd hcd] at hn
  have haeq : a = c := by exact_mod_cast hn
  have hden := congrArg Rat.den hX
  rw [reduced_den ha hb hab, reduced_den hc hd hcd] at hden
  exact ⟨haeq, by omega⟩

end SUnit23

#check SUnit23.actual_sunit_solutions
#check SUnit23.fraction_injective
#print axioms SUnit23.reduced_num
#print axioms SUnit23.reduced_den
#print axioms SUnit23.small_integer_support
#print axioms SUnit23.actual_sunit_solutions
#print axioms SUnit23.fraction_injective
