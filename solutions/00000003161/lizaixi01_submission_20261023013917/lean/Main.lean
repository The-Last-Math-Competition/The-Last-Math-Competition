import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace TLMC3161
open scoped BigOperators
variable (n : ℕ)
abbrev Signal (n : ℕ) := Fin (n+3) → ℝ
noncomputable def support (x : Signal n) : Finset (Fin (n+3)) := by
  classical
  exact Finset.univ.filter fun i => x i ≠ 0
noncomputable def IsSparse (k : ℕ) (x : Signal n) : Prop := (support n x).card ≤ k
lemma sparse_one_single (x : Signal n) (hx : IsSparse n 1 x) :
    ∃ i : Fin (n+3), ∃ t : ℝ, x=Pi.single i t := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hx
  refine ⟨i,x i,?_⟩
  ext j
  by_cases hj : j=i
  · subst j; simp
  · have hz : x j=0 := by
      by_contra h
      have hm : j ∈ support n x := by simp [support,h]
      have he := hi hm
      simp only [Finset.mem_singleton] at he
      exact hj he
    simp [hj,hz]

def A : Matrix (Fin 2) (Fin (n+3)) ℝ := fun r i => if r=0 then 1 else i.val
noncomputable def measure (x : Signal n) : Fin 2 → ℝ := (A n).mulVec x
lemma measure_single_zero (i : Fin (n+3)) (t : ℝ) :
    measure n (Pi.single i t) 0=t := by
  simp [measure,Matrix.mulVec_single,A]
lemma measure_single_one (i : Fin (n+3)) (t : ℝ) :
    measure n (Pi.single i t) 1=(i.val:ℝ)*t := by
  simp [measure,Matrix.mulVec_single,A]
lemma sparse_measure_injective (x y : Signal n) (hx : IsSparse n 1 x)
    (hy : IsSparse n 1 y) (h : measure n x=measure n y) : x=y := by
  classical
  obtain ⟨i,t,rfl⟩ := sparse_one_single n x hx
  obtain ⟨j,u,rfl⟩ := sparse_one_single n y hy
  have h0 : t=u := by simpa only [measure_single_zero] using congrFun h 0
  have h1 : (i.val:ℝ)*t=(j.val:ℝ)*u := by
    simpa only [measure_single_one] using congrFun h 1
  subst u
  by_cases ht : t=0
  · simp [ht]
  · have he : (i.val:ℝ)=(j.val:ℝ) := mul_right_cancel₀ ht h1
    have hij : i=j := Fin.ext (by exact_mod_cast he)
    subst j; rfl

noncomputable def decoder (y : Fin 2 → ℝ) : Signal n := by
  classical
  exact if h : ∃ x : Signal n, IsSparse n 1 x ∧ measure n x=y then Classical.choose h else 0
lemma decoder_correct (x : Signal n) (hx : IsSparse n 1 x) :
    decoder n (measure n x)=x := by
  classical
  have he : ∃ z : Signal n, IsSparse n 1 z ∧ measure n z=measure n x := ⟨x,hx,rfl⟩
  rw [decoder,dif_pos he]
  exact sparse_measure_injective n _ x (Classical.choose_spec he).1 hx
    (Classical.choose_spec he).2

def CanRecover (m k : ℕ) : Prop :=
  ∃ M : Matrix (Fin m) (Fin (n+3)) ℝ, ∃ D : (Fin m → ℝ) → Signal n,
    ∀ x, IsSparse n k x → D (M.mulVec x)=x
lemma two_measurements : CanRecover n 2 1 := ⟨A n,decoder n,decoder_correct n⟩
noncomputable def minimalMeasurements : ℕ := by
  classical
  exact Nat.find (show ∃ m, CanRecover n m 1 from ⟨2,two_measurements n⟩)
lemma minimum_recovers : CanRecover n (minimalMeasurements n) 1 := by
  classical
  exact Nat.find_spec (show ∃ m, CanRecover n m 1 from ⟨2,two_measurements n⟩)
lemma minimum_le_two : minimalMeasurements n ≤ 2 := by
  classical
  exact Nat.find_min' (show ∃ m, CanRecover n m 1 from ⟨2,two_measurements n⟩) (two_measurements n)
lemma underdetermined : 2 < n+3 := by omega
lemma logarithmic_bound_violated (C : ℝ) (hC : 0<C) :
    ∃ n : ℕ, (2:ℝ) < C * Real.log ((n+3:ℕ):ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.exp (2/C))
  have hn3 : Real.exp (2/C) < ((n+3:ℕ):ℝ) := by push_cast; linarith
  have hlog : 2/C < Real.log ((n+3:ℕ):ℝ) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hn3
  refine ⟨n,?_⟩
  have hm := (div_lt_iff₀ hC).mp hlog
  nlinarith
/-- No positive dimension-independent logarithmic lower bound for exact recovery. -/
theorem exact_recovery_counterexample (C : ℝ) (hC : 0<C) :
    ∃ n : ℕ, 2 < n+3 ∧ CanRecover n 2 1 ∧
      (minimalMeasurements n:ℝ) < C * (1:ℝ) * Real.log (((n+3:ℕ):ℝ)/1) := by
  obtain ⟨n,hn⟩ := logarithmic_bound_violated C hC
  have hm : (minimalMeasurements n:ℝ) ≤ 2 := by exact_mod_cast minimum_le_two n
  refine ⟨n,underdetermined n,two_measurements n,?_⟩
  simpa using lt_of_le_of_lt hm hn
end TLMC3161
