import Mathlib
import Conjecture6680.Statement

/-! # Conjecture 00000006680: same optimal transport value, different dual structure

Finite discrete Kantorovich transport.  Reuse note: the 2x2 parametrisation of couplings by one
parameter (`P x`, the analogue of `Omega2_form` / `Omega2_bounds`) and the diagonal/anti-diagonal support
idea are adapted from our own accepted solution of conjecture 00000006320. -/

-- (formal statement: see Statement.lean)

namespace C6680

/-- Uniform marginals `(1/2, 1/2)`. -/
noncomputable def mu2 : Fin 2 → ℝ := fun _ => 1 / 2

/-- The cost `[[0,0],[a,b]]`. -/
def C (a b : ℝ) : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![a, b]]

/-- The one-parameter family of 2x2 plans with marginals `(1/2,1/2)`
(cf. `Omega2_form` of conjecture 6320). -/
noncomputable def P (x : ℝ) : Fin 2 → Fin 2 → ℝ := ![![x, 1 / 2 - x], ![1 / 2 - x, x]]

lemma isProb_mu2 : IsProb mu2 := by
  refine ⟨fun _ => by simp [mu2], ?_⟩
  simp [mu2]

lemma coupling_iff (π : Fin 2 → Fin 2 → ℝ) :
    IsCoupling mu2 mu2 π ↔ ∃ x, 0 ≤ x ∧ x ≤ 1 / 2 ∧ π = P x := by
  constructor
  · rintro ⟨h0, hr, hc⟩
    have r0 := hr 0; have r1 := hr 1; have c0 := hc 0; have c1 := hc 1
    simp only [mu2, Fin.sum_univ_two] at r0 r1 c0 c1
    refine ⟨π 0 0, h0 0 0, by linarith [h0 0 1], ?_⟩
    funext i j
    fin_cases i <;> fin_cases j <;> simp [P] <;> linarith
  · rintro ⟨x, hx0, hx1, rfl⟩
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [P] <;> linarith
    · fin_cases i <;> simp [P, mu2, Fin.sum_univ_two]
    · fin_cases j <;> simp [P, mu2, Fin.sum_univ_two]

lemma planCost_P (a b x : ℝ) : planCost (C a b) (P x) = a * (1 / 2 - x) + b * x := by
  simp [planCost, C, P, Fin.sum_univ_two]

lemma optValue_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : optValue mu2 mu2 (C a b) = a / 2 := by
  unfold optValue
  apply IsLeast.csInf_eq
  refine ⟨⟨P 0, (coupling_iff _).2 ⟨0, le_rfl, by norm_num, rfl⟩, ?_⟩, ?_⟩
  · rw [planCost_P]; ring
  · rintro t ⟨π, hπ, rfl⟩
    obtain ⟨x, hx0, hx1, rfl⟩ := (coupling_iff _).1 hπ
    rw [planCost_P]; nlinarith

lemma optPlan_iff {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (π : Fin 2 → Fin 2 → ℝ) :
    IsOptPlan mu2 mu2 (C a b) π ↔ ∃ x, 0 ≤ x ∧ x ≤ 1 / 2 ∧ π = P x ∧ b * x = a * x := by
  constructor
  · rintro ⟨hπ, hmin⟩
    obtain ⟨x, hx0, hx1, rfl⟩ := (coupling_iff _).1 hπ
    have := hmin (P 0) ((coupling_iff _).2 ⟨0, le_rfl, by norm_num, rfl⟩)
    rw [planCost_P, planCost_P] at this
    refine ⟨x, hx0, hx1, rfl, ?_⟩
    nlinarith
  · rintro ⟨x, hx0, hx1, rfl, hx⟩
    refine ⟨(coupling_iff _).2 ⟨x, hx0, hx1, rfl⟩, fun ρ hρ => ?_⟩
    obtain ⟨y, hy0, hy1, rfl⟩ := (coupling_iff _).1 hρ
    rw [planCost_P, planCost_P]; nlinarith

lemma dualObj_eq (p : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    dualObj mu2 mu2 p = (p.1 0 + p.1 1 + p.2 0 + p.2 1) / 2 := by
  simp [dualObj, mu2, Fin.sum_univ_two]; ring

lemma feasible_iff (a b : ℝ) (p : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    IsDualFeasible (C a b) p ↔
      p.1 0 + p.2 0 ≤ 0 ∧ p.1 0 + p.2 1 ≤ 0 ∧ p.1 1 + p.2 0 ≤ a ∧ p.1 1 + p.2 1 ≤ b := by
  constructor
  · intro h
    exact ⟨by simpa [C] using h 0 0, by simpa [C] using h 0 1, by simpa [C] using h 1 0,
      by simpa [C] using h 1 1⟩
  · rintro ⟨h1, h2, h3, h4⟩ i j
    fin_cases i <;> fin_cases j <;> simpa [C]

/-- The potential pair `u = (0, a)`, `v = (0, 0)`. -/
def p0 (a : ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) := (![0, a], ![0, 0])

lemma dualOpt_iff {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (p : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    IsDualOpt mu2 mu2 (C a b) p ↔
      IsDualFeasible (C a b) p ∧ p.1 0 + p.2 1 = 0 ∧ p.1 1 + p.2 0 = a := by
  have key : ∀ q, IsDualFeasible (C a b) q → q.1 0 + q.1 1 + q.2 0 + q.2 1 ≤ a := by
    intro q hq
    rw [feasible_iff] at hq; linarith [hq.2.1, hq.2.2.1]
  constructor
  · rintro ⟨hf, hmax⟩
    have h := hmax (p0 a) ((feasible_iff _ _ _).2 (by simp [p0]; exact hab))
    rw [dualObj_eq, dualObj_eq] at h
    have := key p hf
    rw [feasible_iff] at hf
    simp [p0] at h
    refine ⟨(feasible_iff _ _ _).2 hf, ?_, ?_⟩ <;> linarith [hf.2.1, hf.2.2.1]
  · rintro ⟨hf, h1, h2⟩
    refine ⟨hf, fun q hq => ?_⟩
    rw [dualObj_eq, dualObj_eq]
    linarith [key q hq]

lemma strongDuality {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : StrongDuality mu2 mu2 (C a b) := by
  refine ⟨p0 a, (dualOpt_iff ha hab _).2 ⟨(feasible_iff _ _ _).2 (by simp [p0]; exact hab),
    by simp [p0], by simp [p0]⟩, ?_⟩
  rw [optValue_eq ha hab, dualObj_eq]; simp [p0]

lemma dualUnique_of_eq {a : ℝ} (ha : 0 ≤ a) : DualUniqueModGauge mu2 mu2 (C a a) := by
  refine ⟨p0 a, (dualOpt_iff ha le_rfl _).2 ⟨(feasible_iff _ _ _).2 (by simp [p0]), by simp [p0],
    by simp [p0]⟩, fun q hq => ?_⟩
  rw [dualOpt_iff ha le_rfl] at hq
  obtain ⟨hf, h1, h2⟩ := hq
  rw [feasible_iff] at hf
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨q.1 0, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [p0] <;> linarith
  · funext j; fin_cases j <;> simp [p0] <;> linarith

lemma not_dualUnique_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ¬ DualUniqueModGauge mu2 mu2 (C a b) := by
  rintro ⟨p, hp, hall⟩
  have hq : IsDualOpt mu2 mu2 (C a b) (![0, b], ![a - b, 0]) :=
    (dualOpt_iff ha hab.le _).2 ⟨(feasible_iff _ _ _).2 (by simp; linarith), by simp, by simp⟩
  have hp0 : IsDualOpt mu2 mu2 (C a b) (p0 a) :=
    (dualOpt_iff ha hab.le _).2 ⟨(feasible_iff _ _ _).2 (by simp [p0]; exact hab.le), by simp [p0],
      by simp [p0]⟩
  obtain ⟨t, h1, h2⟩ := hall _ hq
  obtain ⟨s, k1, k2⟩ := hall _ hp0
  have e1 := congrFun h1 0; have e2 := congrFun h2 0
  have e3 := congrFun k1 0; have e4 := congrFun k2 0
  have e5 := congrFun h2 1; have e6 := congrFun k2 1
  simp [p0] at e1 e2 e3 e4 e5 e6
  linarith

lemma full_mem {a : ℝ} (ha : 0 ≤ a) :
    {ij : Fin 2 × Fin 2 | P (1 / 4) ij.1 ij.2 ≠ 0} ∈ optSuppFamily mu2 mu2 (C a a) := by
  refine ⟨P (1 / 4), (optPlan_iff ha le_rfl _).2 ⟨1 / 4, by norm_num, by norm_num, rfl, rfl⟩, rfl⟩

lemma full_not_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    {ij : Fin 2 × Fin 2 | P (1 / 4) ij.1 ij.2 ≠ 0} ∉ optSuppFamily mu2 mu2 (C a b) := by
  rintro ⟨π, hπ, hS⟩
  obtain ⟨x, hx0, hx1, rfl, hx⟩ := (optPlan_iff ha hab.le _).1 hπ
  have hx' : x = 0 := by
    have : (b - a) * x = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  subst hx'
  have : ((0 : Fin 2), (0 : Fin 2)) ∈ {ij : Fin 2 × Fin 2 | P (1 / 4) ij.1 ij.2 ≠ 0} := by
    simp [P]
  rw [hS] at this
  simp [P] at this

lemma separation {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsProb mu2 ∧ IsProb mu2 ∧ SameValueDualDiffers mu2 mu2 (C a a) (C a b) ∧
      optSuppFamily mu2 mu2 (C a a) ≠ optSuppFamily mu2 mu2 (C a b) := by
  refine ⟨isProb_mu2, isProb_mu2, ⟨?_, strongDuality ha le_rfl, strongDuality ha hab.le,
    dualUnique_of_eq ha, not_dualUnique_of_lt ha hab⟩, fun h => ?_⟩
  · rw [optValue_eq ha le_rfl, optValue_eq ha hab.le]
  · exact full_not_mem ha hab (h ▸ full_mem ha)

theorem main : Claim := by
  refine ⟨⟨2, 2, mu2, mu2, C 0 0, C 0 1, separation le_rfl zero_lt_one⟩,
    ⟨2, 2, mu2, mu2, C 0 0, C 0 1, ?_⟩⟩
  obtain ⟨h1, h2, h3, _⟩ := separation (a := 0) (b := 1) le_rfl zero_lt_one
  refine ⟨h1, h2, h3, fun h => ?_⟩
  have : ((1 : Fin 2), (1 : Fin 2)) ∈ costSupp (C 0 1) := by simp [costSupp, C]
  rw [← h] at this
  simp [costSupp, C] at this

/-- The same separation for the nonzero pair `[[0,0],[1,1]]` vs `[[0,0],[1,2]]` (equal cost supports,
different optimal-plan supports and dual structure). -/
theorem main_nonzero : ConjectureA ∧ costSupp (C 1 1) = costSupp (C 1 2) :=
  ⟨⟨2, 2, mu2, mu2, C 1 1, C 1 2, separation zero_le_one one_lt_two⟩, by
    ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [costSupp, C]⟩

end C6680
