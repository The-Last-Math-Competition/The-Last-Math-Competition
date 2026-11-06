import Mathlib

/-!
# Conjecture 806: the Dirichlet spectral gap ratio R = (lambda_2 - lambda_1) / lambda_1

`lam k Ω` is the k-th Dirichlet eigenvalue of an open set `Ω ⊆ ℝ²` in its Courant-Fischer
(min-max) form, computed over the smooth compactly supported functions `C_c^∞(Ω)`:
`lam k Ω = inf_{W ⊆ C_c^∞(Ω), dim W = k} sup_{u ∈ W \ 0} ∫|∇u|² / ∫|u|²`.
The Rayleigh quotient is taken in `ℝ≥0∞`, so no boundedness side conditions are needed.
We show that for two disjoint open balls of equal radius, `lam 1 = lam 2`, hence `R = 0 ≠ 3/4`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace C806

noncomputable section

/-- Smoothness order `C^∞` (not analytic). -/
abbrev Cinf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- `C_c^∞(Ω)`: smooth functions with compact support contained in `Ω`. -/
def testSpace (Ω : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {u | ContDiff ℝ Cinf u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω}
  add_mem' := by
    rintro f g ⟨hf, hfc, hfΩ⟩ ⟨hg, hgc, hgΩ⟩
    exact ⟨hf.add hg, hfc.add hgc, (tsupport_add f g).trans (union_subset hfΩ hgΩ)⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hfc, hfΩ⟩
    refine ⟨hf.const_smul c, hfc.comp_left (g := fun y => c • y) (by simp), ?_⟩
    exact (closure_mono (Function.support_const_smul_subset c f)).trans hfΩ

/-- Dirichlet energy `∫ |∇u|²`. -/
def N (u : E → ℝ) : ℝ≥0∞ := ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ 2

/-- `∫ |u|²`. -/
def D (u : E → ℝ) : ℝ≥0∞ := ∫⁻ x, ‖u x‖ₑ ^ 2

/-- Rayleigh quotient. -/
def Q (u : E → ℝ) : ℝ≥0∞ := N u / D u

/-- The k-th Dirichlet eigenvalue (counted with multiplicity), Courant-Fischer form. -/
def lam (k : ℕ) (Ω : Set E) : ℝ≥0∞ :=
  ⨅ (W : Submodule ℝ (E → ℝ)) (_ : W ≤ testSpace Ω ∧ Module.finrank ℝ W = k),
    ⨆ (u : E → ℝ) (_ : u ∈ W ∧ u ≠ 0), Q u

/-- The ratio `R = (λ₂ - λ₁) / λ₁`. -/
def R (Ω : Set E) : ℝ := ((lam 2 Ω).toReal - (lam 1 Ω).toReal) / (lam 1 Ω).toReal

/-- The conjecture as stated. -/
def Conjecture : Prop :=
  (∃ c₁ c₂ : E, ∃ r : ℝ, 0 < r ∧ Disjoint (Metric.ball c₁ r) (Metric.ball c₂ r) ∧
      R (Metric.ball c₁ r ∪ Metric.ball c₂ r) = 3 / 4) ∧
  (∀ Ω : Set E, IsOpen Ω → Ω.Nonempty → volume Ω < ⊤ → R Ω ≤ 3 / 4) ∧
  (∀ Ω : Set E, IsOpen Ω → IsConnected Ω → volume Ω < ⊤ → R Ω < 3 / 4)

/-! ### Non-vacuity of the test space -/

theorem testSpace_ne_bot (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ u ∈ testSpace (Metric.ball c r), u ≠ 0 := by
  let b : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport, ?_⟩, ?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show r / 2 < r; linarith)
  · intro h
    have := b.one_of_mem_closedBall (x := c) (Metric.mem_closedBall_self b.rIn_pos.le)
    rw [h] at this
    simp at this

/-! ### Pointwise algebra -/

def Sep (f g : E → ℝ) : Prop :=
  ∀ x, (f x = 0 ∨ g x = 0) ∧ (fderiv ℝ f x = 0 ∨ fderiv ℝ g x = 0)

lemma sep_of_tsupport {f g : E → ℝ} {A B : Set E} (hAB : Disjoint A B)
    (hf : tsupport f ⊆ A) (hg : tsupport g ⊆ B) : Sep f g := by
  intro x
  by_cases hx : x ∈ A
  · have hxB : x ∉ B := Set.disjoint_left.mp hAB hx
    have : x ∉ tsupport g := fun h => hxB (hg h)
    exact ⟨Or.inr (image_eq_zero_of_notMem_tsupport this),
      Or.inr (fderiv_of_notMem_tsupport ℝ this)⟩
  · have : x ∉ tsupport f := fun h => hx (hf h)
    exact ⟨Or.inl (image_eq_zero_of_notMem_tsupport this),
      Or.inl (fderiv_of_notMem_tsupport ℝ this)⟩

lemma pt_comb {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : ℝ) (y z : F)
    (h : y = 0 ∨ z = 0) :
    ‖a • y + b • z‖ₑ ^ 2 = ‖a‖ₑ ^ 2 * ‖y‖ₑ ^ 2 + ‖b‖ₑ ^ 2 * ‖z‖ₑ ^ 2 := by
  rcases h with rfl | rfl <;> simp [enorm_smul, mul_pow]

lemma meas_N {f : E → ℝ} (hf : ContDiff ℝ Cinf f) : Measurable fun x => ‖fderiv ℝ f x‖ₑ ^ 2 :=
  (hf.continuous_fderiv (by simp)).measurable.enorm.pow_const 2

lemma meas_D {f : E → ℝ} (hf : ContDiff ℝ Cinf f) : Measurable fun x => ‖f x‖ₑ ^ 2 :=
  hf.continuous.measurable.enorm.pow_const 2

lemma N_comb {f g : E → ℝ} (hf : ContDiff ℝ Cinf f) (hg : ContDiff ℝ Cinf g) (hs : Sep f g)
    (a b : ℝ) :
    N (fun y => a • f y + b • g y) = ‖a‖ₑ ^ 2 * N f + ‖b‖ₑ ^ 2 * N g := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have pt : ∀ x, ‖fderiv ℝ (fun y => a • f y + b • g y) x‖ₑ ^ 2 =
      ‖a‖ₑ ^ 2 * ‖fderiv ℝ f x‖ₑ ^ 2 + ‖b‖ₑ ^ 2 * ‖fderiv ℝ g x‖ₑ ^ 2 := by
    intro x
    have := (((hdf x).hasFDerivAt.const_smul a).add ((hdg x).hasFDerivAt.const_smul b)).fderiv
    rw [show (fun y => a • f y + b • g y) = a • f + b • g from rfl, this]
    exact pt_comb a b _ _ (hs x).2
  unfold N
  simp_rw [pt]
  rw [lintegral_add_left ((meas_N hf).const_mul _), lintegral_const_mul _ (meas_N hf),
    lintegral_const_mul _ (meas_N hg)]

lemma D_comb {f g : E → ℝ} (hf : ContDiff ℝ Cinf f) (hg : ContDiff ℝ Cinf g) (hs : Sep f g)
    (a b : ℝ) :
    D (fun y => a • f y + b • g y) = ‖a‖ₑ ^ 2 * D f + ‖b‖ₑ ^ 2 * D g := by
  have pt : ∀ x, ‖a • f x + b • g x‖ₑ ^ 2 = ‖a‖ₑ ^ 2 * ‖f x‖ₑ ^ 2 + ‖b‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 :=
    fun x => pt_comb a b _ _ (hs x).1
  unfold D
  simp_rw [pt]
  rw [lintegral_add_left ((meas_D hf).const_mul _), lintegral_const_mul _ (meas_D hf),
    lintegral_const_mul _ (meas_D hg)]

/-! ### Positivity and finiteness -/

lemma D_ne_zero {u : E → ℝ} (hu : ContDiff ℝ Cinf u) (hne : u ≠ 0) : D u ≠ 0 := by
  intro h
  unfold D at h
  rw [lintegral_eq_zero_iff (meas_D hu)] at h
  apply hne
  have h2 : u =ᵐ[volume] (0 : E → ℝ) := by
    filter_upwards [h] with x hx
    simpa using hx
  exact (Continuous.ae_eq_iff_eq volume hu.continuous continuous_const).1 h2

lemma D_ne_top {u : E → ℝ} (hu : ContDiff ℝ Cinf u) (hc : HasCompactSupport u) : D u ≠ ⊤ := by
  have hcont : Continuous (fun x => u x ^ 2) := hu.continuous.pow 2
  have hsupp : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have h : Integrable (fun x => u x ^ 2) volume := hcont.integrable_of_hasCompactSupport hsupp
  have h2 := h.2
  unfold HasFiniteIntegral at h2
  unfold D
  simpa [enorm_pow] using h2.ne

/-! ### Translation invariance -/

lemma N_tr (p : E → ℝ) (v : E) : N (fun x => p (x - v)) = N p := by
  unfold N
  simp_rw [fderiv_comp_sub]
  exact lintegral_sub_right_eq_self (fun x => ‖fderiv ℝ p x‖ₑ ^ 2) v

lemma D_tr (p : E → ℝ) (v : E) : D (fun x => p (x - v)) = D p :=
  lintegral_sub_right_eq_self (fun x => ‖p x‖ₑ ^ 2) v

lemma Q_tr (p : E → ℝ) (v : E) : Q (fun x => p (x - v)) = Q p := by
  unfold Q
  rw [N_tr, D_tr]

lemma tr_mem {S T : Set E} (v : E) (h : ∀ x, x ∈ T ↔ x - v ∈ S) {p : E → ℝ}
    (hp : p ∈ testSpace S) : (fun x => p (x - v)) ∈ testSpace T := by
  obtain ⟨hd, hc, hs⟩ := hp
  refine ⟨hd.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · exact hc.comp_homeomorph (Homeomorph.subRight v)
  · intro x hx
    rw [h]
    apply hs
    have h1 : closure (Function.support fun x => p (x - v)) ⊆ (fun x => x - v) ⁻¹' closure (Function.support p) :=
      (continuous_sub_right v).closure_preimage_subset (Function.support p)
    exact h1 hx


lemma testSpace_mono {S T : Set E} (h : S ⊆ T) : testSpace S ≤ testSpace T :=
  fun _ hu => ⟨hu.1, hu.2.1, hu.2.2.trans h⟩

/-! ### Splitting a test function supported in `A ∪ B` -/

lemma ind_loc {A B : Set E} {u : E → ℝ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hu : tsupport u ⊆ A ∪ B) :
    (∀ x ∈ A, A.indicator u =ᶠ[𝓝 x] u) ∧ (∀ x, x ∉ A → A.indicator u =ᶠ[𝓝 x] 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · filter_upwards [hA.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy u
  · by_cases hxB : x ∈ B
    · filter_upwards [hB.mem_nhds hxB] with y hy
      exact Set.indicator_of_notMem (Set.disjoint_right.mp hAB hy) u
    · have hx' : x ∉ tsupport u := fun h => by
        rcases hu h with h | h <;> contradiction
      have := notMem_tsupport_iff_eventuallyEq.mp hx'
      filter_upwards [this] with y hy
      by_cases hyA : y ∈ A
      · rw [Set.indicator_of_mem hyA]; exact hy
      · rw [Set.indicator_of_notMem hyA]; rfl

lemma ind_mem {A B : Set E} {u : E → ℝ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hu : u ∈ testSpace (A ∪ B)) : A.indicator u ∈ testSpace A := by
  obtain ⟨hd, hc, hs⟩ := hu
  obtain ⟨h1, h2⟩ := ind_loc hA hB hAB hs
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ A
    · exact hd.contDiffAt.congr_of_eventuallyEq (h1 x hx)
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (h2 x hx)
  · refine hc.mono ?_
    intro x hx
    exact (Set.indicator_apply_ne_zero.1 hx).2
  · intro x hx
    by_contra hxA
    exact (notMem_tsupport_iff_eventuallyEq.mpr (h2 x hxA)) hx

lemma ind_add {A B : Set E} {u : E → ℝ} (hAB : Disjoint A B) (hs : tsupport u ⊆ A ∪ B) :
    u = fun y => (1 : ℝ) • A.indicator u y + (1 : ℝ) • B.indicator u y := by
  funext x
  simp only [one_smul]
  by_cases hA : x ∈ A
  · have hB : x ∉ B := Set.disjoint_left.mp hAB hA
    simp [Set.indicator_of_mem hA, Set.indicator_of_notMem hB]
  · by_cases hB : x ∈ B
    · simp [Set.indicator_of_notMem hA, Set.indicator_of_mem hB]
    · have : x ∉ tsupport u := fun h => by rcases hs h with h | h <;> contradiction
      simp [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB,
        image_eq_zero_of_notMem_tsupport this]

/-! ### Constancy of the Rayleigh quotient -/

lemma Q_smul {u : E → ℝ} (hu : ContDiff ℝ Cinf u) {c : ℝ} (hc : c ≠ 0) :
    Q (c • u) = Q u := by
  have hg : ContDiff ℝ Cinf (fun _ : E => (0 : ℝ)) := contDiff_const
  have hs : Sep u (fun _ : E => (0 : ℝ)) := by intro x; simp
  have e : (c • u) = fun y => c • u y + (0 : ℝ) • (fun _ : E => (0 : ℝ)) y := by
    funext y; simp
  have h0 : ‖c‖ₑ ^ 2 ≠ 0 := by simp [hc]
  have ht : ‖c‖ₑ ^ 2 ≠ ⊤ := by simp
  unfold Q
  rw [e, N_comb hu hg hs, D_comb hu hg hs]
  simp only [enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    add_zero]
  exact ENNReal.mul_div_mul_left _ _ h0 ht

lemma Q_pair {f g : E → ℝ} (hf : ContDiff ℝ Cinf f) (hg : ContDiff ℝ Cinf g) (hs : Sep f g)
    (hN : N g = N f) (hD : D g = D f) {a b : ℝ} (hab : ¬(a = 0 ∧ b = 0)) :
    Q (fun y => a • f y + b • g y) = Q f := by
  have h0 : ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 ≠ 0 := by
    intro h
    rw [add_eq_zero] at h
    apply hab
    simpa using h
  have ht : ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 ≠ ⊤ := by simp
  unfold Q
  rw [N_comb hf hg hs, D_comb hf hg hs, hN, hD, ← add_mul, ← add_mul]
  exact ENNReal.mul_div_mul_left _ _ h0 ht

/-! ### Eigenvalue comparisons -/

lemma lam1_le_Q (Ω : Set E) {u : E → ℝ} (hu : u ∈ testSpace Ω) (hne : u ≠ 0) :
    lam 1 Ω ≤ Q u := by
  have h1 : Submodule.span ℝ {u} ≤ testSpace Ω :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 hu)
  refine (iInf₂_le (Submodule.span ℝ {u}) ⟨h1, finrank_span_singleton hne⟩).trans ?_
  refine iSup₂_le fun w hw' => ?_
  obtain ⟨hw, hw0⟩ := hw'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hc : c ≠ 0 := by rintro rfl; simp at hw0
  exact (Q_smul hu.1 hc).le

theorem lam1_le_lam2 (Ω : Set E) : lam 1 Ω ≤ lam 2 Ω := by
  refine le_iInf₂ fun W hW => ?_
  obtain ⟨hWle, hdim⟩ := hW
  have hpos : 0 < Module.finrank ℝ W := by rw [hdim]; norm_num
  have : Module.Finite ℝ W := Module.finite_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hw0 : (w : E → ℝ) ≠ 0 := fun h => hw (Subtype.ext h)
  exact (lam1_le_Q Ω (hWle w.2) hw0).trans (le_iSup₂_of_le (w : E → ℝ) ⟨w.2, hw0⟩ le_rfl)

lemma lam2_le_Q_A {A B : Set E} (hAB : Disjoint A B) (v : E) (hT : ∀ x, x ∈ B ↔ x - v ∈ A)
    {p : E → ℝ} (hp : p ∈ testSpace A) (hne : p ≠ 0) : lam 2 (A ∪ B) ≤ Q p := by
  set q : E → ℝ := fun x => p (x - v) with hq
  have hqB : q ∈ testSpace B := tr_mem v hT hp
  have hs : Sep p q := sep_of_tsupport hAB hp.2.2 hqB.2.2
  have hpm : p ∈ testSpace (A ∪ B) := testSpace_mono subset_union_left hp
  have hqm : q ∈ testSpace (A ∪ B) := testSpace_mono subset_union_right hqB
  obtain ⟨x0, hx0⟩ : ∃ x0, p x0 ≠ 0 := by
    by_contra h
    exact hne (funext fun x => by_contra fun hx => h ⟨x, hx⟩)
  have hli : LinearIndependent ℝ ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hx0A : x0 ∈ A := hp.2.2 (subset_tsupport _ hx0)
    have hq0 : q x0 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => Set.disjoint_left.mp hAB hx0A (hqB.2.2 h))
    have e1 := congrFun hst x0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq0, mul_zero, add_zero,
      Pi.zero_apply] at e1
    have hs0 : s = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · exact h
      · exact absurd h hx0
    subst hs0
    have e2 := congrFun hst (x0 + v)
    have hq1 : q (x0 + v) ≠ 0 := by simpa [hq] using hx0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add,
      Pi.zero_apply] at e2
    refine ⟨rfl, ?_⟩
    rcases mul_eq_zero.1 e2 with h | h
    · exact h
    · exact absurd h hq1
  have hfin : Module.finrank ℝ (Submodule.span ℝ {p, q}) = 2 := by
    have h := finrank_span_eq_card hli
    have hr : Set.range ![p, q] = {p, q} := by
      ext x; simp; tauto
    rw [hr] at h
    simpa using h
  have hle : Submodule.span ℝ {p, q} ≤ testSpace (A ∪ B) := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hpm
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hqm
  refine (iInf₂_le (Submodule.span ℝ {p, q}) ⟨hle, hfin⟩).trans ?_
  refine iSup₂_le fun w hw' => ?_
  obtain ⟨hw, hw0⟩ := hw'
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
  have hab : ¬(a = 0 ∧ b = 0) := fun ⟨ha, hb⟩ => hw0 (by simp [ha, hb])
  exact (Q_pair hp.1 hqB.1 hs (N_tr p v) (D_tr p v) hab).le

lemma lam2_le_Q_B {A B : Set E} (hAB : Disjoint A B) (v : E) (hT : ∀ x, x ∈ B ↔ x - v ∈ A)
    {p : E → ℝ} (hp : p ∈ testSpace B) (hne : p ≠ 0) : lam 2 (A ∪ B) ≤ Q p := by
  have hT' : ∀ x, x ∈ A ↔ x - -v ∈ B := by
    intro x
    rw [hT, sub_neg_eq_add, add_sub_cancel_right]
  have hp' := tr_mem (-v) hT' hp
  have hne' : (fun x => p (x - -v)) ≠ 0 := by
    intro h
    apply hne
    funext x
    have := congrFun h (x - v)
    simpa using this
  have := lam2_le_Q_A hAB v hT hp' hne'
  rwa [Q_tr] at this

theorem lam2_le_Q {A B : Set E} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (v : E)
    (hT : ∀ x, x ∈ B ↔ x - v ∈ A) {u : E → ℝ} (hu : u ∈ testSpace (A ∪ B)) (hne : u ≠ 0) :
    lam 2 (A ∪ B) ≤ Q u := by
  set q := lam 2 (A ∪ B) with hqdef
  have hPA : ∀ p ∈ testSpace A, q * D p ≤ N p := by
    intro p hp
    by_cases h0 : p = 0
    · subst h0; simp [D]
    · exact (ENNReal.le_div_iff_mul_le (Or.inl (D_ne_zero hp.1 h0))
        (Or.inl (D_ne_top hp.1 hp.2.1))).1 (lam2_le_Q_A hAB v hT hp h0)
  have hPB : ∀ p ∈ testSpace B, q * D p ≤ N p := by
    intro p hp
    by_cases h0 : p = 0
    · subst h0; simp [D]
    · exact (ENNReal.le_div_iff_mul_le (Or.inl (D_ne_zero hp.1 h0))
        (Or.inl (D_ne_top hp.1 hp.2.1))).1 (lam2_le_Q_B hAB v hT hp h0)
  have hAu := ind_mem hA hB hAB hu
  have hBu := ind_mem hB hA hAB.symm (by rwa [union_comm] at hu)
  have hs : Sep (A.indicator u) (B.indicator u) := sep_of_tsupport hAB hAu.2.2 hBu.2.2
  have e := ind_add hAB hu.2.2
  have hN : N u = N (A.indicator u) + N (B.indicator u) := by
    have := N_comb hAu.1 hBu.1 hs 1 1
    rw [← e] at this
    simpa using this
  have hD : D u = D (A.indicator u) + D (B.indicator u) := by
    have := D_comb hAu.1 hBu.1 hs 1 1
    rw [← e] at this
    simpa using this
  refine (ENNReal.le_div_iff_mul_le (Or.inl (D_ne_zero hu.1 hne))
    (Or.inl (D_ne_top hu.1 hu.2.1))).2 ?_
  rw [hN, hD, mul_add]
  exact add_le_add (hPA _ hAu) (hPB _ hBu)

theorem lam2_le_lam1 {A B : Set E} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (v : E) (hT : ∀ x, x ∈ B ↔ x - v ∈ A) : lam 2 (A ∪ B) ≤ lam 1 (A ∪ B) := by
  refine le_iInf₂ fun W hW => ?_
  obtain ⟨hWle, hdim⟩ := hW
  have hpos : 0 < Module.finrank ℝ W := by rw [hdim]; norm_num
  have : Module.Finite ℝ W := Module.finite_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hw0 : (w : E → ℝ) ≠ 0 := fun h => hw (Subtype.ext h)
  exact (lam2_le_Q hA hB hAB v hT (hWle w.2) hw0).trans
    (le_iSup₂_of_le (w : E → ℝ) ⟨w.2, hw0⟩ le_rfl)

/-! ### Two equal disjoint disks -/

/-- For two disjoint open disks of the same radius, `λ₁ = λ₂`, so `R = 0`. -/
theorem R_two_disks (c₁ c₂ : E) (r : ℝ)
    (hd : Disjoint (Metric.ball c₁ r) (Metric.ball c₂ r)) :
    lam 1 (Metric.ball c₁ r ∪ Metric.ball c₂ r) = lam 2 (Metric.ball c₁ r ∪ Metric.ball c₂ r) ∧
    R (Metric.ball c₁ r ∪ Metric.ball c₂ r) = 0 := by
  have hT : ∀ x, x ∈ Metric.ball c₂ r ↔ x - (c₂ - c₁) ∈ Metric.ball c₁ r := by
    intro x
    rw [mem_ball_iff_norm, mem_ball_iff_norm]
    have : x - (c₂ - c₁) - c₁ = x - c₂ := by abel
    rw [this]
  have h := le_antisymm (lam1_le_lam2 _)
    (lam2_le_lam1 Metric.isOpen_ball Metric.isOpen_ball hd (c₂ - c₁) hT)
  refine ⟨h, ?_⟩
  simp [R, h]

theorem not_conjecture : ¬ Conjecture := by
  rintro ⟨⟨c₁, c₂, r, -, hd, hR⟩, -, -⟩
  rw [(R_two_disks c₁ c₂ r hd).2] at hR
  norm_num at hR

end

end C806
