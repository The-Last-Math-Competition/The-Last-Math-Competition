import Conjecture1030.SphereMoments

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030
set_option maxHeartbeats 3000000

/-- Golden ratio and the common circumradius of the displayed coordinates. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2
def r : ℝ := Real.sqrt (phi + 2)

theorem phi_pos : 0 < phi := by unfold phi; positivity
theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  unfold phi
  nlinarith

theorem r_pos : 0 < r := by
  unfold r
  exact Real.sqrt_pos.2 (by linarith [phi_pos])
theorem r_ne_zero : r ≠ 0 := ne_of_gt r_pos
theorem r_sq : r ^ 2 = phi + 2 := Real.sq_sqrt (by linarith [phi_pos])
theorem phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos

def icoA : ℝ := 1 / r
def icoB : ℝ := phi / r

theorem icoA_pos : 0 < icoA := div_pos (by norm_num) r_pos
theorem icoB_pos : 0 < icoB := div_pos phi_pos r_pos

theorem icoA_sq_add_icoB_sq : icoA ^ 2 + icoB ^ 2 = 1 := by
  unfold icoA icoB
  field_simp [r_ne_zero]
  nlinarith [phi_sq, r_sq]

theorem icoA_sq_mul_icoB_sq : icoA ^ 2 * icoB ^ 2 = 1 / 5 := by
  unfold icoA icoB
  field_simp [r_ne_zero]
  nlinarith [phi_sq, r_sq, sq_nonneg (r ^ 2 - (phi + 2))]

theorem icoA_fourth_add_icoB_fourth : icoA ^ 4 + icoB ^ 4 = 3 / 5 := by
  have h := icoA_sq_add_icoB_sq
  have hm := icoA_sq_mul_icoB_sq
  nlinarith [sq_nonneg (icoA ^ 2 + icoB ^ 2 - 1)]

/-- Twelve independently signed cyclic coordinate triples. -/
def icoVec : Fin 12 → E := ![
  !₂[0, icoA, icoB], !₂[0, icoA, -icoB],
  !₂[0, -icoA, icoB], !₂[0, -icoA, -icoB],
  !₂[icoA, icoB, 0], !₂[icoA, -icoB, 0],
  !₂[-icoA, icoB, 0], !₂[-icoA, -icoB, 0],
  !₂[icoB, 0, icoA], !₂[icoB, 0, -icoA],
  !₂[-icoB, 0, icoA], !₂[-icoB, 0, -icoA]]

theorem icoVec_norm (i : Fin 12) : ‖icoVec i‖ = 1 := by
  have h : ‖icoVec i‖ ^ 2 = 1 := by
    rw [norm_sq3]
    fin_cases i <;> simpa [icoVec, add_comm] using icoA_sq_add_icoB_sq
  nlinarith [norm_nonneg (icoVec i)]

def icoVertex (i : Fin 12) : S2 :=
  ⟨icoVec i, by simpa only [Metric.mem_sphere, dist_zero_right] using icoVec_norm i⟩

@[simp] theorem icoVertex_coe (i : Fin 12) : (icoVertex i : E) = icoVec i := rfl

theorem icoVec_injective : Function.Injective icoVec := by
  intro i j h
  have h0 := congrArg (fun x : E => x 0) h
  have h1 := congrArg (fun x : E => x 1) h
  have h2 := congrArg (fun x : E => x 2) h
  fin_cases i <;> fin_cases j <;>
    norm_num [icoVec, Matrix.cons_val_two] at h0 h1 h2 ⊢ <;>
    nlinarith [icoA_pos, icoB_pos]

theorem icoVertex_injective : Function.Injective icoVertex := by
  intro i j h
  exact icoVec_injective (congrArg Subtype.val h)

def ico : Finset S2 := Finset.univ.map ⟨icoVertex, icoVertex_injective⟩

@[simp] theorem ico_card : ico.card = 12 := by simp [ico]
theorem ico_nonempty : ico.Nonempty := by
  exact Finset.card_pos.mp (by rw [ico_card]; norm_num)

@[simp] theorem mem_ico (x : S2) : x ∈ ico ↔ ∃ i : Fin 12, icoVertex i = x := by
  simp [ico]

theorem sum_ico (f : S2 → ℝ) : ∑ x ∈ ico, f x = ∑ i : Fin 12, f (icoVertex i) := by
  simp [ico]

/-- The entire total-degree-five discrete monomial table, with no parity cases omitted. -/
theorem ico_monomial_table (a b c : ℕ) (h : a + b + c ≤ 5) :
    (12 : ℝ)⁻¹ * ∑ i : Fin 12,
      (icoVec i 0) ^ a * (icoVec i 1) ^ b * (icoVec i 2) ^ c =
    if Odd a ∨ Odd b ∨ Odd c then 0
    else if a + b + c = 0 then 1
    else if a + b + c = 2 then 1 / 3
    else if a = 4 ∨ b = 4 ∨ c = 4 then 1 / 5 else 1 / 15 := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  have hc : c ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [Nat.odd_iff] at h ⊢
  all_goals
    norm_num [Fin.sum_univ_succ, icoVec, Matrix.cons_val_two]
  all_goals
    nlinarith [icoA_sq_add_icoB_sq, icoA_sq_mul_icoB_sq,
      icoA_fourth_add_icoB_fourth]

/-- Membership characterized by the zero coordinate and the two independent signs. -/
theorem ico_coordinates_iff (x : S2) : x ∈ ico ↔
    ((x : E) 0 = 0 ∧ ((x : E) 1 = icoA ∨ (x : E) 1 = -icoA) ∧
      ((x : E) 2 = icoB ∨ (x : E) 2 = -icoB)) ∨
    (((x : E) 0 = icoA ∨ (x : E) 0 = -icoA) ∧
      ((x : E) 1 = icoB ∨ (x : E) 1 = -icoB) ∧ (x : E) 2 = 0) ∨
    (((x : E) 0 = icoB ∨ (x : E) 0 = -icoB) ∧ (x : E) 1 = 0 ∧
      ((x : E) 2 = icoA ∨ (x : E) 2 = -icoA)) := by
  constructor
  · rintro hx
    obtain ⟨i, rfl⟩ := (mem_ico x).1 hx
    fin_cases i <;> norm_num [icoVertex, icoVec, Matrix.cons_val_two]
  · intro hx
    apply (mem_ico x).2
    rcases hx with ⟨h0, h1 | h1, h2 | h2⟩ |
      ⟨h0 | h0, h1 | h1, h2⟩ | ⟨h0 | h0, h1, h2 | h2⟩
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨2, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨3, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨4, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨5, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨6, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨7, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨8, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨9, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨10, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]
    · refine ⟨11, ?_⟩
      apply Subtype.ext
      ext j
      fin_cases j <;> simp_all [icoVertex, icoVec, Matrix.cons_val_two]

/-- Any independent coordinate sign choices preserve the vertex set. -/
theorem ico_sign_symmetry (x y : S2)
    (h : ∀ i, (y : E) i = (x : E) i ∨ (y : E) i = -(x : E) i)
    (hx : x ∈ ico) : y ∈ ico := by
  have hz (i : Fin 3) (hi : (x : E) i = 0) : (y : E) i = 0 := by
    rcases h i with h | h <;> simp_all
  have hs (i : Fin 3) (v : ℝ) (hi : (x : E) i = v ∨ (x : E) i = -v) :
      (y : E) i = v ∨ (y : E) i = -v := by
    rcases h i with h | h <;> rcases hi with hi | hi <;> simp_all
  rw [ico_coordinates_iff] at hx ⊢
  rcases hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl ⟨hz 0 h0, hs 1 icoA h1, hs 2 icoB h2⟩
  · exact Or.inr (Or.inl ⟨hs 0 icoA h0, hs 1 icoB h1, hz 2 h2⟩)
  · exact Or.inr (Or.inr ⟨hs 0 icoB h0, hz 1 h1, hs 2 icoA h2⟩)

/-- The cyclic permutation (x,y,z)↦(y,z,x) preserves the vertex set. -/
theorem ico_cyclic_symmetry (x y : S2)
    (h0 : (y : E) 0 = (x : E) 1) (h1 : (y : E) 1 = (x : E) 2)
    (h2 : (y : E) 2 = (x : E) 0) (hx : x ∈ ico) : y ∈ ico := by
  rw [ico_coordinates_iff] at hx ⊢
  rw [h0, h1, h2]
  rcases hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h0⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h0⟩)
  · exact Or.inl ⟨h1, h2, h0⟩

/-- The mutual inner product of the canonical upper pair. -/
theorem icoB_sq_sub_icoA_sq : icoB ^ 2 - icoA ^ 2 = icoA * icoB := by
  unfold icoA icoB
  field_simp [r_ne_zero]
  nlinarith [phi_sq]

@[simp] theorem ico_canonical_inner :
    ⟪(icoVertex 0 : E), (icoVertex 2 : E)⟫ = icoA * icoB := by
  rw [inner3]
  norm_num [icoVertex, icoVec, Matrix.cons_val_two]
  nlinarith [icoB_sq_sub_icoA_sq]

/-- Exhaust the four other upper vertices from the two prescribed inner products. -/
theorem ico_upper_candidates (z : S2)
    (h0 : ⟪(icoVertex 0 : E), (z : E)⟫ = icoA * icoB)
    (h1 : ⟪(icoVertex 2 : E), (z : E)⟫ = icoA * icoB ∨
      ⟪(icoVertex 2 : E), (z : E)⟫ = -(icoA * icoB)) : z ∈ ico := by
  rw [inner3] at h0
  simp only [icoVertex_coe] at h0
  norm_num [icoVec, Matrix.cons_val_two] at h0
  simp only [inner3, icoVertex_coe] at h1
  norm_num [icoVec, Matrix.cons_val_two] at h1
  have hn := sphere_sq z
  rw [ico_coordinates_iff]
  rcases h1 with h1 | h1
  · have hz1 : (z : E) 1 = 0 := by nlinarith [icoA_pos]
    have hz2 : (z : E) 2 = icoA := by nlinarith [icoB_pos]
    have hz0 : (z : E) 0 = icoB ∨ (z : E) 0 = -icoB :=
      (sq_eq_sq_iff_eq_or_eq_neg).1 (by rw [hz1, hz2] at hn; nlinarith [icoA_sq_add_icoB_sq])
    exact Or.inr (Or.inr ⟨hz0, hz1, Or.inl hz2⟩)
  · have hz2 : (z : E) 2 = 0 := by nlinarith [icoB_pos]
    have hz1 : (z : E) 1 = icoB := by nlinarith [icoA_pos]
    have hz0 : (z : E) 0 = icoA ∨ (z : E) 0 = -icoA :=
      (sq_eq_sq_iff_eq_or_eq_neg).1 (by rw [hz1, hz2] at hn; nlinarith [icoA_sq_add_icoB_sq])
    exact Or.inr (Or.inl ⟨hz0, Or.inl hz1, hz2⟩)

/-- Discrete exactness for every exponent vector of total degree at most five. -/
theorem ico_sphereMonomial_moment (d : Fin 3 → ℕ) (hd : ∑ i, d i ≤ 5) :
    (ico.card : ℝ)⁻¹ * ∑ x ∈ ico, sphereMonomial d x = sphereMoment d := by
  have hd' : d 0 + d 1 + d 2 ≤ 5 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hd
  rw [ico_card, sum_ico]
  simpa [sphereMonomial, sphereMoment, icoVertex_coe,
    Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.exists_fin_succ,
    add_assoc, mul_assoc] using ico_monomial_table (d 0) (d 1) (d 2) hd'

/-- Actual Euclidean coordinate reflections restrict to symmetries of the finite set. -/
theorem ico_coordFlip_mem (i : Fin 3) (x : S2) (hx : x ∈ ico) :
    sphereIso (coordFlip i) x ∈ ico := by
  apply ico_sign_symmetry x _ ?_ hx
  intro j
  simp only [sphereIso_coe, coordFlip_apply]
  split_ifs <;> simp

/-- Cyclic coordinate permutation, as an actual Euclidean linear isometry. -/
def icoCycle : E ≃ₗᵢ[ℝ] E := (coordSwap 0 1).trans (coordSwap 1 2)

@[simp] theorem icoCycle_zero (x : E) : icoCycle x 0 = x 1 := by
  simp [icoCycle, Equiv.swap_apply_def]
@[simp] theorem icoCycle_one (x : E) : icoCycle x 1 = x 2 := by
  simp [icoCycle, Equiv.swap_apply_def]
@[simp] theorem icoCycle_two (x : E) : icoCycle x 2 = x 0 := by
  simp [icoCycle, Equiv.swap_apply_def]

theorem ico_cycle_mem (x : S2) (hx : x ∈ ico) : sphereIso icoCycle x ∈ ico :=
  ico_cyclic_symmetry x _ (by simp) (by simp) (by simp) hx

/-- The vertices integrate every polynomial of total degree at most five exactly. -/
theorem ico_designFor (μ : Measure S2) [IsProbabilityMeasure μ]
    (hμ : OrthogonallyInvariant μ) : DesignFor μ 5 ico :=
  designFor_of_monomial_moments μ hμ ico ico_nonempty ico_sphereMonomial_moment

end Conjecture1030
