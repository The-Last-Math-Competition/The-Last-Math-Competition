import Mathlib.Algebra.Module.Rat
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace TLMC4271
abbrev Aut := ℚ ≃+ ℚ
def identity : Aut := AddEquiv.refl ℚ

/-- Actual divisibility of the additive rational group, in the source's definition. -/
theorem rational_divisible (n : ℕ) (hn : 0<n) (x : ℚ) : ∃ y : ℚ, n • y=x := by
  refine ⟨x/(n : ℚ),?_⟩
  rw [nsmul_eq_mul]
  have h : (n : ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

def doubling : Aut where
  toFun x := 2*x
  invFun x := x/2
  left_inv x := by ring
  right_inv x := by ring
  map_add' x y := by ring

lemma doubling_not_identity : doubling≠identity := by
  intro h
  have he := congrArg (fun f : Aut => f 1) h
  norm_num [doubling,identity] at he

lemma rational_automorphism_scalar (f : Aut) (x : ℚ) : f x=f 1*x := by
  have h := map_rat_smul f x (1 : ℚ)
  simpa [smul_eq_mul,mul_comm] using h

/-- The literal support relative to the identity permutation. -/
def FiniteMovedSupport (f : Aut) : Prop := Set.Finite {x : ℚ | f x≠x}

/-- The actual additive endomorphism f-id and its fixed subgroup. -/
def defect (f : Aut) : ℚ →+ ℚ := f.toAddMonoidHom-AddMonoidHom.id ℚ
def fixed (f : Aut) : AddSubgroup ℚ := (defect f).ker
def FiniteDefectImage (f : Aut) : Prop := Set.Finite (Set.range (defect f))
/-- The standard group-theoretic finitary condition: a finite-index fixed subgroup. -/
def GroupFinitary (f : Aut) : Prop := (fixed f).FiniteIndex

def IdentityOnSomeFiniteIndex (f : Aut) : Prop :=
  ∃ H : AddSubgroup ℚ, H.FiniteIndex ∧ ∀ x∈H, f x=x

lemma fixed_mem (f : Aut) (x : ℚ) : x∈fixed f ↔ f x=x := by
  simp [fixed,defect,sub_eq_zero]

lemma some_finite_index_iff_fixed_index (f : Aut) :
    IdentityOnSomeFiniteIndex f ↔ GroupFinitary f := by
  constructor
  · rintro ⟨H,hH,hfix⟩
    let _ : H.FiniteIndex := hH
    have hle : H≤fixed f := by
      intro x hx
      exact (fixed_mem f x).mpr (hfix x hx)
    exact AddSubgroup.finiteIndex_of_le hle
  · intro h
    exact ⟨fixed f,h,fun x hx => (fixed_mem f x).mp hx⟩

lemma finite_moved_implies_finite_defect (f : Aut) (hf : FiniteMovedSupport f) :
    FiniteDefectImage f := by
  have hfinite : Set.Finite (insert (0 : ℚ) ((defect f) '' {x : ℚ | f x≠x})) :=
    (hf.image (defect f)).insert 0
  apply hfinite.subset
  rintro y ⟨x,rfl⟩
  by_cases hx : f x=x
  · simp [defect,hx]
  · exact Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩

lemma finite_defect_eq_identity (f : Aut) (hf : FiniteDefectImage f) : f=identity := by
  have h1 : f 1=1 := by
    by_contra hne
    have hn : f 1-1≠0 := sub_ne_zero.mpr hne
    have hscale (x : ℚ) : defect f x=(f 1-1)*x := by
      change f x-x=(f 1-1)*x
      rw [rational_automorphism_scalar f x]
      ring
    have hi : Function.Injective (defect f) := by
      intro x y he
      rw [hscale,hscale] at he
      exact mul_left_cancel₀ hn he
    exact (Set.infinite_range_of_injective hi) hf
  ext x
  simp [rational_automorphism_scalar f x,h1,identity]

lemma finite_support_eq_identity (f : Aut) (hf : FiniteMovedSupport f) : f=identity :=
  finite_defect_eq_identity f (finite_moved_implies_finite_defect f hf)

/-- A direct finite-index argument: no finite-quotient-to-image bridge is assumed. -/
lemma finitary_eq_identity (f : Aut) (hf : GroupFinitary f) : f=identity := by
  let _ : (fixed f).FiniteIndex := hf
  have hn : (fixed f).index≠0 := AddSubgroup.FiniteIndex.index_ne_zero
  have hnq : ((fixed f).index : ℚ)≠0 := by exact_mod_cast hn
  ext x
  have hm := (fixed f).nsmul_index_mem x
  have he : f ((fixed f).index • x)=(fixed f).index • x := (fixed_mem f _).mp hm
  rw [map_nsmul,nsmul_eq_mul,nsmul_eq_mul] at he
  simpa [identity] using mul_left_cancel₀ hnq he

lemma fixed_identity : fixed identity=⊤ := by
  ext x
  simp [fixed_mem,identity]

lemma identity_finitary : GroupFinitary identity := by
  unfold GroupFinitary
  rw [fixed_identity]
  infer_instance

lemma identity_finite_support : FiniteMovedSupport identity := by
  simp [FiniteMovedSupport,identity]

lemma identity_finite_defect : FiniteDefectImage identity :=
  finite_moved_implies_finite_defect identity identity_finite_support

theorem group_finitary_iff_finite_defect (f : Aut) :
    GroupFinitary f ↔ FiniteDefectImage f := by
  constructor
  · intro h
    rw [finitary_eq_identity f h]
    exact identity_finite_defect
  · intro h
    rw [finite_defect_eq_identity f h]
    exact identity_finitary

/-- All three finite-support readings have exactly the same singleton here. -/
def Small (f : Aut) : Prop := FiniteMovedSupport f ∨ FiniteDefectImage f ∨ GroupFinitary f

lemma small_iff_identity (f : Aut) : Small f ↔ f=identity := by
  constructor
  · rintro (h|h|h)
    · exact finite_support_eq_identity f h
    · exact finite_defect_eq_identity f h
    · exact finitary_eq_identity f h
  · rintro rfl
    exact Or.inl identity_finite_support

lemma small_set_eq_singleton : {f : Aut | Small f}=({identity} : Set Aut) := by
  ext f
  simp [small_iff_identity]

/-- Every T1 topology, including the topology of any genuine extended metric. -/
theorem doubling_not_in_closure [TopologicalSpace Aut] [T1Space Aut] :
    doubling ∉ closure {f : Aut | Small f} := by
  rw [small_set_eq_singleton,closure_singleton]
  exact doubling_not_identity

/-- Uniform approximation in any true metric on the underlying group is impossible. -/
theorem no_uniform_approximation [MetricSpace ℚ] :
    ¬ ∀ ε : ℝ, 0<ε → ∃ f : Aut, Small f ∧ ∀ x : ℚ, dist (f x) (doubling x)<ε := by
  intro h
  have hp : 0<dist (1 : ℚ) 2 := dist_pos.mpr (by norm_num)
  obtain ⟨f,hf,hclose⟩ := h _ hp
  have he := (small_iff_identity f).mp hf
  subst f
  have hx := hclose 1
  simp [identity,doubling] at hx

/-- If the named metric is instead on the automorphism group, the same obstruction holds. -/
theorem no_automorphism_metric_approximation [MetricSpace Aut] :
    ¬ ∀ ε : ℝ, 0<ε → ∃ f : Aut, Small f ∧ dist f doubling<ε := by
  intro h
  have hp : 0<dist identity doubling := dist_pos.mpr doubling_not_identity.symm
  obtain ⟨f,hf,hclose⟩ := h _ hp
  rw [(small_iff_identity f).mp hf] at hclose
  exact (lt_irrefl _) hclose

theorem literal_uniform_claim_false [MetricSpace ℚ] :
    ¬ ∀ g : Aut, ∀ ε : ℝ, 0<ε →
      ∃ f : Aut, FiniteMovedSupport f ∧ ∀ x : ℚ, dist (f x) (g x)<ε := by
  intro h
  apply no_uniform_approximation
  intro ε hε
  obtain ⟨f,hf,hclose⟩ := h doubling ε hε
  exact ⟨f,Or.inl hf,hclose⟩

theorem finitary_uniform_claim_false [MetricSpace ℚ] :
    ¬ ∀ g : Aut, ∀ ε : ℝ, 0<ε →
      ∃ f : Aut, GroupFinitary f ∧ ∀ x : ℚ, dist (f x) (g x)<ε := by
  intro h
  apply no_uniform_approximation
  intro ε hε
  obtain ⟨f,hf,hclose⟩ := h doubling ε hε
  exact ⟨f,Or.inr (Or.inr hf),hclose⟩

theorem standard_finitary_uniform_claim_false [MetricSpace ℚ] :
    ¬ ∀ g : Aut, ∀ ε : ℝ, 0<ε →
      ∃ f : Aut, IdentityOnSomeFiniteIndex f ∧ ∀ x : ℚ, dist (f x) (g x)<ε := by
  intro h
  apply finitary_uniform_claim_false
  intro g ε hε
  obtain ⟨f,hf,hclose⟩ := h g ε hε
  exact ⟨f,(some_finite_index_iff_fixed_index f).mp hf,hclose⟩

end TLMC4271
