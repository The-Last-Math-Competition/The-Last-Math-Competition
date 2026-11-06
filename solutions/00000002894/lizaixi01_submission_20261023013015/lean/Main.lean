import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace TLMC2894
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000
open scoped LinearAlgebra.Projectivization
variable {K : Type*} [Field K] [Fintype K]
abbrev V (K : Type*) := Fin 3 → K
abbrev Point (K : Type*) [Field K] := Projectivization K (V K)
noncomputable instance : Fintype (Point K) := Fintype.ofFinite _

def vec (i : Fin 3) (t : Kˣ) : V K :=
  if i=0 then ![0,1,(t:K)] else if i=1 then ![(t:K),0,1] else ![1,(t:K),0]
lemma vec_ne_zero (i : Fin 3) (t : Kˣ) : vec i t ≠ 0 := by
  fin_cases i <;> simp [vec, funext_iff, Fin.forall_fin_succ]
def point (x : Fin 3 × Kˣ) : Point K := Projectivization.mk K (vec x.1 x.2) (vec_ne_zero _ _)
lemma point_injective : Function.Injective (point (K:=K)) := by
  rintro ⟨i,t⟩ ⟨j,u⟩ h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec, Pi.smul_apply, smul_eq_mul, Units.smul_def] at h0
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec, Pi.smul_apply, smul_eq_mul, Units.smul_def] at h1
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec, Pi.smul_apply, smul_eq_mul, Units.smul_def] at h2
  all_goals simp_all only [Units.val_one,one_mul,mul_one]
  all_goals apply Prod.ext
  all_goals first | rfl | skip
  all_goals apply Units.ext
  all_goals first | assumption | (symm; assumption)
noncomputable def B : Finset (Point K) := by
  classical
  exact Finset.univ.image point
lemma mem_B (p : Point K) : p ∈ B ↔ ∃ i t, p = point (i,t) := by
  classical
  simp only [B,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,t⟩,h⟩; exact ⟨i,t,h.symm⟩
  · rintro ⟨i,t,rfl⟩; exact ⟨(i,t),rfl⟩
lemma B_card : (B (K:=K)).card = 3 * (Fintype.card K - 1) := by
  classical
  rw [B,Finset.card_image_of_injective _ point_injective]
  simp [Fintype.card_units]

def form (a : V K) : V K →ₗ[K] K where
  toFun v := a 0 * v 0 + a 1 * v 1 + a 2 * v 2
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
noncomputable def line (a : V K) : Finset (Point K) := by
  classical
  exact Finset.univ.filter fun p => p ∈ (form a).ker.projectivization
lemma point_on (a : V K) (i : Fin 3) (t : Kˣ) :
    point (i,t) ∈ line a ↔ form a (vec i t) = 0 := by
  classical
  simp [line,point,Submodule.mk_mem_projectivization_iff,LinearMap.mem_ker]
lemma form_surjective (a : V K) (ha : a ≠ 0) : Function.Surjective (form a) := by
  have hex : ∃ i, a i ≠ 0 := by contrapose! ha; ext i; exact ha i
  obtain ⟨i,hi⟩ := hex
  intro c
  refine ⟨Pi.single i (c / a i), ?_⟩
  have he : a i * (c / a i) = c := by field_simp [hi]
  fin_cases i <;> simpa [form,Pi.single_apply] using he
lemma kernel_rank (a : V K) (ha : a ≠ 0) : Module.finrank K (form a).ker = 2 := by
  have h := (form a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (form_surjective a ha)] at h
  simp only [finrank_top,Module.finrank_self,Module.finrank_pi,Module.finrank_self,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at h
  omega
noncomputable def restrictPoint (a : V K)
    (p : {p : Point K // p ∈ (form a).ker.projectivization}) :
    Projectivization K (form a).ker :=
  Projectivization.mk K ⟨p.val.rep, by
    apply (Submodule.mk_mem_projectivization_iff _ p.val.rep_nonzero).mp
    rw [p.val.mk_rep]; exact p.property⟩ (by
      intro h; exact p.val.rep_nonzero (congrArg Subtype.val h))
lemma restrictPoint_injective (a : V K) : Function.Injective (restrictPoint a) := by
  intro p q h
  apply Subtype.ext
  have he := congrArg (Projectivization.map (form a).ker.subtype
    (by intro x y h; exact Subtype.ext h)) h
  change Projectivization.mk K p.val.rep p.val.rep_nonzero =
    Projectivization.mk K q.val.rep q.val.rep_nonzero at he
  simpa only [Projectivization.mk_rep] using he
lemma line_card_le (a : V K) (ha : a ≠ 0) : (line a).card ≤ Fintype.card K + 1 := by
  classical
  have hi := Nat.card_le_card_of_injective (restrictPoint a) (restrictPoint_injective a)
  have hc := Projectivization.card_of_finrank K (V:=(form a).ker) (n:=2) (kernel_rank a ha)
  have he : (line a).card = Nat.card {p : Point K // p ∈ (form a).ker.projectivization} := by
    simp [line,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [he]
  refine hi.trans_eq ?_
  simpa [Nat.card_eq_fintype_card,Finset.sum_range_succ,Nat.add_comm] using hc

/-- Standard homogeneous-coordinate lines are all kernels of nonzero linear forms. -/
def IsBlocking (S : Finset (Point K)) : Prop := ∀ a : V K, a ≠ 0 → ∃ p ∈ S, p ∈ line a
def IsMinimalBlocking (S : Finset (Point K)) : Prop :=
  IsBlocking S ∧ ∀ T ⊆ S, IsBlocking T → S ⊆ T
def IsNontrivial (S : Finset (Point K)) : Prop := ∀ a : V K, a ≠ 0 → ¬ line a ⊆ S
def IsRedei (S : Finset (Point K)) : Prop :=
  by
    classical
    exact ∃ a : V K, a ≠ 0 ∧ (S \ line a).card = Fintype.card K

lemma B_blocking : IsBlocking (B (K:=K)) := by
  classical
  intro a ha
  have hp (i : Fin 3) (t : Kˣ) (h : form a (vec i t)=0) :
      ∃ p ∈ B (K:=K), p ∈ line a :=
    ⟨point (i,t),(mem_B _).mpr ⟨i,t,rfl⟩,(point_on _ _ _).mpr h⟩
  by_cases h0 : a 0=0 <;> by_cases h1 : a 1=0 <;> by_cases h2 : a 2=0
  · exact False.elim (ha (by ext i; fin_cases i <;> assumption))
  · exact hp 2 1 (by simp [form,vec,h0,h1])
  · exact hp 1 1 (by simp [form,vec,h0,h2])
  · apply hp 0 (Units.mk0 (-a 1 / a 2) (div_ne_zero (neg_ne_zero.mpr h1) h2))
    simp [form,vec]; field_simp; ring
  · exact hp 0 1 (by simp [form,vec,h1,h2])
  · apply hp 1 (Units.mk0 (-a 2 / a 0) (div_ne_zero (neg_ne_zero.mpr h2) h0))
    simp [form,vec]; field_simp; ring
  · apply hp 2 (Units.mk0 (-a 0 / a 1) (div_ne_zero (neg_ne_zero.mpr h0) h1))
    simp [form,vec]; field_simp; ring
  · apply hp 2 (Units.mk0 (-a 0 / a 1) (div_ne_zero (neg_ne_zero.mpr h0) h1))
    simp [form,vec]; field_simp; ring

def tangent (i : Fin 3) (t : Kˣ) : V K :=
  if i=0 then ![0,-(t:K),1] else if i=1 then ![1,0,-(t:K)] else ![-(t:K),1,0]
lemma tangent_ne_zero (i : Fin 3) (t : Kˣ) : tangent i t ≠ 0 := by
  fin_cases i <;> simp [tangent,funext_iff,Fin.forall_fin_succ]
lemma tangent_iff (i j : Fin 3) (t u : Kˣ) :
    form (tangent i t) (vec j u)=0 ↔ i=j ∧ t=u := by
  fin_cases i <;> fin_cases j <;>
    simp [form,tangent,vec,neg_add_eq_zero,add_neg_eq_zero,Units.ext_iff,eq_comm]
lemma B_tangent (p : Point K) (hp : p ∈ B) :
    ∃ a : V K, a ≠ 0 ∧ p ∈ line a ∧ ∀ z ∈ B, z ∈ line a → z=p := by
  classical
  obtain ⟨i,t,rfl⟩ := (mem_B p).mp hp
  refine ⟨tangent i t,tangent_ne_zero _ _,?_,?_⟩
  · rw [point_on,tangent_iff]; exact ⟨rfl,rfl⟩
  · intro z hz hline
    obtain ⟨j,u,rfl⟩ := (mem_B z).mp hz
    obtain ⟨rfl,rfl⟩ := (tangent_iff i j t u).mp ((point_on _ _ _).mp hline)
    rfl
lemma B_minimal : IsMinimalBlocking (B (K:=K)) := by
  classical
  refine ⟨B_blocking,?_⟩
  intro T hT hblock p hp
  obtain ⟨a,ha,hpL,ht⟩ := B_tangent p hp
  obtain ⟨z,hz,hzL⟩ := hblock a ha
  have he := ht z (hT hz) hzL
  simpa [he] using hz
lemma mk_on (a v : V K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ line a ↔ form a v = 0 := by
  classical
  simp [line,Submodule.mk_mem_projectivization_iff,LinearMap.mem_ker]
lemma single_ne_zero (i : Fin 3) : (Pi.single i (1:K) : V K) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp at hi
lemma single_not_B (i : Fin 3) :
    Projectivization.mk K (Pi.single i 1) (single_ne_zero i) ∉ B := by
  intro hb
  obtain ⟨j,t,h⟩ := (mem_B _).mp hb
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec,Pi.single_apply,Pi.smul_apply,smul_eq_mul,Units.smul_def] at h0
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec,Pi.single_apply,Pi.smul_apply,smul_eq_mul,Units.smul_def] at h1
  all_goals try norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec,Pi.single_apply,Pi.smul_apply,smul_eq_mul,Units.smul_def] at h2
  all_goals simp [show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide] at h2
lemma all_nonzero_not_B (v : V K) (hv : ∀ i, v i ≠ 0) :
    Projectivization.mk K v (by intro h; exact hv 0 (congrFun h 0)) ∉ B := by
  intro hb
  obtain ⟨i,t,h⟩ := (mem_B _).mp hb
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  have he := congrFun hc i
  have hz : vec i t i = 0 := by fin_cases i <;> simp [vec]
  simp only [Pi.smul_apply,hz,smul_zero] at he
  exact hv i he.symm
lemma B_nontrivial [CharP K 3] : IsNontrivial (B (K:=K)) := by
  classical
  intro a ha hsub
  have hs (i : Fin 3) (hi : a i=0) : False := by
    apply single_not_B (K:=K) i
    apply hsub
    rw [mk_on]
    fin_cases i <;> simpa [form,Pi.single_apply] using hi
  by_cases h0 : a 0=0
  · exact hs 0 h0
  by_cases h1 : a 1=0
  · exact hs 1 h1
  by_cases h2 : a 2=0
  · exact hs 2 h2
  let v : V K := ![(a 0)⁻¹,(a 1)⁻¹,(a 2)⁻¹]
  have hv : ∀ i, v i ≠ 0 := by
    intro i; fin_cases i <;> simp [v,h0,h1,h2]
  apply all_nonzero_not_B v hv
  apply hsub
  rw [mk_on]
  have hthree : (3:K)=0 := CharP.cast_eq_zero K 3
  convert hthree using 1
  norm_num [form,v,h0,h1,h2,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
lemma B_not_redei (hq : 4 < Fintype.card K) : ¬ IsRedei (B (K:=K)) := by
  classical
  rintro ⟨a,ha,h⟩
  have hl := line_card_le a ha
  have hi : ((B (K:=K)) ∩ line a).card ≤ (line a).card :=
    Finset.card_le_card Finset.inter_subset_right
  have he := Finset.card_sdiff_add_card_inter (B (K:=K)) (line a)
  rw [B_card,h] at he
  omega

abbrev F9 := GaloisField 3 2
noncomputable instance : Fintype F9 := Fintype.ofFinite _
lemma F9_card : Fintype.card F9 = 9 := by
  have h := GaloisField.card 3 (n:=2) (by decide)
  simpa [Nat.card_eq_fintype_card] using h
lemma three_not_square : ¬ IsSquare (3:ℕ) := by
  rintro ⟨n,hn⟩
  have : n < 2 := by nlinarith
  interval_cases n <;> norm_num at hn
/-- Concrete failure in order Q=9=3^2, with non-square q=3. -/
theorem counterexample :
    (Fintype.card F9=3^2) ∧ ¬ IsSquare (3:ℕ) ∧
    (B (K:=F9)).card=24 ∧ IsMinimalBlocking (B (K:=F9)) ∧
    IsNontrivial (B (K:=F9)) ∧ ¬ IsRedei (B (K:=F9)) := by
  refine ⟨by norm_num [F9_card],three_not_square,?_,B_minimal,B_nontrivial,?_⟩
  · rw [B_card,F9_card]
  · exact B_not_redei (by norm_num [F9_card])
end TLMC2894
