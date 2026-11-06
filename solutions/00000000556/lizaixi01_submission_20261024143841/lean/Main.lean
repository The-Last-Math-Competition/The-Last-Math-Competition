import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
The four-leaf star path algebra over Q.  The necessary implication
HH^1(A)=0 => representation-finite is independent of any meaning of rigid.
No self-injectivity or alternative rigidity premise is substituted.
-/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ModuleCat.Algebra TensorProduct

namespace TLMC556

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Vertex := Fin 5
abbrev Arrow := Fin 4
abbrev Diagonal := Vertex → ℚ
abbrev ArrowSpace := Arrow → ℚ

instance arrow_left : Module Diagonal ArrowSpace where
  smul r m := fun i => r 0 * m i
  one_smul m := by funext i; change (1 : ℚ) * m i = m i; ring
  mul_smul r s m := by funext i; exact mul_assoc _ _ _
  smul_zero r := by funext i; exact mul_zero _
  smul_add r m n := by funext i; exact mul_add _ _ _
  add_smul r s m := by funext i; exact add_mul _ _ _
  zero_smul m := by funext i; exact zero_mul _

instance arrow_right : Module Diagonalᵐᵒᵖ ArrowSpace where
  smul r m := fun i => r.unop i.succ * m i
  one_smul m := by funext i; change (1 : ℚ) * m i = m i; ring
  mul_smul r s m := by
    funext i
    change s.unop i.succ * r.unop i.succ * m i = r.unop i.succ * (s.unop i.succ * m i)
    ring
  smul_zero r := by funext i; exact mul_zero _
  smul_add r m n := by funext i; exact mul_add _ _ _
  add_smul r s m := by funext i; exact add_mul _ _ _
  zero_smul m := by funext i; exact zero_mul _

instance arrow_comm : SMulCommClass Diagonal Diagonalᵐᵒᵖ ArrowSpace where
  smul_comm r s m := by
    funext i
    change r 0 * (s.unop i.succ * m i) = s.unop i.succ * (r 0 * m i)
    ring

instance arrow_left_tower : IsScalarTower ℚ Diagonal ArrowSpace where
  smul_assoc c r m := by
    funext i
    change (c * r 0) * m i = c * (r 0 * m i)
    ring

instance arrow_right_tower : IsScalarTower ℚ Diagonalᵐᵒᵖ ArrowSpace where
  smul_assoc c r m := by
    funext i
    change (c * r.unop i.succ) * m i = c * (r.unop i.succ * m i)
    ring

@[simp] theorem left_smul_apply (r : Diagonal) (m : ArrowSpace) (i : Arrow) :
    (r • m) i = r 0 * m i := rfl

@[simp] theorem right_smul_apply (r : Diagonalᵐᵒᵖ) (m : ArrowSpace) (i : Arrow) :
    (r • m) i = r.unop i.succ * m i := rfl

abbrev A := TrivSqZeroExt Diagonal ArrowSpace

instance algebra_finite : Module.Finite ℚ A :=
  inferInstanceAs (Module.Finite ℚ (Diagonal × ArrowSpace))

theorem algebra_dimension : Module.finrank ℚ A = 9 := by
  change Module.finrank ℚ (Diagonal × ArrowSpace) = 9
  simp [Diagonal, ArrowSpace, Vertex, Arrow, Module.finrank_prod]

theorem multiplication_diagonal (a b : A) (i : Vertex) :
    (a * b).fst i = a.fst i * b.fst i := rfl

theorem multiplication_arrow (a b : A) (i : Arrow) :
    (a * b).snd i = a.fst 0 * b.snd i + a.snd i * b.fst i.succ := by
  change a.fst 0 * b.snd i + b.fst i.succ * a.snd i = _
  ring

def vertex (i : Vertex) : A := TrivSqZeroExt.inl (Pi.single i 1)
def arrow (i : Arrow) : A := TrivSqZeroExt.inr (Pi.single i 1)

theorem vertex_mul (i j : Vertex) :
    vertex i * vertex j = if i = j then vertex i else 0 := by
  by_cases h : i = j
  · subst j
    ext k <;> simp [vertex, Pi.single_apply]
  · simp only [if_neg h]
    apply TrivSqZeroExt.ext
    · funext k
      by_cases hk : k = i
      · subst k
        simp [vertex, h]
      · simp [vertex, Pi.single_apply, hk]
    · ext k; simp [vertex]

theorem vertex_square (i : Vertex) : vertex i * vertex i = vertex i := by
  simp [vertex_mul]

theorem vertex_arrow (i : Vertex) (j : Arrow) :
    vertex i * arrow j = if i = 0 then arrow j else 0 := by
  by_cases hi : i = 0
  · subst i
    ext k <;> simp [vertex, arrow]
  · simp only [if_neg hi]
    ext k <;> simp [vertex, arrow, Pi.single_apply, Ne.symm hi]

theorem arrow_vertex (i : Arrow) (j : Vertex) :
    arrow i * vertex j = if j = i.succ then arrow i else 0 := by
  by_cases hj : j = i.succ
  · subst j
    apply TrivSqZeroExt.ext
    · ext k; simp [arrow, vertex]
    · funext k
      by_cases hk : k = i
      · subst k; simp [vertex, arrow]
      · simp [vertex, arrow, hk]
  · simp only [if_neg hj]
    apply TrivSqZeroExt.ext
    · ext k; simp [arrow, vertex]
    · funext k
      by_cases hk : k = i
      · subst k; simp [vertex, arrow, Ne.symm hj]
      · simp [vertex, arrow, Pi.single_apply, hk]

theorem arrow_mul (i j : Arrow) : arrow i * arrow j = 0 :=
  TrivSqZeroExt.inr_mul_inr _ _ _

theorem vertex_sum : (∑ i : Vertex, vertex i) = 1 := by
  ext j <;> fin_cases j <;> norm_num [Fin.sum_univ_succ, vertex, Pi.single_apply, Fin.ext_iff]

theorem algebra_decomposition (x : A) :
    x = (∑ i : Vertex, x.fst i • vertex i) + ∑ i : Arrow, x.snd i • arrow i := by
  ext j <;> fin_cases j <;> norm_num [Fin.sum_univ_succ, vertex, arrow, Pi.single_apply, Fin.ext_iff] <;> rfl

theorem linearMap_ext_basis {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f g : A →ₗ[ℚ] M) (hv : ∀ i, f (vertex i) = g (vertex i))
    (ha : ∀ i, f (arrow i) = g (arrow i)) : f = g := by
  ext x
  conv_lhs => rw [algebra_decomposition x]
  conv_rhs => rw [algebra_decomposition x]
  simp only [map_add, map_sum, map_smul]
  simp_rw [hv, ha]

theorem radical_form (x : A) (hx : ∀ i, x.fst i = 0) :
    x = TrivSqZeroExt.inr x.snd := by
  apply TrivSqZeroExt.ext
  · exact funext hx
  · rfl

theorem radical_mul_zero (x y : A) (hx : ∀ i, x.fst i = 0) (hy : ∀ i, y.fst i = 0) :
    x * y = 0 := by
  rw [radical_form x hx, radical_form y hy]
  exact TrivSqZeroExt.inr_mul_inr _ _ _

abbrev C1 := A →ₗ[ℚ] A
abbrev C2 := A →ₗ[ℚ] A →ₗ[ℚ] A

/-- The actual degree-zero Hochschild coboundary. -/
def inner (h : A) : C1 where
  toFun x := x * h - h * x
  map_add' x y := by simp only [add_mul, mul_add]; abel
  map_smul' c x := by
    change (c • x) * h - h * (c • x) = c • (x * h - h * x)
    simp only [smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]

def coboundary0 : A →ₗ[ℚ] C1 where
  toFun := inner
  map_add' h k := by
    apply LinearMap.ext
    intro x
    change x * (h + k) - (h + k) * x = (x * h - h * x) + (x * k - k * x)
    noncomm_ring
  map_smul' c h := by
    apply LinearMap.ext
    intro x
    change x * (c • h) - (c • h) * x = c • (x * h - h * x)
    simp only [Algebra.mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The complete degree-one bar coboundary, with both regular bimodule actions. -/
def coboundary1 : C1 →ₗ[ℚ] C2 where
  toFun f :=
    { toFun := fun x =>
        { toFun := fun y => x * f y - f (x * y) + f x * y
          map_add' y z := by simp only [map_add, mul_add]; abel
          map_smul' c y := by
            simp only [map_smul, Algebra.mul_smul_comm,
              smul_sub, smul_add, RingHom.id_apply] }
      map_add' x z := by
        apply LinearMap.ext
        intro y
        change (x + z) * f y - f ((x + z) * y) + f (x + z) * y =
          (x * f y - f (x * y) + f x * y) + (z * f y - f (z * y) + f z * y)
        simp only [map_add, add_mul]
        abel
      map_smul' c x := by
        apply LinearMap.ext
        intro y
        change (c • x) * f y - f ((c • x) * y) + f (c • x) * y =
          c • (x * f y - f (x * y) + f x * y)
        simp only [map_smul, smul_mul_assoc, smul_sub, smul_add] }
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change x * (f y + g y) - (f (x * y) + g (x * y)) + (f x + g x) * y =
      (x * f y - f (x * y) + f x * y) + (x * g y - g (x * y) + g x * y)
    noncomm_ring
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change x * (c • f y) - c • f (x * y) + (c • f x) * y =
      c • (x * f y - f (x * y) + f x * y)
    simp only [Algebra.mul_smul_comm, smul_mul_assoc, smul_sub, smul_add]

theorem coboundary_squared (h : A) : coboundary1 (coboundary0 h) = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change x * (y * h - h * y) - (x * y * h - h * (x * y)) +
    (x * h - h * x) * y = 0
  noncomm_ring

def DerCondition (f : C1) : Prop := ∀ x y, f (x * y) = x * f y + f x * y

theorem cocycle_iff_derivation (f : C1) :
    f ∈ LinearMap.ker coboundary1 ↔ DerCondition f := by
  constructor
  · intro h x y
    have he := congrArg (fun g : C2 => g x y) h
    change x * f y - f (x * y) + f x * y = 0 at he
    change f (x * y) = _
    exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, add_right_comm] using he)).symm
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change x * f y - f (x * y) + f x * y = 0
    rw [h x y]
    abel

def cochain2TensorEquiv : C2 ≃ₗ[ℚ] (A ⊗[ℚ] A →ₗ[ℚ] A) :=
  TensorProduct.lift.equiv (RingHom.id ℚ) A A A

theorem coboundary1_tensor_formula (f : C1) (x y : A) :
    cochain2TensorEquiv (coboundary1 f) (TensorProduct.tmul ℚ x y) =
      x * f y - f (x * y) + f x * y := by
  exact TensorProduct.lift.equiv_apply (RingHom.id ℚ) A A A (coboundary1 f) x y

theorem deriv_vertex_diagonal (f : C1) (hf : DerCondition f) (i j : Vertex) :
    (f (vertex i)).fst j = 0 := by
  have h := congrArg (fun x : A => x.fst j) (hf (vertex i) (vertex i))
  rw [vertex_square] at h
  change (f (vertex i)).fst j =
    (vertex i).fst j * (f (vertex i)).fst j +
      (f (vertex i)).fst j * (vertex i).fst j at h
  by_cases hij : i = j
  · subst j
    simp [vertex] at h
    simpa [vertex] using h
  · simpa [vertex, Pi.single_apply, hij, Ne.symm hij] using h

theorem corner_is_arrow (i : Arrow) (x : A)
    (hl : vertex 0 * x = x) (hr : x * vertex i.succ = x) :
    x = x.snd i • arrow i := by
  apply TrivSqZeroExt.ext
  · ext j
    have hleft := congrArg (fun a : A => a.fst j) hl
    have hright := congrArg (fun a : A => a.fst j) hr
    by_cases hj : j = 0
    · subst j
      simpa [vertex, arrow, Pi.single_apply] using hright.symm
    · simpa [vertex, arrow, Pi.single_apply, hj, Ne.symm hj] using hleft.symm
  · ext j
    have h := congrArg (fun a : A => a.snd j) hr
    by_cases hij : i = j
    · subst j
      simp [arrow]
    · simpa [vertex, arrow, multiplication_arrow, Pi.single_apply, hij,
        Ne.symm hij, Fin.succ_inj] using h.symm

theorem deriv_arrow_formula (f : C1) (hf : DerCondition f) (i : Arrow) :
    f (arrow i) = (f (arrow i)).snd i • arrow i := by
  apply corner_is_arrow
  · have h := hf (vertex 0) (arrow i)
    rw [vertex_arrow, if_pos rfl] at h
    rw [radical_mul_zero _ _ (deriv_vertex_diagonal f hf 0) (by intro j; rfl), add_zero] at h
    exact h.symm
  · have h := hf (arrow i) (vertex i.succ)
    rw [arrow_vertex, if_pos rfl] at h
    rw [radical_mul_zero _ _ (by intro j; rfl) (deriv_vertex_diagonal f hf i.succ), zero_add] at h
    exact h.symm

/-- The correcting element is obtained from the actual values of the derivation. -/
def corrector (f : C1) : A :=
  ⟨fun i => if h : i = 0 then 0 else (f (arrow ⟨i.val - 1, by omega⟩)).snd ⟨i.val - 1, by omega⟩,
   (f (vertex 0)).snd⟩

theorem corrector_center (f : C1) : (corrector f).fst 0 = 0 := by
  simp [corrector]

theorem corrector_leaf (f : C1) (i : Arrow) :
    (corrector f).fst i.succ = (f (arrow i)).snd i := by
  simp [corrector]

theorem inner_corrector_vertex (f : C1) (hf : DerCondition f) (i : Vertex) :
    inner (corrector f) (vertex i) = f (vertex i) := by
  apply TrivSqZeroExt.ext
  · ext j
    change (vertex i).fst j * (corrector f).fst j -
      (corrector f).fst j * (vertex i).fst j = (f (vertex i)).fst j
    rw [deriv_vertex_diagonal f hf i j]
    ring
  · ext j
    change (vertex i * corrector f).snd j - (corrector f * vertex i).snd j = _
    rw [multiplication_arrow, multiplication_arrow]
    by_cases hi : i = 0
    · subst i
      simp [vertex, corrector]
    · have h := congrArg (fun x : A => x.snd j) (hf (vertex 0) (vertex i))
      rw [vertex_mul, if_neg (Ne.symm hi), map_zero] at h
      simp [vertex, corrector, Pi.single_apply, Ne.symm hi] at h ⊢
      linarith

theorem inner_corrector_arrow (f : C1) (hf : DerCondition f) (i : Arrow) :
    inner (corrector f) (arrow i) = f (arrow i) := by
  rw [deriv_arrow_formula f hf i]
  apply TrivSqZeroExt.ext
  · ext j
    simp [inner, arrow]
  · ext j
    change (arrow i * corrector f).snd j - (corrector f * arrow i).snd j = _
    rw [multiplication_arrow, multiplication_arrow]
    by_cases hj : j = i
    · subst j
      simp [arrow, corrector_center, corrector_leaf]
    · simp [arrow, corrector_center, hj]

theorem every_derivation_inner (f : C1) (hf : DerCondition f) :
    inner (corrector f) = f :=
  linearMap_ext_basis _ _ (inner_corrector_vertex f hf) (inner_corrector_arrow f hf)

def hochschildLow : ShortComplex (ModuleCat ℚ) where
  X₁ := ModuleCat.of ℚ A
  X₂ := ModuleCat.of ℚ C1
  X₃ := ModuleCat.of ℚ C2
  f := ModuleCat.ofHom coboundary0
  g := ModuleCat.ofHom coboundary1
  zero := by
    apply ModuleCat.hom_ext
    change coboundary1.comp coboundary0 = 0
    apply LinearMap.ext
    intro h
    exact coboundary_squared h

abbrev HH1 := hochschildLow.homology

theorem hochschild_exact : hochschildLow.Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range coboundary0 = LinearMap.ker coboundary1
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    exact coboundary_squared h
  · intro f hf
    exact ⟨corrector f, every_derivation_inner f ((cocycle_iff_derivation f).mp hf)⟩

theorem HH1_zero : IsZero HH1 :=
  hochschildLow.exact_iff_isZero_homology.mp hochschild_exact


/-! The complete basis is identified with all actual paths of the star quiver. -/

instance starQuiver : Quiver Vertex where
  Hom a b := PLift (a ≠ 0 ∧ b = 0)

abbrev StarPath (a b : Vertex) := @Quiver.Path Vertex starQuiver a b
abbrev AllPath := Σ a : Vertex, Σ b : Vertex, StarPath a b

def singlePath (i : Arrow) : StarPath i.succ 0 :=
  Quiver.Path.nil.cons ⟨by simp⟩

theorem path_shape {a b : Vertex} (p : StarPath a b) :
    (p.length = 0 ∧ a = b) ∨ (p.length = 1 ∧ a ≠ 0 ∧ b = 0) := by
  induction p with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons b c p e ih =>
    have he : b ≠ 0 ∧ c = 0 := e.down
    rcases ih with ⟨hlen, hab⟩ | ⟨_, _, hb⟩
    · exact Or.inr ⟨by simp [hlen], by simpa [hab] using he.1, he.2⟩
    · exact False.elim (he.1 hb)

theorem path_unique {a b : Vertex} (p q : StarPath a b) : p = q := by
  induction p with
  | nil =>
    have hq : q.length = 0 := by
      rcases path_shape q with h | h
      · exact h.1
      · exact False.elim (h.2.1 h.2.2)
    exact (q.eq_nil_of_length_zero hq).symm
  | @cons b c p e ih =>
    have he : b ≠ 0 ∧ c = 0 := e.down
    have hp : a = b := by
      rcases path_shape p with h | h
      · exact h.2
      · exact False.elim (he.1 h.2.2)
    cases q with
    | nil => exact False.elim (he.1 (hp.symm.trans he.2))
    | cons q f =>
      rcases path_shape q with ⟨_, hq⟩ | ⟨_, _, hbad⟩
      · have hbb := hp.symm.trans hq
        cases hbb
        have hpq := ih q
        subst q
        have hef : e = f := by
          change @Eq (PLift (b ≠ 0 ∧ c = 0)) e f
          exact Subsingleton.elim _ _
        rw [hef]
      · exact False.elim (f.down.1 hbad)

def leafIndex (a : Vertex) (ha : a ≠ 0) : Arrow := ⟨a.val - 1, by
  have hval : a.val ≠ 0 := fun h => ha (Fin.ext h)
  omega⟩

theorem leafIndex_source (a : Vertex) (ha : a ≠ 0) : (leafIndex a ha).succ = a := by
  apply Fin.ext
  have hval : a.val ≠ 0 := fun h => ha (Fin.ext h)
  change a.val - 1 + 1 = a.val
  omega

@[simp] theorem leafIndex_succ (i : Arrow) (h : i.succ ≠ (0 : Vertex)) :
    leafIndex i.succ h = i := by
  apply Fin.ext
  simp [leafIndex]

def pathFor : Vertex ⊕ Arrow → AllPath
  | Sum.inl i => ⟨i, i, Quiver.Path.nil⟩
  | Sum.inr i => ⟨i.succ, 0, singlePath i⟩

theorem pathFor_injective : Function.Injective pathFor := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      exact congrArg Sum.inl (congrArg (fun p : AllPath => p.1) h)
    | inr j =>
      have ha : i = j.succ := congrArg (fun p : AllPath => p.1) h
      have hb : i = 0 := congrArg (fun p : AllPath => p.2.1) h
      have hc := ha.symm.trans hb
      simp at hc
  | inr i =>
    cases y with
    | inl j =>
      have ha : i.succ = j := congrArg (fun p : AllPath => p.1) h
      have hb : (0 : Vertex) = j := congrArg (fun p : AllPath => p.2.1) h
      have hc := ha.trans hb.symm
      simp at hc
    | inr j =>
      have ha : i.succ = j.succ := congrArg (fun p : AllPath => p.1) h
      exact congrArg Sum.inr (Fin.succ_inj.mp ha)

theorem pathFor_surjective : Function.Surjective pathFor := by
  rintro ⟨a, b, p⟩
  rcases path_shape p with ⟨_, hab⟩ | ⟨_, ha, hb⟩
  · subst b
    refine ⟨Sum.inl a, ?_⟩
    exact congrArg (fun q : StarPath a a => (⟨a, a, q⟩ : AllPath))
      (path_unique Quiver.Path.nil p)
  · subst b
    obtain ⟨i, rfl⟩ : ∃ i : Arrow, i.succ = a := ⟨leafIndex a ha, leafIndex_source a ha⟩
    refine ⟨Sum.inr i, ?_⟩
    exact congrArg (fun q : StarPath i.succ 0 => (⟨i.succ, 0, q⟩ : AllPath))
      (path_unique (singlePath i) p)

def pathIndexEquiv : (Vertex ⊕ Arrow) ≃ AllPath :=
  Equiv.ofBijective pathFor ⟨pathFor_injective, pathFor_surjective⟩

instance allPathFintype : Fintype AllPath := Fintype.ofEquiv (Vertex ⊕ Arrow) pathIndexEquiv

theorem actual_path_count : Fintype.card AllPath = 9 := by
  rw [← Fintype.card_congr pathIndexEquiv]
  simp [Vertex, Arrow]

def algebraBasis : Module.Basis (Vertex ⊕ Arrow) ℚ A := by
  change Module.Basis (Vertex ⊕ Arrow) ℚ (Diagonal × ArrowSpace)
  exact (Pi.basisFun ℚ Vertex).prod (Pi.basisFun ℚ Arrow)

theorem algebraBasis_vertex (i : Vertex) : algebraBasis (Sum.inl i) = vertex i := by
  change ((Pi.basisFun ℚ Vertex).prod (Pi.basisFun ℚ Arrow)) (Sum.inl i) =
    (Pi.single i 1, 0)
  apply Prod.ext <;> simp

theorem algebraBasis_arrow (i : Arrow) : algebraBasis (Sum.inr i) = arrow i := by
  change ((Pi.basisFun ℚ Vertex).prod (Pi.basisFun ℚ Arrow)) (Sum.inr i) =
    (0, Pi.single i 1)
  apply Prod.ext <;> simp

def pathBasis : Module.Basis AllPath ℚ A := algebraBasis.reindex pathIndexEquiv

theorem pathBasis_pathFor (i : Vertex ⊕ Arrow) : pathBasis (pathFor i) = algebraBasis i := by
  rw [pathBasis, Module.Basis.reindex_apply]
  change algebraBasis (pathIndexEquiv.symm (pathIndexEquiv i)) = algebraBasis i
  rw [Equiv.symm_apply_apply]

def pathElement {a b : Vertex} (p : StarPath a b) : A := by
  induction p with
  | nil => exact vertex a
  | @cons b c p e ih => exact arrow (leafIndex b e.down.1) * ih

@[simp] theorem pathElement_nil (a : Vertex) :
    pathElement (Quiver.Path.nil : StarPath a a) = vertex a := rfl

@[simp] theorem pathElement_cons {a b c : Vertex} (p : StarPath a b)
    (e : @Quiver.Hom Vertex starQuiver b c) :
    pathElement (p.cons e) = arrow (leafIndex b e.down.1) * pathElement p := rfl

@[simp] theorem pathElement_single (i : Arrow) : pathElement (singlePath i) = arrow i := by
  simp [singlePath, arrow_vertex]

theorem pathBasis_is_actual_path (p : AllPath) : pathBasis p = pathElement p.2.2 := by
  obtain ⟨i, rfl⟩ := pathFor_surjective p
  rw [pathBasis_pathFor]
  cases i with
  | inl i => exact algebraBasis_vertex i
  | inr i => simpa [pathFor] using algebraBasis_arrow i

theorem path_left_identity {a b : Vertex} (p : StarPath a b) :
    vertex b * pathElement p = pathElement p := by
  induction p with
  | nil => exact vertex_square _
  | @cons b c p e ih =>
    have hc : c = 0 := e.down.2
    subst c
    rw [pathElement_cons, ← mul_assoc, vertex_arrow, if_pos rfl]

theorem path_right_identity {a b : Vertex} (p : StarPath a b) :
    pathElement p * vertex a = pathElement p := by
  induction p with
  | nil => exact vertex_square _
  | @cons b c p e ih => rw [pathElement_cons, mul_assoc, ih]

theorem actual_path_concatenation {a b c : Vertex} (p : StarPath a b) (q : StarPath b c) :
    pathElement q * pathElement p = pathElement (p.comp q) := by
  induction q with
  | nil => simpa using path_left_identity p
  | @cons b c q e ih =>
    simp only [Quiver.Path.comp_cons, pathElement_cons]
    rw [mul_assoc, ih]

theorem noncomposable_paths_multiply_zero {a b c d : Vertex}
    (p : StarPath a b) (q : StarPath c d) (h : b ≠ c) :
    pathElement q * pathElement p = 0 := by
  calc
    pathElement q * pathElement p =
        (pathElement q * vertex c) * (vertex b * pathElement p) := by
      rw [path_right_identity, path_left_identity]
    _ = pathElement q * (vertex c * vertex b) * pathElement p := by noncomm_ring
    _ = 0 := by rw [vertex_mul, if_neg (Ne.symm h), mul_zero, zero_mul]

def Incoming := Σ a : Vertex, @Quiver.Hom Vertex starQuiver a 0

def incomingArrow (i : Arrow) : Incoming := ⟨i.succ, ⟨by simp⟩⟩

theorem incomingArrow_injective : Function.Injective incomingArrow := by
  intro i j h
  exact Fin.succ_inj.mp (congrArg (fun p : Incoming => p.1) h)

theorem four_incoming_arrows : ∃ f : Fin 4 → Incoming, Function.Injective f :=
  ⟨incomingArrow, incomingArrow_injective⟩

theorem not_at_most_two_incoming : ¬ Nonempty (Incoming ↪ Fin 2) := by
  rintro ⟨e⟩
  have h := Fintype.card_le_of_injective (e ∘ incomingArrow)
    (e.injective.comp incomingArrow_injective)
  norm_num at h


/-! Genuine finite-dimensional modules and all their native module morphisms. -/

@[ext] structure Family (t : ℚ) where
  x : ℚ
  y : ℚ
  leaves : ArrowSpace

def familyEquiv (t : ℚ) : Family t ≃ ℚ × ℚ × ArrowSpace where
  toFun m := (m.x, m.y, m.leaves)
  invFun m := ⟨m.1, m.2.1, m.2.2⟩
  left_inv m := by cases m; rfl
  right_inv m := by cases m; rfl

instance family_add (t : ℚ) : AddCommGroup (Family t) := (familyEquiv t).addCommGroup
instance family_scalar (t : ℚ) : Module ℚ (Family t) := (familyEquiv t).module ℚ

@[simp] theorem family_zero_x (t : ℚ) : (0 : Family t).x = 0 := rfl
@[simp] theorem family_zero_y (t : ℚ) : (0 : Family t).y = 0 := rfl
@[simp] theorem family_zero_leaves (t : ℚ) (i : Arrow) : (0 : Family t).leaves i = 0 := rfl
@[simp] theorem family_add_x {t : ℚ} (m n : Family t) : (m + n).x = m.x + n.x := rfl
@[simp] theorem family_add_y {t : ℚ} (m n : Family t) : (m + n).y = m.y + n.y := rfl
@[simp] theorem family_add_leaves {t : ℚ} (m n : Family t) (i : Arrow) :
    (m + n).leaves i = m.leaves i + n.leaves i := rfl
@[simp] theorem family_smul_x {t : ℚ} (c : ℚ) (m : Family t) : (c • m).x = c * m.x := rfl
@[simp] theorem family_smul_y {t : ℚ} (c : ℚ) (m : Family t) : (c • m).y = c * m.y := rfl
@[simp] theorem family_smul_leaves {t : ℚ} (c : ℚ) (m : Family t) (i : Arrow) :
    (c • m).leaves i = c * m.leaves i := rfl

def lineX (i : Arrow) : ℚ := if i = 1 then 0 else 1
def lineY (t : ℚ) (i : Arrow) : ℚ := if i = 0 then 0 else if i = 3 then t else 1

def act (t : ℚ) (a : A) (m : Family t) : Family t where
  x := a.fst 0 * m.x + ∑ i : Arrow, a.snd i * m.leaves i * lineX i
  y := a.fst 0 * m.y + ∑ i : Arrow, a.snd i * m.leaves i * lineY t i
  leaves i := a.fst i.succ * m.leaves i

instance family_module (t : ℚ) : Module A (Family t) where
  smul := act t
  one_smul m := by
    apply Family.ext
    · change (act t 1 m).x = m.x
      norm_num [act, Fin.sum_univ_succ]
    · change (act t 1 m).y = m.y
      norm_num [act, Fin.sum_univ_succ]
    · funext i; change (1 : ℚ) * m.leaves i = m.leaves i; ring
  mul_smul a b m := by
    apply Family.ext
    · change (act t (a * b) m).x = (act t a (act t b m)).x
      norm_num [act, Fin.sum_univ_succ, multiplication_diagonal, multiplication_arrow]; ring
    · change (act t (a * b) m).y = (act t a (act t b m)).y
      norm_num [act, Fin.sum_univ_succ, multiplication_diagonal, multiplication_arrow]; ring
    · funext i
      change (a.fst i.succ * b.fst i.succ) * m.leaves i =
        a.fst i.succ * (b.fst i.succ * m.leaves i)
      ring
  smul_zero a := by
    apply Family.ext
    · change (act t a 0).x = 0
      norm_num [act, Fin.sum_univ_succ]
    · change (act t a 0).y = 0
      norm_num [act, Fin.sum_univ_succ]
    · funext i; change a.fst i.succ * 0 = 0; ring
  smul_add a m n := by
    apply Family.ext
    · change (act t a (m + n)).x = (act t a m).x + (act t a n).x
      norm_num [act, Fin.sum_univ_succ]; ring
    · change (act t a (m + n)).y = (act t a m).y + (act t a n).y
      norm_num [act, Fin.sum_univ_succ]; ring
    · funext i
      change a.fst i.succ * (m.leaves i + n.leaves i) =
        a.fst i.succ * m.leaves i + a.fst i.succ * n.leaves i
      ring
  add_smul a b m := by
    apply Family.ext
    · change (act t (a + b) m).x = (act t a m).x + (act t b m).x
      norm_num [act, Fin.sum_univ_succ]; ring
    · change (act t (a + b) m).y = (act t a m).y + (act t b m).y
      norm_num [act, Fin.sum_univ_succ]; ring
    · funext i
      change (a.fst i.succ + b.fst i.succ) * m.leaves i =
        a.fst i.succ * m.leaves i + b.fst i.succ * m.leaves i
      ring
  zero_smul m := by
    apply Family.ext
    · change (act t 0 m).x = 0
      norm_num [act, Fin.sum_univ_succ]
    · change (act t 0 m).y = 0
      norm_num [act, Fin.sum_univ_succ]
    · funext i; change (0 : ℚ) * m.leaves i = 0; ring

@[simp] theorem family_a_smul_x {t : ℚ} (a : A) (m : Family t) :
    (a • m).x = a.fst 0 * m.x + ∑ i : Arrow, a.snd i * m.leaves i * lineX i := rfl
@[simp] theorem family_a_smul_y {t : ℚ} (a : A) (m : Family t) :
    (a • m).y = a.fst 0 * m.y + ∑ i : Arrow, a.snd i * m.leaves i * lineY t i := rfl
@[simp] theorem family_a_smul_leaves {t : ℚ} (a : A) (m : Family t) (i : Arrow) :
    (a • m).leaves i = a.fst i.succ * m.leaves i := rfl

instance family_tower (t : ℚ) : IsScalarTower ℚ A (Family t) where
  smul_assoc c a m := by
    apply Family.ext
    · change (act t (c • a) m).x = c * (act t a m).x
      norm_num [act, Fin.sum_univ_succ]; ring
    · change (act t (c • a) m).y = c * (act t a m).y
      norm_num [act, Fin.sum_univ_succ]; ring
    · funext i
      change (c * a.fst i.succ) * m.leaves i = c * (a.fst i.succ * m.leaves i)
      ring

def familyCoordinates (t : ℚ) : Family t ≃ₗ[ℚ] (ℚ × ℚ × ArrowSpace) where
  __ := familyEquiv t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance family_finite_base (t : ℚ) : Module.Finite ℚ (Family t) :=
  Module.Finite.of_injective (familyCoordinates t).toLinearMap (familyCoordinates t).injective

instance family_finite_algebra (t : ℚ) : Module.Finite A (Family t) :=
  Module.Finite.of_restrictScalars_finite ℚ A (Family t)

theorem family_dimension (t : ℚ) : Module.finrank ℚ (Family t) = 6 := by
  rw [(familyCoordinates t).finrank_eq]
  simp [Module.finrank_prod, ArrowSpace, Arrow]

def center (t x y : ℚ) : Family t := ⟨x, y, 0⟩
def leaf (t : ℚ) (i : Arrow) (c : ℚ) : Family t := ⟨0, 0, Pi.single i c⟩
def xVec (t : ℚ) : Family t := center t 1 0
def yVec (t : ℚ) : Family t := center t 0 1
def leafVec (t : ℚ) (i : Arrow) : Family t := leaf t i 1

instance family_nontrivial (t : ℚ) : Nontrivial (Family t) := by
  refine ⟨⟨xVec t, 0, ?_⟩⟩
  intro h
  have hx := congrArg Family.x h
  norm_num [xVec, center] at hx

theorem center_decomposition (t x y : ℚ) :
    center t x y = x • xVec t + y • yVec t := by
  apply Family.ext
  · simp [center, xVec, yVec]
  · simp [center, xVec, yVec]
  · funext i; simp [center, xVec, yVec]

theorem family_decomposition {t : ℚ} (m : Family t) :
    m = m.x • xVec t + m.y • yVec t + ∑ i : Arrow, m.leaves i • leafVec t i := by
  apply Family.ext
  · norm_num [Fin.sum_univ_succ, xVec, yVec, center, leafVec, leaf]
  · norm_num [Fin.sum_univ_succ, xVec, yVec, center, leafVec, leaf]
  · funext j
    fin_cases j <;>
      norm_num [Fin.sum_univ_succ, xVec, yVec, center, leafVec, leaf, Pi.single_apply, Fin.ext_iff] <;> rfl

theorem linearMap_ext_family_basis {t : ℚ} {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f g : Family t →ₗ[ℚ] M) (hx : f (xVec t) = g (xVec t))
    (hy : f (yVec t) = g (yVec t)) (hl : ∀ i, f (leafVec t i) = g (leafVec t i)) : f = g := by
  apply LinearMap.ext
  intro m
  conv_lhs => rw [family_decomposition m]
  conv_rhs => rw [family_decomposition m]
  simp only [map_add, map_sum, map_smul]
  simp_rw [hx, hy, hl]

theorem vertex_center_action (t : ℚ) (m : Family t) :
    vertex 0 • m = center t m.x m.y := by
  apply Family.ext
  · norm_num [act, vertex, center, Fin.sum_univ_succ]
  · norm_num [act, vertex, center, Fin.sum_univ_succ]
  · funext i; norm_num [act, vertex, center, Pi.single_apply]

theorem vertex_leaf_action (t : ℚ) (i : Arrow) (m : Family t) :
    vertex i.succ • m = leaf t i (m.leaves i) := by
  apply Family.ext
  · norm_num [act, vertex, leaf, Fin.sum_univ_succ]
  · norm_num [act, vertex, leaf, Fin.sum_univ_succ]
  · funext j
    by_cases h : j = i
    · subst j; simp [vertex, leaf]
    · simp [vertex, leaf, h]

theorem arrow_leaf_action (t : ℚ) (i : Arrow) (c : ℚ) :
    arrow i • leaf t i c = center t (c * lineX i) (c * lineY t i) := by
  apply Family.ext
  · norm_num [act, arrow, leaf, center, Pi.single_apply]
  · norm_num [act, arrow, leaf, center, Pi.single_apply]
  · funext j; norm_num [act, arrow, leaf, center]

def coefficient {t s : ℚ} (f : Family t →ₗ[A] Family s) (i : Arrow) : ℚ :=
  (f (leafVec t i)).leaves i

theorem hom_leaf {t s : ℚ} (f : Family t →ₗ[A] Family s) (i : Arrow) :
    f (leafVec t i) = leaf s i (coefficient f i) := by
  have h := f.map_smul (vertex i.succ) (leafVec t i)
  have hfix : vertex i.succ • leafVec t i = leafVec t i := by
    rw [vertex_leaf_action]
    simp [leafVec, leaf]
  rw [hfix, vertex_leaf_action] at h
  exact h

theorem hom_line {t s : ℚ} (f : Family t →ₗ[A] Family s) (i : Arrow) :
    f (center t (lineX i) (lineY t i)) =
      center s (coefficient f i * lineX i) (coefficient f i * lineY s i) := by
  have h := f.map_smul (arrow i) (leafVec t i)
  have hsource : arrow i • leafVec t i = center t (lineX i) (lineY t i) := by
    simpa [leafVec] using arrow_leaf_action t i 1
  rw [hsource, hom_leaf, arrow_leaf_action] at h
  exact h

theorem hom_x {t s : ℚ} (f : Family t →ₗ[A] Family s) :
    f (xVec t) = center s (coefficient f 0) 0 := by
  have h := hom_line f 0
  norm_num [lineX, lineY, xVec, Fin.ext_iff] at h ⊢
  exact h

theorem hom_y {t s : ℚ} (f : Family t →ₗ[A] Family s) :
    f (yVec t) = center s 0 (coefficient f 1) := by
  have h := hom_line f 1
  norm_num [lineX, lineY, yVec, Fin.ext_iff] at h ⊢
  exact h

theorem hom_coefficients_equal {t s : ℚ} (f : Family t →ₗ[A] Family s) :
    ∀ i : Arrow, coefficient f i = coefficient f 0 := by
  have h2 : f (center t 1 1) = center s (coefficient f 2) (coefficient f 2) := by
    have h := hom_line f 2
    norm_num [lineX, lineY, Fin.ext_iff] at h
    exact h
  have hone : center t 1 1 = xVec t + yVec t := by
    simpa using center_decomposition t 1 1
  rw [hone, map_add, hom_x, hom_y] at h2
  have hx2 : coefficient f 0 = coefficient f 2 := by
    simpa [center] using congrArg Family.x h2
  have hy2 : coefficient f 1 = coefficient f 2 := by
    simpa [center] using congrArg Family.y h2
  have h3 : (f.restrictScalars ℚ) (center t 1 t) =
      center s (coefficient f 3) (coefficient f 3 * s) := by
    have h := hom_line f 3
    norm_num [lineX, lineY, Fin.ext_iff] at h
    exact h
  have hcenter : center t 1 t = xVec t + t • yVec t := by
    simpa using center_decomposition t 1 t
  rw [hcenter, map_add, map_smul] at h3
  change f (xVec t) + t • f (yVec t) = _ at h3
  rw [hom_x, hom_y] at h3
  have hx3 : coefficient f 0 = coefficient f 3 := by
    simpa [center] using congrArg Family.x h3
  intro i
  fin_cases i
  · rfl
  · exact hy2.trans hx2.symm
  · exact hx2.symm
  · exact hx3.symm

theorem hom_parameter_constraint {t s : ℚ} (f : Family t →ₗ[A] Family s) :
    coefficient f 0 * t = coefficient f 0 * s := by
  have h3 : (f.restrictScalars ℚ) (center t 1 t) =
      center s (coefficient f 3) (coefficient f 3 * s) := by
    have h := hom_line f 3
    norm_num [lineX, lineY, Fin.ext_iff] at h
    exact h
  have hcenter : center t 1 t = xVec t + t • yVec t := by
    simpa using center_decomposition t 1 t
  rw [hcenter, map_add, map_smul] at h3
  change f (xVec t) + t • f (yVec t) = _ at h3
  rw [hom_x, hom_y] at h3
  have hy3 : t * coefficient f 1 = coefficient f 3 * s := by
    simpa [center] using congrArg Family.y h3
  rw [hom_coefficients_equal f 1, hom_coefficients_equal f 3] at hy3
  simpa only [mul_comm t] using hy3

def scalarMap (t s c : ℚ) : Family t →ₗ[ℚ] Family s where
  toFun m := ⟨c * m.x, c * m.y, fun i => c * m.leaves i⟩
  map_add' m n := by
    apply Family.ext
    · change c * (m.x + n.x) = c * m.x + c * n.x; ring
    · change c * (m.y + n.y) = c * m.y + c * n.y; ring
    · funext i
      change c * (m.leaves i + n.leaves i) = c * m.leaves i + c * n.leaves i
      ring
  map_smul' a m := by
    apply Family.ext
    · change c * (a * m.x) = a * (c * m.x); ring
    · change c * (a * m.y) = a * (c * m.y); ring
    · funext i; change c * (a * m.leaves i) = a * (c * m.leaves i); ring

theorem hom_scalar_map {t s : ℚ} (f : Family t →ₗ[A] Family s) :
    f.restrictScalars ℚ = scalarMap t s (coefficient f 0) := by
  apply linearMap_ext_family_basis
  · change f (xVec t) = _
    rw [hom_x]
    apply Family.ext
    · simp [scalarMap, xVec, center]
    · simp [scalarMap, xVec, center]
    · funext i; simp [scalarMap, xVec, center]
  · change f (yVec t) = _
    rw [hom_y, hom_coefficients_equal f 1]
    apply Family.ext
    · simp [scalarMap, yVec, center]
    · simp [scalarMap, yVec, center]
    · funext i; simp [scalarMap, yVec, center]
  · intro i
    change f (leafVec t i) = _
    rw [hom_leaf, hom_coefficients_equal f i]
    apply Family.ext
    · simp [scalarMap, leafVec, leaf]
    · simp [scalarMap, leafVec, leaf]
    · funext j
      by_cases h : j = i <;> simp [scalarMap, leafVec, leaf, Pi.single_apply, h]

theorem hom_zero_of_ne {t s : ℚ} (h : t ≠ s) (f : Family t →ₗ[A] Family s) : f = 0 := by
  have hmul : coefficient f 0 * (t - s) = 0 := by
    rw [mul_sub, hom_parameter_constraint, sub_self]
  have hc : coefficient f 0 = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr h)
  apply LinearMap.ext
  intro m
  have he := congrArg (fun g : Family t →ₗ[ℚ] Family s => g m) (hom_scalar_map f)
  rw [hc] at he
  have hzero : scalarMap t s 0 m = 0 := by
    apply Family.ext
    · simp [scalarMap]
    · simp [scalarMap]
    · funext i; simp [scalarMap]
  exact he.trans hzero

theorem every_endomorphism_scalar (t : ℚ) (f : Family t →ₗ[A] Family t) :
    ∃ c : ℚ, ∀ m : Family t, f m = c • m := by
  refine ⟨coefficient f 0, fun m => ?_⟩
  exact congrArg (fun g : Family t →ₗ[ℚ] Family t => g m) (hom_scalar_map f)

def Indecomposable (M : ModuleCat.{0} A) : Prop :=
  Nontrivial M ∧ ∀ P Q : Submodule A M, IsCompl P Q → P = ⊥ ∨ Q = ⊥

abbrev familyObject (t : ℚ) : ModuleCat.{0} A := ModuleCat.of A (Family t)

theorem family_indecomposable (t : ℚ) : Indecomposable (familyObject t) := by
  refine ⟨inferInstance, ?_⟩
  intro P Q hPQ
  by_cases hP : P = ⊥
  · exact Or.inl hP
  right
  have hex : ∃ p : Family t, p ∈ P ∧ p ≠ 0 := by
    by_contra hnot
    apply hP
    apply le_antisymm ?_ bot_le
    intro p hp
    change p = 0
    by_contra hp0
    exact hnot ⟨p, hp, hp0⟩
  obtain ⟨p, hp, hp0⟩ := hex
  let projection : Family t →ₗ[A] Family t := P.projection Q hPQ
  obtain ⟨c, hc⟩ := every_endomorphism_scalar t projection
  have hcp : c • p = p := by
    rw [← hc]
    exact P.projection_apply_of_mem_left hPQ hp
  have hcm : (c - 1) • p = 0 := by rw [sub_smul, one_smul, hcp, sub_self]
  have hc1 : c = 1 := sub_eq_zero.mp ((smul_eq_zero.mp hcm).resolve_right hp0)
  apply le_antisymm ?_ bot_le
  intro q hq
  change q = 0
  have he : c • q = 0 := by
    rw [← hc]
    exact P.projection_apply_of_mem_right hPQ hq
  simpa [hc1] using he

theorem family_nonisomorphic {t s : ℚ} (h : t ≠ s) :
    ¬ Nonempty (familyObject t ≃ₗ[A] familyObject s) := by
  rintro ⟨e⟩
  have hz := hom_zero_of_ne h e.toLinearMap
  have he : e (xVec t) = (0 : Family s) :=
    congrArg (fun f : Family t →ₗ[A] Family s => f (xVec t)) hz
  have hzero := e.injective (he.trans (map_zero e).symm)
  have hx := congrArg Family.x hzero
  norm_num [xVec, center] at hx

def FiniteIndecomposable := {M : ModuleCat.{0} A // Module.Finite A M ∧ Indecomposable M}

theorem finitely_generated_iff_finite_dimensional (M : ModuleCat.{0} A) :
    Module.Finite A M ↔ Module.Finite ℚ M := by
  constructor
  · intro h
    have : Module.Finite A M := h
    exact Module.Finite.trans A M
  · intro h
    have : Module.Finite ℚ M := h
    exact Module.Finite.of_restrictScalars_finite ℚ A M

def moduleIso : Setoid FiniteIndecomposable where
  r M N := Nonempty (M.val ≃ₗ[A] N.val)
  iseqv := ⟨fun _ => ⟨LinearEquiv.refl _ _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev IndecomposableClass := Quotient moduleIso

def familyClass (t : ℚ) : IndecomposableClass :=
  Quotient.mk _ ⟨familyObject t, inferInstance, family_indecomposable t⟩

theorem familyClass_injective : Function.Injective familyClass := by
  intro t s h
  by_contra hts
  exact family_nonisomorphic hts (Quotient.exact h)

instance indecomposableClasses_infinite : Infinite IndecomposableClass :=
  Infinite.of_injective familyClass familyClass_injective

/-- Standard finite representation type: all finitely generated indecomposables up to native iso. -/
def RepresentationFinite : Prop := Finite IndecomposableClass

theorem not_representation_finite : ¬ RepresentationFinite := by
  intro h
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite IndecomposableClass)) h

theorem printed_iff_impossible (rigid : Prop) :
    ¬ (IsZero HH1 ↔ RepresentationFinite ∧ rigid) := by
  intro h
  exact not_representation_finite (h.mp HH1_zero).1

theorem complete_counterexample :
    Module.finrank ℚ A = 9 ∧ IsZero HH1 ∧
    Infinite IndecomposableClass ∧ ¬ RepresentationFinite :=
  ⟨algebra_dimension, HH1_zero, inferInstance, not_representation_finite⟩

end
end TLMC556
