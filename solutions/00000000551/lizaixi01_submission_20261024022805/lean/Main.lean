import Mathlib

open CategoryTheory
open scoped BigOperators

namespace TLMC551

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Vertex := Fin 4
abbrev Arrow := Fin 3
abbrev Diagonal := Vertex → ℂ
abbrev ArrowSpace := Arrow → ℂ

instance arrow_add : AddCommGroup ArrowSpace := inferInstanceAs (AddCommGroup (Arrow → ℂ))
instance arrow_scalar : Module ℂ ArrowSpace := inferInstanceAs (Module ℂ (Arrow → ℂ))

@[ext] theorem arrow_ext {x y : ArrowSpace} (h : ∀ i, x i = y i) : x = y := funext h

instance arrow_left : Module Diagonal ArrowSpace where
  smul r m := fun i => r i.castSucc * m i
  one_smul m := by funext i; change (1 : ℂ) * m i = m i; exact one_mul _
  mul_smul r s m := by funext i; exact mul_assoc _ _ _
  smul_zero r := by funext i; exact mul_zero _
  smul_add r m n := by funext i; exact mul_add _ _ _
  add_smul r s m := by funext i; exact add_mul _ _ _
  zero_smul m := by funext i; exact zero_mul _

instance arrow_right : Module Diagonalᵐᵒᵖ ArrowSpace where
  smul r m := fun i => r.unop i.succ * m i
  one_smul m := by funext i; change (1 : ℂ) * m i = m i; exact one_mul _
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
    change r i.castSucc * (s.unop i.succ * m i) = s.unop i.succ * (r i.castSucc * m i)
    ring

instance arrow_left_tower : IsScalarTower ℂ Diagonal ArrowSpace where
  smul_assoc c r m := by
    funext i
    change (c * r i.castSucc) * m i = c * (r i.castSucc * m i)
    ring

instance arrow_right_tower : IsScalarTower ℂ Diagonalᵐᵒᵖ ArrowSpace where
  smul_assoc c r m := by
    funext i
    change (c * r.unop i.succ) * m i = c * (r.unop i.succ * m i)
    ring

abbrev AlgebraA := TrivSqZeroExt Diagonal ArrowSpace

instance algebra_finite : Module.Finite ℂ AlgebraA :=
  inferInstanceAs (Module.Finite ℂ (Diagonal × (Arrow → ℂ)))

theorem multiplication_diagonal (a b : AlgebraA) (i : Vertex) :
    (a * b).fst i = a.fst i * b.fst i := rfl

theorem multiplication_arrow (a b : AlgebraA) (i : Arrow) :
    (a * b).snd i = a.fst i.castSucc * b.snd i + a.snd i * b.fst i.succ := by
  change a.fst i.castSucc * b.snd i + b.fst i.succ * a.snd i = _
  ring

def vertexIdempotent (i : Vertex) : AlgebraA :=
  TrivSqZeroExt.inl (Pi.single i 1)

def arrowElement (i : Arrow) : AlgebraA :=
  TrivSqZeroExt.inr (Pi.single i 1)

theorem arrow_product_zero (i j : Arrow) : arrowElement i * arrowElement j = 0 :=
  TrivSqZeroExt.inr_mul_inr _ _ _

@[ext] structure Simple (i : Vertex) where
  val : ℂ

def simpleEquiv (i : Vertex) : Simple i ≃ ℂ where
  toFun z := z.val
  invFun z := ⟨z⟩
  left_inv z := by cases z; rfl
  right_inv z := rfl

instance simple_add (i : Vertex) : AddCommGroup (Simple i) := (simpleEquiv i).addCommGroup
instance simple_scalar (i : Vertex) : Module ℂ (Simple i) := (simpleEquiv i).module ℂ

@[simp] theorem simple_zero_val (i : Vertex) : (0 : Simple i).val = 0 := rfl
@[simp] theorem simple_add_val {i : Vertex} (x y : Simple i) :
    (x + y).val = x.val + y.val := rfl

instance simple_module (i : Vertex) : Module AlgebraA (Simple i) where
  smul a z := ⟨a.fst i * z.val⟩
  one_smul z := by apply Simple.ext; change (1 : ℂ) * z.val = z.val; ring
  mul_smul a b z := by
    apply Simple.ext
    change (a.fst i * b.fst i) * z.val = a.fst i * (b.fst i * z.val)
    ring
  smul_zero a := by apply Simple.ext; change a.fst i * 0 = 0; ring
  smul_add a x y := by
    apply Simple.ext
    change a.fst i * (x.val+y.val) = a.fst i * x.val + a.fst i * y.val
    ring
  add_smul a b z := by
    apply Simple.ext
    change (a.fst i + b.fst i) * z.val = a.fst i * z.val + b.fst i * z.val
    ring
  zero_smul z := by apply Simple.ext; change (0 : ℂ) * z.val = 0; ring

@[simp] theorem simple_smul_val {i : Vertex} (a : AlgebraA) (z : Simple i) :
    (a • z).val = a.fst i * z.val := rfl

def simpleProjection (i : Vertex) : AlgebraA →ₗ[AlgebraA] Simple i where
  toFun a := ⟨a.fst i⟩
  map_add' a b := by apply Simple.ext; rfl
  map_smul' a b := by apply Simple.ext; rfl

theorem simpleProjection_surjective (i : Vertex) : Function.Surjective (simpleProjection i) := by
  intro z
  exact ⟨TrivSqZeroExt.inl (fun _ => z.val), by cases z; rfl⟩

instance simple_finite (i : Vertex) : Module.Finite AlgebraA (Simple i) :=
  Module.Finite.of_surjective (simpleProjection i) (simpleProjection_surjective i)

@[ext] structure ProjectivePair (i : Arrow) where
  top : ℂ
  socle : ℂ

def pairEquiv (i : Arrow) : ProjectivePair i ≃ ℂ × ℂ where
  toFun z := (z.top,z.socle)
  invFun z := ⟨z.1,z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

instance pair_add (i : Arrow) : AddCommGroup (ProjectivePair i) :=
  (pairEquiv i).addCommGroup

@[simp] theorem pair_zero_top (i : Arrow) : (0 : ProjectivePair i).top = 0 := rfl
@[simp] theorem pair_zero_socle (i : Arrow) : (0 : ProjectivePair i).socle = 0 := rfl
@[simp] theorem pair_add_top {i : Arrow} (x y : ProjectivePair i) :
    (x+y).top = x.top+y.top := rfl
@[simp] theorem pair_add_socle {i : Arrow} (x y : ProjectivePair i) :
    (x+y).socle = x.socle+y.socle := rfl

instance pair_module (i : Arrow) : Module AlgebraA (ProjectivePair i) where
  smul a z := ⟨a.fst i.succ * z.top, a.snd i * z.top + a.fst i.castSucc * z.socle⟩
  one_smul z := by
    apply ProjectivePair.ext
    · change (1 : ℂ)*z.top = z.top; ring
    · change (0 : ℂ)*z.top+1*z.socle = z.socle; ring
  mul_smul a b z := by
    apply ProjectivePair.ext
    · change (a.fst i.succ * b.fst i.succ) * z.top = a.fst i.succ * (b.fst i.succ * z.top)
      ring
    · change (a.fst i.castSucc * b.snd i + b.fst i.succ * a.snd i) * z.top +
        (a.fst i.castSucc * b.fst i.castSucc) * z.socle =
        a.snd i * (b.fst i.succ * z.top) +
        a.fst i.castSucc * (b.snd i * z.top + b.fst i.castSucc * z.socle)
      ring
  smul_zero a := by
    apply ProjectivePair.ext
    · change a.fst i.succ * 0 = 0; ring
    · change a.snd i * 0 + a.fst i.castSucc * 0 = 0; ring
  smul_add a x y := by
    apply ProjectivePair.ext
    · change a.fst i.succ * (x.top+y.top) = a.fst i.succ*x.top+a.fst i.succ*y.top; ring
    · change a.snd i * (x.top+y.top) + a.fst i.castSucc * (x.socle+y.socle) =
        (a.snd i*x.top+a.fst i.castSucc*x.socle)+(a.snd i*y.top+a.fst i.castSucc*y.socle)
      ring
  add_smul a b z := by
    apply ProjectivePair.ext
    · change (a.fst i.succ+b.fst i.succ)*z.top = a.fst i.succ*z.top+b.fst i.succ*z.top; ring
    · change (a.snd i+b.snd i)*z.top + (a.fst i.castSucc+b.fst i.castSucc)*z.socle =
        (a.snd i*z.top+a.fst i.castSucc*z.socle)+(b.snd i*z.top+b.fst i.castSucc*z.socle)
      ring
  zero_smul z := by
    apply ProjectivePair.ext
    · change (0 : ℂ)*z.top = 0; ring
    · change (0 : ℂ)*z.top+0*z.socle = 0; ring

@[simp] theorem pair_smul_top {i : Arrow} (a : AlgebraA) (z : ProjectivePair i) :
    (a • z).top = a.fst i.succ * z.top := rfl

@[simp] theorem pair_smul_socle {i : Arrow} (a : AlgebraA) (z : ProjectivePair i) :
    (a • z).socle = a.snd i * z.top + a.fst i.castSucc * z.socle := rfl

def pairProjection (i : Arrow) : AlgebraA →ₗ[AlgebraA] ProjectivePair i where
  toFun a := ⟨a.fst i.succ, a.snd i⟩
  map_add' a b := by apply ProjectivePair.ext <;> rfl
  map_smul' a b := by
    apply ProjectivePair.ext
    · rfl
    · change (a*b).snd i = a.snd i * b.fst i.succ + a.fst i.castSucc * b.snd i
      rw [multiplication_arrow]
      ring

def pairInclusion (i : Arrow) : ProjectivePair i →ₗ[AlgebraA] AlgebraA where
  toFun z := (Pi.single i.succ z.top, Pi.single i z.socle)
  map_add' z w := by
    apply TrivSqZeroExt.ext
    · ext j; change (Pi.single i.succ (z.top+w.top) : Diagonal) j = _; simp [Pi.single_add]
    · ext j; change (Pi.single i (z.socle+w.socle) : Arrow → ℂ) j = _; simp [Pi.single_add, Pi.add_apply]
  map_smul' a z := by
    apply TrivSqZeroExt.ext
    · ext j
      change (Pi.single i.succ (a.fst i.succ * z.top) : Diagonal) j =
        a.fst j * (Pi.single i.succ z.top : Diagonal) j
      by_cases h : i.succ = j
      · subst j; simp
      · simp [h]
    · ext j
      change (Pi.single i (a.snd i * z.top + a.fst i.castSucc * z.socle) : ArrowSpace) j =
        a.fst j.castSucc * (Pi.single i z.socle : Arrow → ℂ) j +
        (Pi.single i.succ z.top : Diagonal) j.succ * a.snd j
      by_cases h : i = j
      · subst j; simp; ring
      · have hs : i.succ ≠ j.succ := fun e => h (Fin.succ_inj.mp e)
        simp [h, hs]

theorem pair_retract (i : Arrow) : (pairProjection i).comp (pairInclusion i) = LinearMap.id := by
  ext z <;> simp [pairProjection, pairInclusion]

instance pair_projective (i : Arrow) : Module.Projective AlgebraA (ProjectivePair i) :=
  Module.Projective.of_split (pairInclusion i) (pairProjection i) (pair_retract i)

def socleInclusion (i : Arrow) : Simple i.castSucc →ₗ[AlgebraA] ProjectivePair i where
  toFun z := ⟨0,z.val⟩
  map_add' z w := by apply ProjectivePair.ext <;> simp
  map_smul' a z := by apply ProjectivePair.ext <;> simp

def topProjection (i : Arrow) : ProjectivePair i →ₗ[AlgebraA] Simple i.succ where
  toFun z := ⟨z.top⟩
  map_add' z w := by apply Simple.ext; rfl
  map_smul' a z := by apply Simple.ext; rfl

def sequence (i : Arrow) : ShortComplex (ModuleCat AlgebraA) :=
  ShortComplex.moduleCatMk (socleInclusion i) (topProjection i) (by ext z; rfl)

theorem sequence_exact (i : Arrow) : (sequence i).ShortExact where
  exact := by
    apply (sequence i).moduleCat_exact_iff.mpr
    intro z hz
    change (⟨z.top⟩ : Simple i.succ) = 0 at hz
    have hz' := congrArg Simple.val hz
    exact ⟨⟨z.socle⟩, by apply ProjectivePair.ext; exact hz'.symm; rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro z w h
    apply Simple.ext
    exact congrArg ProjectivePair.socle h)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro z
    exact ⟨⟨z.val,0⟩, by cases z; rfl⟩)

def zeroInclusion : Simple 0 →ₗ[AlgebraA] AlgebraA where
  toFun z := (Pi.single 0 z.val, 0)
  map_add' z w := by
    apply TrivSqZeroExt.ext
    · ext j; simp [Pi.single_add]
    · change (0 : ArrowSpace) = 0 + 0
      simp
  map_smul' a z := by
    apply TrivSqZeroExt.ext
    · ext j
      change (Pi.single 0 (a.fst 0 * z.val) : Diagonal) j =
        a.fst j * (Pi.single 0 z.val : Diagonal) j
      by_cases h : (0 : Vertex) = j
      · subst j; simp
      · simp [h]
    · ext j
      change (0 : ℂ) = a.fst j.castSucc * 0 + (Pi.single 0 z.val : Diagonal) j.succ * a.snd j
      simp

theorem zero_retract : (simpleProjection 0).comp zeroInclusion = LinearMap.id := by
  ext z
  simp [simpleProjection, zeroInclusion]

instance zero_projective : Module.Projective AlgebraA (Simple 0) :=
  Module.Projective.of_split zeroInclusion (simpleProjection 0) zero_retract

theorem topProjection_surjective (i : Arrow) : Function.Surjective (topProjection i) := by
  intro z
  exact ⟨⟨z.val,0⟩, by cases z; rfl⟩

theorem simple_one_not_projective : ¬ Module.Projective AlgebraA (Simple 1) := by
  intro hp
  have := hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (topProjection 0)
    (LinearMap.id : Simple 1 →ₗ[AlgebraA] Simple 1) (topProjection_surjective 0)
  let v : Simple 1 := ⟨1⟩
  have htop : (s v).top = 1 := by
    have h := congrArg Simple.val (LinearMap.congr_fun hs v)
    simpa [topProjection, v] using h
  have hz : arrowElement 0 • v = (0 : Simple 1) := by
    apply Simple.ext
    simp [arrowElement]
  have hr : (arrowElement 0 • s v).socle = 0 := by
    rw [← s.map_smul, hz, s.map_zero]
    rfl
  simp [arrowElement, htop] at hr

abbrev simpleObject (i : Vertex) : ModuleCat AlgebraA := ModuleCat.of AlgebraA (Simple i)

theorem dimension_shift (i : Arrow) (n : ℕ) :
    HasProjectiveDimensionLT (simpleObject i.succ) (n + 2) ↔
      HasProjectiveDimensionLT (simpleObject i.castSucc) (n + 1) := by
  have hp : CategoryTheory.Projective (ModuleCat.of AlgebraA (ProjectivePair i)) := inferInstance
  exact (sequence_exact i).hasProjectiveDimensionLT_X₃_iff n hp

theorem simple_three_dimension_le : HasProjectiveDimensionLE (simpleObject 3) 3 := by
  have h0 : HasProjectiveDimensionLT (simpleObject 0) 1 := inferInstance
  have h1 := (dimension_shift 0 0).mpr h0
  have h2 := (dimension_shift 1 1).mpr h1
  exact (dimension_shift 2 2).mpr h2

theorem simple_three_not_dimension_lt : ¬ HasProjectiveDimensionLT (simpleObject 3) 3 := by
  intro h3
  have h2 := (dimension_shift 2 1).mp h3
  have h1 := (dimension_shift 1 0).mp h2
  have hc : CategoryTheory.Projective (simpleObject 1) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr h1
  have hm : Module.Projective AlgebraA (Simple 1) :=
    (IsProjective.iff_projective (Simple 1)).mpr hc
  exact simple_one_not_projective hm

theorem simple_three_projectiveDimension : projectiveDimension (simpleObject 3) = 3 := by
  apply le_antisymm
  · exact (projectiveDimension_le_iff _ 3).mpr simple_three_dimension_le
  · exact (projectiveDimension_ge_iff _ 3).mpr simple_three_not_dimension_lt

def finitisticDimension : WithBot ℕ∞ :=
  sSup {d | ∃ M : ModuleCat.{0} AlgebraA, Module.Finite AlgebraA M ∧
    projectiveDimension M ≠ ⊤ ∧ d = projectiveDimension M}

theorem finitistic_dimension_ge_three : (3 : WithBot ℕ∞) ≤ finitisticDimension := by
  apply le_sSup
  refine ⟨simpleObject 3, inferInstance, ?_, simple_three_projectiveDimension.symm⟩
  rw [simple_three_projectiveDimension]
  change ((3 : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
  exact fun h => ENat.natCast_ne_top 3 (WithBot.coe_injective h)

theorem not_finitistic_dimension_le_two : ¬ finitisticDimension ≤ 2 := by
  intro h
  have h' : (3 : WithBot ℕ∞) ≤ 2 := finitistic_dimension_ge_three.trans h
  norm_num at h'

abbrev LinePathAlgebra := IncidenceAlgebra ℂ Vertex

def pathUnit (i j : Vertex) (h : i ≤ j) : LinePathAlgebra where
  toFun a b := if a = i ∧ b = j then 1 else 0
  eq_zero_of_not_le' a b hab := by
    split_ifs with he
    · exact (hab (he.1.symm ▸ he.2.symm ▸ h)).elim
    · rfl

theorem adjacent_interval (i : Arrow) :
    Finset.Icc i.castSucc i.succ = {i.castSucc,i.succ} := by
  fin_cases i <;> decide

def presentationMap : LinePathAlgebra →ₐ[ℂ] AlgebraA where
  toFun f := (fun i => f i i, fun i => f i.castSucc i.succ)
  map_zero' := rfl
  map_add' f g := rfl
  map_one' := by
    apply TrivSqZeroExt.ext
    · ext i; simp
    · ext i
      change (if i.castSucc = i.succ then (1 : ℂ) else 0) = 0
      have h : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
      simp [h]
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · ext i
      simp [IncidenceAlgebra.mul_apply]
    · ext i
      change (f*g) i.castSucc i.succ =
        f i.castSucc i.castSucc*g i.castSucc i.succ + g i.succ i.succ*f i.castSucc i.succ
      rw [IncidenceAlgebra.mul_apply, adjacent_interval]
      have h : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
      simp [h]
      ring
  commutes' c := by
    apply TrivSqZeroExt.ext
    · ext i
      simp [Algebra.algebraMap_eq_smul_one, IncidenceAlgebra.constSMul_apply]
    · ext i
      have h : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
      simp [Algebra.algebraMap_eq_smul_one, IncidenceAlgebra.constSMul_apply, h]

def presentationSection (a : AlgebraA) : LinePathAlgebra where
  toFun i j := if h : i = j then a.fst i else
    if h' : i.val + 1 = j.val then a.snd ⟨i.val, by omega⟩ else 0
  eq_zero_of_not_le' i j hij := by
    split_ifs with h h'
    · exact (hij h.le).elim
    · exact (hij (by change i.val ≤ j.val; omega)).elim
    · rfl

theorem presentation_right_inverse : Function.RightInverse presentationSection presentationMap := by
  intro a
  apply TrivSqZeroExt.ext
  · ext i; simp [presentationMap, presentationSection]
  · ext i
    have h : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
    simp [presentationMap, presentationSection, h]

def relationIdeal : Ideal LinePathAlgebra := RingHom.ker presentationMap.toRingHom

instance relationIdeal_twoSided : relationIdeal.IsTwoSided :=
  inferInstanceAs (RingHom.ker presentationMap.toRingHom).IsTwoSided

noncomputable def presentationEquiv : (LinePathAlgebra ⧸ relationIdeal) ≃ₐ[ℂ] AlgebraA :=
  Ideal.quotientKerAlgEquivOfRightInverse presentation_right_inverse

instance lineQuiver : Quiver Vertex where
  Hom a b := PLift (b.val + 1 = a.val)

abbrev LinePath (a b : Vertex) := @Quiver.Path Vertex lineQuiver a b

def singleDown (i : Arrow) : LinePath i.succ i.castSucc :=
  Quiver.Path.nil.cons ⟨rfl⟩

theorem path_length {a b : Vertex} (p : LinePath a b) : b.val + p.length = a.val := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
    have he : c.val + 1 = b.val := e.down
    simp only [Quiver.Path.length_cons]
    omega

theorem path_unique {a b : Vertex} (p q : LinePath a b) : p = q := by
  induction p with
  | nil =>
    have hq := path_length q
    exact (q.eq_nil_of_length_zero (by omega)).symm
  | @cons b c p e ih =>
    cases q with
    | nil =>
      have hp := path_length p
      have he : a.val + 1 = b.val := e.down
      omega
    | @cons b' c' q f =>
      have he : c.val + 1 = b.val := e.down
      have hf : c.val + 1 = b'.val := f.down
      have hb : b = b' := Fin.ext (by omega)
      subst b'
      have hq : p = q := ih q
      subst q
      have h : e = f := by
        change @Eq (PLift (c.val + 1 = b.val)) e f
        exact Subsingleton.elim _ _
      rw [h]

def canonicalPath (a b : Vertex) (h : b ≤ a) : LinePath a b := by
  classical
  change b.val ≤ a.val at h
  exact Classical.choice (by
    fin_cases a <;> fin_cases b <;> norm_num at h
    all_goals first
      | exact ⟨Quiver.Path.nil⟩
      | exact ⟨singleDown 0⟩
      | exact ⟨singleDown 1⟩
      | exact ⟨singleDown 2⟩
      | exact ⟨(singleDown 1).comp (singleDown 0)⟩
      | exact ⟨(singleDown 2).comp (singleDown 1)⟩
      | exact ⟨((singleDown 2).comp (singleDown 1)).comp (singleDown 0)⟩)

theorem path_exists_iff (a b : Vertex) : Nonempty (LinePath a b) ↔ b ≤ a := by
  constructor
  · rintro ⟨p⟩
    have h := path_length p
    change b.val ≤ a.val
    omega
  · exact fun h => ⟨canonicalPath a b h⟩

abbrev Interval := {p : Vertex × Vertex // p.1 ≤ p.2}

def pathCoordinates : LinePathAlgebra ≃ₗ[ℂ] (Interval → ℂ) where
  toFun f p := f p.1.1 p.1.2
  invFun c :=
    { toFun := fun i j => if h : i ≤ j then c ⟨(i,j),h⟩ else 0
      eq_zero_of_not_le' := by intro i j h; simp [h] }
  left_inv f := by
    apply IncidenceAlgebra.ext
    intro i j h
    simp [h]
  right_inv c := by
    funext p
    simp [p.2]
  map_add' f g := rfl
  map_smul' c f := rfl

def pathBasis : Module.Basis Interval ℂ LinePathAlgebra :=
  (Pi.basisFun ℂ Interval).map pathCoordinates.symm

theorem pathBasis_eq_unit (p : Interval) :
    pathBasis p = pathUnit p.1.1 p.1.2 p.2 := by
  apply IncidenceAlgebra.ext
  intro i j hij
  change (if h : i ≤ j then (Pi.basisFun ℂ Interval p) ⟨(i,j),h⟩ else 0) =
    (if i = p.1.1 ∧ j = p.1.2 then 1 else 0)
  simp only [dif_pos hij, Pi.basisFun_apply, Pi.single_apply]
  have he : (⟨(i,j),hij⟩ : Interval) = p ↔ i = p.1.1 ∧ j = p.1.2 := by
    simp [Subtype.ext_iff, Prod.ext_iff, eq_comm]
  simp [he]

theorem pathUnit_mul (a b c d : Vertex) (hab : a ≤ b) (hcd : c ≤ d) :
    pathUnit a b hab * pathUnit c d hcd =
      if h : b = c then pathUnit a d (by subst c; exact hab.trans hcd) else 0 := by
  classical
  apply IncidenceAlgebra.ext
  intro x y hxy
  by_cases hx : x = a
  · subst x
    by_cases hy : y = d
    · subst y
      by_cases hbc : b = c
      · subst c
        simp [pathUnit, IncidenceAlgebra.mul_apply, hab, hcd]
      · simp [pathUnit, IncidenceAlgebra.mul_apply, hbc, Ne.symm hbc]
    · split_ifs <;> simp [pathUnit, IncidenceAlgebra.mul_apply, hy]
  · split_ifs <;> simp [pathUnit, IncidenceAlgebra.mul_apply, hx]

theorem relation_coordinates (f : LinePathAlgebra) : f ∈ relationIdeal ↔
    (∀ i : Vertex, f i i = 0) ∧ (∀ i : Arrow, f i.castSucc i.succ = 0) := by
  change presentationMap f = 0 ↔ _
  constructor
  · intro h
    exact ⟨fun i => congrArg (fun a : AlgebraA => a.fst i) h,
      fun i => congrArg (fun a : AlgebraA => a.snd i) h⟩
  · rintro ⟨hd,ha⟩
    apply TrivSqZeroExt.ext
    · exact funext hd
    · exact funext ha

theorem long_unit_mem (i j : Vertex) (hij : i ≤ j) (hlen : i.val + 2 ≤ j.val) :
    pathUnit i j hij ∈ relationIdeal := by
  apply (relation_coordinates _).mpr
  constructor
  · intro v
    change (if v = i ∧ v = j then (1 : ℂ) else 0) = 0
    split_ifs with h
    · rcases h with ⟨hi,hj⟩
      subst i; subst j; omega
    · rfl
  · intro v
    change (if v.castSucc = i ∧ v.succ = j then (1 : ℂ) else 0) = 0
    split_ifs with h
    · rcases h with ⟨hi,hj⟩
      subst i; subst j
      simp only [Fin.val_castSucc, Fin.val_succ] at hlen
      omega
    · rfl

def pathElement {a b : Vertex} (p : LinePath a b) : LinePathAlgebra :=
  pathUnit b a ((path_exists_iff a b).mp ⟨p⟩)

theorem long_path_mem {a b : Vertex} (p : LinePath a b) (hlen : 2 ≤ p.length) :
    pathElement p ∈ relationIdeal := by
  apply long_unit_mem
  have h := path_length p
  omega

theorem presentation_arrow (i : Arrow) :
    presentationMap (pathUnit i.castSucc i.succ (by change i.val ≤ i.val+1; omega)) = arrowElement i := by
  fin_cases i <;> apply TrivSqZeroExt.ext
  all_goals ext j; fin_cases j <;> norm_num [presentationMap, pathUnit, arrowElement] <;> decide

theorem arrow_pair_in_relation (i j : Arrow) :
    pathUnit i.castSucc i.succ (by change i.val ≤ i.val+1; omega) *
      pathUnit j.castSucc j.succ (by change j.val ≤ j.val+1; omega)
      ∈ relationIdeal := by
  change presentationMap (_ * _) = 0
  rw [map_mul, presentation_arrow, presentation_arrow, arrow_product_zero]

def definingRelations : Set LinePathAlgebra :=
  {pathUnit 0 2 (by decide), pathUnit 1 3 (by decide), pathUnit 0 3 (by decide)}

theorem relation_decomposition (f : LinePathAlgebra) (hf : f ∈ relationIdeal) :
    f = f 0 2 • pathUnit 0 2 (by decide) + f 1 3 • pathUnit 1 3 (by decide) +
      f 0 3 • pathUnit 0 3 (by decide) := by
  obtain ⟨hd,ha⟩ := (relation_coordinates f).mp hf
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h33 := hd 3
  have h01 : f 0 1 = 0 := ha 0
  have h12 : f 1 2 = 0 := ha 1
  have h23 : f 2 3 = 0 := ha 2
  apply IncidenceAlgebra.ext
  intro i j hij
  change i.val ≤ j.val at hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals simp [pathUnit, h00, h11, h22, h33,
    h01, h12, h23]

theorem relation_ideal_generated : relationIdeal = Ideal.span definingRelations := by
  apply le_antisymm
  · intro f hf
    rw [relation_decomposition f hf]
    have hs (c : ℂ) (u : LinePathAlgebra) (hu : u ∈ Ideal.span definingRelations) :
        c • u ∈ Ideal.span definingRelations := by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hu
    have h02 : pathUnit 0 2 (by decide) ∈ Ideal.span definingRelations :=
      Ideal.subset_span (by simp [definingRelations])
    have h13 : pathUnit 1 3 (by decide) ∈ Ideal.span definingRelations :=
      Ideal.subset_span (by simp [definingRelations])
    have h03 : pathUnit 0 3 (by decide) ∈ Ideal.span definingRelations :=
      Ideal.subset_span (by simp [definingRelations])
    exact add_mem (add_mem (hs _ _ h02) (hs _ _ h13)) (hs _ _ h03)
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [definingRelations, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact long_unit_mem _ _ _ (by decide)
    · exact long_unit_mem _ _ _ (by decide)
    · exact long_unit_mem _ _ _ (by decide)

def outgoingArrows (v : Vertex) : Finset Arrow := Finset.univ.filter (fun i => i.succ = v)
def incomingArrows (v : Vertex) : Finset Arrow := Finset.univ.filter (fun i => i.castSucc = v)

theorem vertex_degree_bounds : ∀ v : Vertex,
    (outgoingArrows v).card ≤ 2 ∧ (incomingArrows v).card ≤ 2 := by decide

def allowedFollowers (i : Arrow) : Finset Arrow := by
  classical
  exact Finset.univ.filter (fun j => i.succ = j.castSucc ∧
    pathUnit i.castSucc i.succ (by change i.val ≤ i.val+1; omega) *
      pathUnit j.castSucc j.succ (by change j.val ≤ j.val+1; omega) ∉ relationIdeal)

def allowedPredecessors (i : Arrow) : Finset Arrow := by
  classical
  exact Finset.univ.filter (fun j => j.succ = i.castSucc ∧
    pathUnit j.castSucc j.succ (by change j.val ≤ j.val+1; omega) *
      pathUnit i.castSucc i.succ (by change i.val ≤ i.val+1; omega) ∉ relationIdeal)

theorem allowed_followers_empty (i : Arrow) : allowedFollowers i = ∅ := by
  classical
  ext j
  simp [allowedFollowers, arrow_pair_in_relation]

theorem allowed_predecessors_empty (i : Arrow) : allowedPredecessors i = ∅ := by
  classical
  ext j
  simp [allowedPredecessors, arrow_pair_in_relation]

/-- The standard bound-quiver conditions, for the actual presentation constructed above. -/
def specialBiserialPresentation : Prop :=
  relationIdeal = Ideal.span definingRelations ∧
  (∀ v : Vertex, (outgoingArrows v).card ≤ 2 ∧ (incomingArrows v).card ≤ 2) ∧
  (∀ i : Arrow, (allowedFollowers i).card ≤ 1 ∧ (allowedPredecessors i).card ≤ 1) ∧
  (∃ N : ℕ, ∀ (a b : Vertex) (p : LinePath a b), N ≤ p.length → pathElement p ∈ relationIdeal)

theorem special_biserial_certificate : specialBiserialPresentation := by
  refine ⟨relation_ideal_generated, vertex_degree_bounds, ?_, 2, ?_⟩
  · intro i
    simp [allowed_followers_empty, allowed_predecessors_empty]
  · intro a b p hp
    exact long_path_mem p hp

theorem counterexample : specialBiserialPresentation ∧ ¬ finitisticDimension ≤ 2 :=
  ⟨special_biserial_certificate, not_finitistic_dimension_le_two⟩

end
end TLMC551

