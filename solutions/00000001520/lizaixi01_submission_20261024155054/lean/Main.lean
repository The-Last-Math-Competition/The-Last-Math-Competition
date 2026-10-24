import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

/-!
Actual stable matrix groups, their native group colimit, algebraic K1 and
the signed group-unit quotient defining the Whitehead group.
The concrete counterexample uses the integral group algebra of C5.
-/

namespace TLMC1520

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Matrix

noncomputable section

/-- Ordered finite matrix indices, with one new final coordinate at every step. -/
def Index : ℕ → Type
  | 0 => PUnit
  | n + 1 => Index n ⊕ PUnit

instance indexFintype (n : ℕ) : Fintype (Index n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Index n ⊕ PUnit))

instance indexDecidableEq (n : ℕ) : DecidableEq (Index n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Index n ⊕ PUnit))

theorem index_card (n : ℕ) : Fintype.card (Index n) = n + 1 := by
  induction n with
  | zero => simp [Index]
  | succ n ih =>
      change Fintype.card (Index n ⊕ PUnit) = n + 1 + 1
      rw [Fintype.card_sum, Fintype.card_punit, ih]

variable (R : Type) [CommRing R]

/-- The actual block embedding M ↦ diag(M,1), as a multiplicative map. -/
def matrixStep (n : ℕ) : Matrix (Index n) (Index n) R →*
    Matrix (Index (n + 1)) (Index (n + 1)) R where
  toFun M := Matrix.fromBlocks M 0 0 1
  map_one' := by
    change Matrix.fromBlocks (1 : Matrix (Index n) (Index n) R) 0 0 1 = (1 : Matrix (Index n ⊕ PUnit) (Index n ⊕ PUnit) R)
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  map_mul' A B := by
    change Matrix.fromBlocks (A * B) 0 0 1 = Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1
    simp [Matrix.fromBlocks_multiply]

theorem matrixStep_apply (n : ℕ) (M : Matrix (Index n) (Index n) R)
    (i j : Index n) : matrixStep R n M (.inl i) (.inl j) = M i j := rfl

theorem matrixStep_injective (n : ℕ) : Function.Injective (matrixStep R n) := by
  intro A B h
  ext i j
  exact congrArg (fun M => M (.inl i) (.inl j)) h

abbrev FiniteGL (n : ℕ) := Matrix.GeneralLinearGroup (Index n) R

def groupStep (n : ℕ) : FiniteGL R n →* FiniteGL R (n + 1) :=
  Units.map (matrixStep R n)

theorem groupStep_injective (n : ℕ) : Function.Injective (groupStep R n) := by
  intro A B h
  apply Units.ext
  exact matrixStep_injective R n (congrArg Units.val h)

theorem det_groupStep (n : ℕ) (g : FiniteGL R n) :
    Matrix.GeneralLinearGroup.det (groupStep R n g) =
      Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  exact (Matrix.det_fromBlocks_zero₂₁ _ _ _).trans (by simp)

/-- The full stabilization diagram, with all functor laws supplied by ofSequence. -/
def stableDiagram : ℕ ⥤ GrpCat :=
  Functor.ofSequence (fun n => GrpCat.ofHom (groupStep R n))

/-- The native filtered group colimit, not an assigned unit group. -/
abbrev StableGL := GrpCat.FilteredColimits.colimit (stableDiagram R)

def intoStable (n : ℕ) : FiniteGL R n →* StableGL R :=
  ((GrpCat.FilteredColimits.colimitCocone (stableDiagram R)).ι.app n).hom

def determinantTransformation : stableDiagram R ⟶
    (Functor.const ℕ).obj (GrpCat.of Rˣ) :=
  NatTrans.ofSequence (fun _ => GrpCat.ofHom Matrix.GeneralLinearGroup.det) (by
    intro n
    simp only [stableDiagram, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    rw [← GrpCat.ofHom_comp]
    apply congrArg GrpCat.ofHom
    exact MonoidHom.ext (det_groupStep R n))

def determinantCocone : Cocone (stableDiagram R) :=
  ⟨GrpCat.of Rˣ, determinantTransformation R⟩

def determinantStable : StableGL R →* Rˣ :=
  ((GrpCat.FilteredColimits.colimitCoconeIsColimit (stableDiagram R)).desc
    (determinantCocone R)).hom

theorem determinantStable_into (n : ℕ) (g : FiniteGL R n) :
    determinantStable R (intoStable R n g) = Matrix.GeneralLinearGroup.det g := by
  have h := (GrpCat.FilteredColimits.colimitCoconeIsColimit (stableDiagram R)).fac
    (determinantCocone R) n
  exact ConcreteCategory.congr_hom h g

/-- Algebraic K1 is the actual abelianization of the stable general linear group. -/
abbrev K1 := Abelianization (StableGL R)

def unitsToK1 : Rˣ →* K1 R :=
  Abelianization.of.comp ((intoStable R 0).comp
    (Matrix.GeneralLinearGroup.scalar (Index 0)))

def determinantK1 : K1 R →* Rˣ :=
  Abelianization.lift (determinantStable R)

theorem determinantK1_unit (u : Rˣ) : determinantK1 R (unitsToK1 R u) = u := by
  change determinantStable R (intoStable R 0 (Matrix.GeneralLinearGroup.scalar (Index 0) u)) = u
  rw [determinantStable_into, Matrix.GeneralLinearGroup.det_scalar, index_card]
  simp

abbrev CyclicFive := Multiplicative (ZMod 5)
abbrev GroupRing := MonoidAlgebra ℤ CyclicFive

def generator : CyclicFive := Multiplicative.ofAdd 1

theorem cyclicFive_card : Fintype.card CyclicFive = 5 := by decide

theorem generator_ne_one : generator ≠ 1 := by decide

theorem generator_pow_five : generator ^ 5 = 1 := by decide +kernel

def groupUnit : CyclicFive →* GroupRingˣ where
  toFun g :=
    { val := MonoidAlgebra.single g 1
      inv := MonoidAlgebra.single g⁻¹ 1
      val_inv := by simp [← MonoidAlgebra.one_def]
      inv_val := by simp [← MonoidAlgebra.one_def] }
  map_one' := Units.ext rfl
  map_mul' g h := Units.ext (by simp [MonoidAlgebra.single_mul_single])

/-- Every signed group element, using the true integer units. -/
def signedUnit : (ℤˣ × CyclicFive) →* GroupRingˣ where
  toFun x := Units.map (Int.castRingHom GroupRing).toMonoidHom x.1 * groupUnit x.2
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc, mul_left_comm, mul_comm]

def trivialUnits : Subgroup GroupRingˣ := signedUnit.range

theorem signedUnit_one (g : CyclicFive) : signedUnit (1, g) = groupUnit g := by
  apply Units.ext
  simp [signedUnit]

theorem signedUnit_minus (g : CyclicFive) :
    signedUnit (-1, g) = (-1 : GroupRingˣ) * groupUnit g := by
  apply Units.ext
  simp [signedUnit]

theorem trivialUnits_generated :
    trivialUnits = Subgroup.closure (Set.range groupUnit ∪ {(-1 : GroupRingˣ)}) := by
  apply le_antisymm
  · rintro _ ⟨⟨z, g⟩, rfl⟩
    rcases Int.units_eq_one_or z with rfl | rfl
    · rw [signedUnit_one]
      exact Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)
    · rw [signedUnit_minus]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
        (Subgroup.subset_closure (Or.inl ⟨g, rfl⟩))
  · rw [Subgroup.closure_le]
    rintro u (⟨g, rfl⟩ | hu)
    · exact ⟨(1, g), signedUnit_one g⟩
    · have h : u = (-1 : GroupRingˣ) := hu
      subst u
      exact ⟨(-1, 1), by rw [signedUnit_minus, map_one, mul_one]⟩

def trivialK1 : Subgroup (K1 GroupRing) :=
  trivialUnits.map (unitsToK1 GroupRing)

theorem trivialK1_generated :
    trivialK1 = Subgroup.closure
      (Set.range ((unitsToK1 GroupRing).comp groupUnit) ∪
        {unitsToK1 GroupRing (-1)}) := by
  rw [trivialK1, trivialUnits_generated, MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨x, (⟨g, rfl⟩ | hx), rfl⟩
    · exact Or.inl ⟨g, rfl⟩
    · have h : x = (-1 : GroupRingˣ) := hx
      subst x
      exact Or.inr rfl
  · rintro (⟨g, rfl⟩ | hu)
    · exact ⟨groupUnit g, Or.inl ⟨g, rfl⟩, rfl⟩
    · have h : u = unitsToK1 GroupRing (-1) := hu
      subst u
      exact ⟨-1, Or.inr rfl, rfl⟩

/-- The actual Whitehead quotient of K1 by the images of ±C5. -/
abbrev Whitehead := K1 GroupRing ⧸ trivialK1

def whiteheadUnit (u : GroupRingˣ) : Whitehead :=
  QuotientGroup.mk (unitsToK1 GroupRing u)

/-- The unit quotient is a detector only; it does not define K1 or Whitehead. -/
def whiteheadDeterminant : Whitehead →* GroupRingˣ ⧸ trivialUnits :=
  QuotientGroup.map trivialK1 trivialUnits (determinantK1 GroupRing) (by
    rintro _ ⟨u, hu, rfl⟩
    simpa [determinantK1_unit] using hu)

theorem whiteheadDeterminant_unit (u : GroupRingˣ) :
    whiteheadDeterminant (whiteheadUnit u) = QuotientGroup.mk u := by
  simp [whiteheadDeterminant, whiteheadUnit, determinantK1_unit]

theorem inverse_generator_ne : generator⁻¹ ≠ generator := by decide +kernel

def unitValue : GroupRing :=
  1 - MonoidAlgebra.single generator 1 - MonoidAlgebra.single generator⁻¹ 1

def inverseValue : GroupRing :=
  1 - MonoidAlgebra.single (generator ^ 2) 1 - MonoidAlgebra.single (generator⁻¹ ^ 2) 1

theorem unitValue_inverseValue : unitValue * inverseValue = 1 := by
  let t : GroupRing := MonoidAlgebra.single generator 1
  have ht : t ^ 5 = 1 := by
    dsimp [t]
    rw [MonoidAlgebra.single_pow, generator_pow_five, one_pow]
    rfl
  have hg4 : generator⁻¹ = generator ^ 4 := by decide +kernel
  have hg3 : generator⁻¹ ^ 2 = generator ^ 3 := by decide +kernel
  have hu : unitValue = 1 - t - t ^ 4 := by
    simp only [unitValue, t, MonoidAlgebra.single_pow, one_pow, hg4]
  have hv : inverseValue = 1 - t ^ 2 - t ^ 3 := by
    simp only [inverseValue, t, MonoidAlgebra.single_pow, one_pow, hg3]
  rw [hu, hv]
  linear_combination (t + t ^ 2) * ht

theorem inverseValue_unitValue : inverseValue * unitValue = 1 := by
  rw [mul_comm, unitValue_inverseValue]

/-- The negative of Milnor's Example6.6 unit, in the genuine integral group ring. -/
def counterUnit : GroupRingˣ :=
  ⟨unitValue, inverseValue, unitValue_inverseValue, inverseValue_unitValue⟩

theorem unitValue_generator : unitValue.coeff generator = -1 := by
  simp [unitValue, MonoidAlgebra.one_def, generator_ne_one, inverse_generator_ne]

theorem unitValue_inverse_generator : unitValue.coeff generator⁻¹ = -1 := by
  simp [unitValue, MonoidAlgebra.one_def, generator_ne_one, Ne.symm inverse_generator_ne]


theorem signedUnit_value (z : ℤˣ) (g : CyclicFive) :
    (signedUnit (z, g) : GroupRing) = MonoidAlgebra.single g (z : ℤ) := by
  change (Int.cast (z : ℤ) : GroupRing) * MonoidAlgebra.single g 1 = _
  simp [MonoidAlgebra.intCast_def]

theorem counterUnit_not_trivial : counterUnit ∉ trivialUnits := by
  rintro ⟨⟨z, g⟩, h⟩
  have hv := congrArg Units.val h
  rw [signedUnit_value] at hv
  have hg : g = generator := by
    by_contra hne
    have hc := congrArg (fun f : GroupRing => f.coeff generator) hv
    have hz : (0 : ℤ) = -1 := by
      simp [MonoidAlgebra.coeff_single, Ne.symm hne, counterUnit, unitValue_generator] at hc
    norm_num at hz
  subst g
  have hc := congrArg (fun f : GroupRing => f.coeff generator⁻¹) hv
  have hz : (0 : ℤ) = -1 := by
    simp [MonoidAlgebra.coeff_single, inverse_generator_ne, counterUnit, unitValue_inverse_generator] at hc
  norm_num at hz

theorem whitehead_counterUnit_ne_one : whiteheadUnit counterUnit ≠ 1 := by
  intro h
  have hc : (QuotientGroup.mk counterUnit : GroupRingˣ ⧸ trivialUnits) = 1 := by
    simpa [whiteheadDeterminant_unit] using congrArg whiteheadDeterminant h
  exact counterUnit_not_trivial ((QuotientGroup.eq_one_iff counterUnit).mp hc)

theorem whitehead_nontrivial : Nontrivial Whitehead :=
  ⟨⟨whiteheadUnit counterUnit, 1, whitehead_counterUnit_ne_one⟩⟩

/-- A genuine finite symmetric generating set for C5. -/
def generators : Finset CyclicFive := Finset.univ.erase 1

theorem generators_card : generators.card = 4 := by
  simp [generators, Finset.card_erase_of_mem]

theorem generators_symmetric (g : CyclicFive) (hg : g ∈ generators) :
    g⁻¹ ∈ generators := by
  simp only [generators, Finset.mem_erase, Finset.mem_univ, and_true] at hg ⊢
  exact inv_ne_one.mpr hg

theorem generators_generate : Subgroup.closure (generators : Set CyclicFive) = ⊤ := by
  apply top_unique
  intro g _
  by_cases h : g = 1
  · subst g
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simpa [generators] using h)

/-- The actual Cayley graph, whose walks are generator words. -/
def cayley : SimpleGraph CyclicFive := SimpleGraph.mulCayley (generators : Set CyclicFive)

theorem cayley_eq_complete : cayley = ⊤ := by
  have hs : (generators : Set CyclicFive) = ({1}ᶜ : Set CyclicFive) := by
    ext g
    simp [generators]
  rw [cayley, hs, SimpleGraph.mulCayley_compl_singleton_one]

theorem cayley_connected : cayley.Connected := by
  rw [cayley_eq_complete]
  exact SimpleGraph.connected_top

/-- Native shortest Cayley-walk length, with connectivity proved before using it. -/
def wordDistance (g h : CyclicFive) : ℕ := cayley.dist g h

theorem wordDistance_eq (g h : CyclicFive) :
    wordDistance g h = if g = h then 0 else 1 := by
  rw [wordDistance, cayley_eq_complete, SimpleGraph.dist_top]

theorem shortest_word_exists (g h : CyclicFive) :
    ∃ p : cayley.Walk g h, p.length = wordDistance g h :=
  cayley_connected.exists_walk_length_eq_dist g h

theorem wordDistance_triangle (g h k : CyclicFive) :
    wordDistance g k ≤ wordDistance g h + wordDistance h k :=
  cayley_connected.dist_triangle

/-- The actual finite-generator word metric, not an assigned hyperbolicity label. -/
instance wordMetric : MetricSpace CyclicFive where
  dist g h := (wordDistance g h : ℝ)
  dist_self g := by simp [wordDistance_eq]
  dist_comm g h := by
    exact_mod_cast (cayley.dist_comm : cayley.dist g h = cayley.dist h g)
  dist_triangle g h k := by exact_mod_cast wordDistance_triangle g h k
  eq_of_dist_eq_zero := by
    intro g h hh
    have hn : wordDistance g h = 0 := by exact_mod_cast hh
    exact cayley_connected.dist_eq_zero_iff.mp hn

theorem metric_is_word_length (g h : CyclicFive) :
    dist g h = (cayley.dist g h : ℝ) := rfl

theorem wordMetric_left_invariant (a g h : CyclicFive) :
    dist (a * g) (a * h) = dist g h := by
  change (wordDistance (a * g) (a * h) : ℝ) = (wordDistance g h : ℝ)
  simp only [wordDistance_eq, mul_left_cancel_iff]

theorem wordMetric_bounded (g h : CyclicFive) : dist g h ≤ 1 := by
  change (wordDistance g h : ℝ) ≤ 1
  rw [wordDistance_eq]
  split_ifs <;> norm_num

/-- Standard four-point Gromov hyperbolicity, with the conventional 2δ term. -/
def FourPointHyperbolic (δ : ℝ) : Prop :=
  ∀ a b c d : CyclicFive, dist a c + dist b d ≤
    max (dist a b + dist c d) (dist a d + dist b c) + 2 * δ

theorem cayley_four_point_hyperbolic : FourPointHyperbolic 1 := by
  intro a b c d
  have hac := wordMetric_bounded a c
  have hbd := wordMetric_bounded b d
  have hmax : 0 ≤ max (dist a b + dist c d) (dist a d + dist b c) :=
    le_trans (add_nonneg dist_nonneg dist_nonneg) (le_max_left _ _)
  linarith

theorem complete_counterexample :
    Fintype.card CyclicFive = 5 ∧ generators.card = 4 ∧
    Subgroup.closure (generators : Set CyclicFive) = ⊤ ∧
    (∀ g ∈ generators, g⁻¹ ∈ generators) ∧
    FourPointHyperbolic 1 ∧
    (∃ g : CyclicFive, g ≠ 1 ∧ g ^ 5 = 1) ∧
    (∃ w : Whitehead, w ≠ 1) :=
  ⟨cyclicFive_card, generators_card, generators_generate, generators_symmetric,
    cayley_four_point_hyperbolic, ⟨generator, generator_ne_one, generator_pow_five⟩,
    ⟨whiteheadUnit counterUnit, whitehead_counterUnit_ne_one⟩⟩

end

end TLMC1520
