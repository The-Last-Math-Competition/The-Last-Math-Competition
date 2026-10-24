import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section

namespace TLMC7730

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open scoped ComplexConjugate ENNReal Pointwise
open Monoid

abbrev Factor := Multiplicative (ZMod 3)
abbrev FreeProduct := Monoid.CoprodI (fun _ : ℕ => Factor)

def factorGenerator : Factor := Multiplicative.ofAdd 1

def factorEmbedding (i : ℕ) : Factor →* FreeProduct :=
  Monoid.CoprodI.of (M := fun _ : ℕ => Factor) (i := i)

theorem factorEmbedding_injective (i : ℕ) : Function.Injective (factorEmbedding i) :=
  Monoid.CoprodI.of_injective (M := fun _ : ℕ => Factor) i

def generator (i : ℕ) : FreeProduct := factorEmbedding i factorGenerator

theorem factorGenerator_ne_one : factorGenerator ≠ 1 := by decide +kernel

theorem generator_ne_one (i : ℕ) : generator i ≠ 1 := by
  intro h
  exact factorGenerator_ne_one (factorEmbedding_injective i (by simpa [generator] using h))

theorem factorGenerator_cube : factorGenerator ^ 3 = 1 := by decide +kernel

theorem generator_cube (i : ℕ) : generator i ^ 3 = 1 := by
  simpa [generator, ← map_pow] using congrArg (factorEmbedding i) factorGenerator_cube

instance freeProductCountable : Countable FreeProduct :=
  Function.Injective.countable
    (f := fun g : FreeProduct => (Monoid.CoprodI.Word.equiv g).toList)
    (fun _ _ h => Monoid.CoprodI.Word.equiv.injective (Monoid.CoprodI.Word.ext h))

/-- The genuine complex Hilbert space of square-summable functions on the free product. -/
abbrev Hilbert := lp (fun _ : FreeProduct => ℂ) 2
abbrev Operator := Hilbert →L[ℂ] Hilbert

def reindex (e : FreeProduct ≃ FreeProduct) : Hilbert ≃ₗᵢ[ℂ] Hilbert where
  toFun f := ⟨fun g => f (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun f := ⟨fun g => f (e.symm g), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' f h := by ext g; rfl
  map_smul' c f := by ext g; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun g => ‖f g‖ ^ (2 : ℝ≥0∞).toReal)

def regularIsometry (g : FreeProduct) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  reindex (Equiv.mulLeft g⁻¹)

/-- Bounded left-regular operators, with their actual multiplication laws. -/
def regular : FreeProduct →* Operator where
  toFun g := regularIsometry g
  map_one' := by ext f h; simp [regularIsometry, reindex]
  map_mul' g h := by
    ext f x
    simp [regularIsometry, reindex, mul_assoc]

theorem regular_apply (g : FreeProduct) (f : Hilbert) (h : FreeProduct) :
    regular g f h = f (g⁻¹ * h) := rfl

theorem regular_star (g : FreeProduct) : star (regular g) = regular g⁻¹ := by
  have h : star (regular g) * regular g = 1 := by
    change ContinuousLinearMap.adjoint (regular g) ∘L regular g = 1
    exact (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp
      (regularIsometry g).isometry
  calc
    star (regular g) = star (regular g) * (regular g * regular g⁻¹) := by
      rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = (star (regular g) * regular g) * regular g⁻¹ := (mul_assoc _ _ _).symm
    _ = regular g⁻¹ := by rw [h, one_mul]

theorem regular_unitary (g : FreeProduct) :
    star (regular g) * regular g = 1 ∧ regular g * star (regular g) = 1 := by
  rw [regular_star, ← map_mul, ← map_mul]
  simp

abbrev GroupAlgebra := MonoidAlgebra ℂ FreeProduct

/-- The actual faithful bounded regular representation of the entire group algebra. -/
def representation : GroupAlgebra →ₐ[ℂ] Operator :=
  MonoidAlgebra.lift ℂ Operator FreeProduct regular

theorem representation_single (g : FreeProduct) (c : ℂ) :
    representation (MonoidAlgebra.single g c) = c • regular g :=
  MonoidAlgebra.lift_single regular g c

def vacuum : Hilbert := lp.single 2 (1 : FreeProduct) (1 : ℂ)

theorem vacuum_apply (g : FreeProduct) : vacuum g = if g = 1 then 1 else 0 := by
  simp [vacuum, Pi.single_apply]

theorem vacuum_norm : ‖vacuum‖ = 1 := by simp [vacuum]

theorem representation_vacuum_coeff (a : GroupAlgebra) (h : FreeProduct) :
    representation a vacuum h = a.coeff h := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      change representation (MonoidAlgebra.single g 1) vacuum h = _
      rw [representation_single]
      simp [regular_apply, vacuum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
        inv_mul_eq_one, eq_comm]
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | smul c a ha => simpa using congrArg (c * ·) ha

theorem representation_injective : Function.Injective representation := by
  intro a b h
  ext g
  simpa only [representation_vacuum_coeff] using congrArg (fun T : Operator => T vacuum g) h

/-- This vector functional is a state; trace will be proved only on the regular algebra. -/
def vectorFunctional : Operator →ₗ[ℂ] ℂ where
  toFun T := inner ℂ vacuum (T vacuum)
  map_add' T S := by simp only [add_apply, inner_add_right]
  map_smul' c T := by simp only [smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply]

theorem vectorFunctional_representation (a : GroupAlgebra) :
    vectorFunctional (representation a) = a.coeff 1 := by
  change inner ℂ (lp.single 2 1 1) (representation a vacuum) = a.coeff 1
  rw [lp.inner_single_left, representation_vacuum_coeff]
  simp

theorem vectorFunctional_one : vectorFunctional 1 = 1 := by
  simp [vectorFunctional, vacuum, lp.inner_single_left]

theorem vectorFunctional_bound (T : Operator) : ‖vectorFunctional T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖vacuum‖ * ‖T vacuum‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖T‖ * 1) := by
      rw [vacuum_norm, one_mul, one_mul]
      simpa only [vacuum_norm] using T.le_opNorm vacuum
    _ = _ := by ring

def vectorState : Operator →L[ℂ] ℂ := vectorFunctional.mkContinuous 1 (by
  intro T
  simpa using vectorFunctional_bound T)

theorem vectorFunctional_positive (T : Operator) :
    vectorFunctional (star T * T) = (‖T vacuum‖ : ℂ) ^ 2 := by
  change inner ℂ vacuum (star T (T vacuum)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K (T vacuum)

theorem representation_star_closed (a : GroupAlgebra) :
    ∃ b : GroupAlgebra, representation b = star (representation a) := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      refine ⟨MonoidAlgebra.single g⁻¹ 1, ?_⟩
      change representation (MonoidAlgebra.single g⁻¹ 1) =
        star (representation (MonoidAlgebra.single g 1))
      simp [representation_single, regular_star]
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by simp [ha', hb']⟩
  | smul c a ha =>
      obtain ⟨a', ha'⟩ := ha
      exact ⟨star c • a', by simp [ha', star_smul]⟩

/-- The real represented star-algebra, on which the vacuum state is tracial. -/
def RegularAlgebra : StarSubalgebra ℂ Operator where
  toSubalgebra := representation.range
  star_mem' := by
    rintro T ⟨a, rfl⟩
    exact representation_star_closed a

theorem coeff_one_mul_comm (a b : GroupAlgebra) :
    (a * b).coeff 1 = (b * a).coeff 1 := by
  revert b
  refine MonoidAlgebra.induction_on (motive := fun a : GroupAlgebra =>
    ∀ b : GroupAlgebra, (a * b).coeff 1 = (b * a).coeff 1) a ?_ ?_ ?_
  · intro g b
    refine MonoidAlgebra.induction_on (motive := fun b : GroupAlgebra =>
      ((MonoidAlgebra.of ℂ FreeProduct) g * b).coeff 1 =
        (b * (MonoidAlgebra.of ℂ FreeProduct) g).coeff 1) b ?_ ?_ ?_
    · intro h
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, mul_eq_one_comm]
    · intro b c _ _
      simp [mul_add, add_mul]
    · intro c b _
      simp
  · intro a b ha hb c
    simpa [add_mul, mul_add] using congrArg₂ (· + ·) (ha c) (hb c)
  · intro c a ha b
    simpa [mul_smul_comm, smul_mul_assoc] using congrArg (c * ·) (ha b)

def trace : RegularAlgebra →ₗ[ℂ] ℂ :=
  vectorFunctional.comp RegularAlgebra.subtype.toAlgHom.toLinearMap

theorem trace_one : trace 1 = 1 := vectorFunctional_one

theorem trace_tracial (a b : RegularAlgebra) : trace (a * b) = trace (b * a) := by
  obtain ⟨a', ha⟩ := a.property
  obtain ⟨b', hb⟩ := b.property
  change vectorFunctional ((a : Operator) * (b : Operator)) =
    vectorFunctional ((b : Operator) * (a : Operator))
  rw [← ha, ← hb, ← map_mul, ← map_mul]
  change vectorFunctional (representation (a' * b')) = vectorFunctional (representation (b' * a'))
  rw [vectorFunctional_representation, vectorFunctional_representation]
  exact coeff_one_mul_comm a' b'

theorem trace_positive (a : RegularAlgebra) :
    trace (star a * a) = (‖(a : Operator) vacuum‖ : ℂ) ^ 2 :=
  vectorFunctional_positive a

theorem trace_bound (a : RegularAlgebra) : ‖trace a‖ ≤ ‖a‖ :=
  vectorFunctional_bound a

abbrev FactorAlgebra := MonoidAlgebra ℂ Factor

def factorAlgebra (i : ℕ) : FactorAlgebra →ₐ[ℂ] GroupAlgebra :=
  MonoidAlgebra.lift ℂ GroupAlgebra Factor
    ((MonoidAlgebra.of ℂ FreeProduct).comp (factorEmbedding i))

theorem factorAlgebra_single (i : ℕ) (g : Factor) (c : ℂ) :
    factorAlgebra i (MonoidAlgebra.single g c) = MonoidAlgebra.single (factorEmbedding i g) c := by
  simp [factorAlgebra, MonoidAlgebra.lift_single]

theorem factorAlgebra_trace (i : ℕ) (a : FactorAlgebra) :
    (factorAlgebra i a).coeff 1 = a.coeff 1 := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      change (factorAlgebra i (MonoidAlgebra.single g 1)).coeff 1 = _
      rw [factorAlgebra_single]
      have h : factorEmbedding i g = 1 ↔ g = 1 :=
        (factorEmbedding_injective i).eq_iff' (map_one _)
      simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, h]
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | smul c a ha => simpa using congrArg (c * ·) ha

theorem factorAlgebra_outside (i : ℕ) (a : FactorAlgebra) (g : FreeProduct)
    (hg : ∀ h : Factor, factorEmbedding i h ≠ g) : (factorAlgebra i a).coeff g = 0 := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
      change (factorAlgebra i (MonoidAlgebra.single h 1)).coeff g = 0
      rw [factorAlgebra_single]
      simp [MonoidAlgebra.coeff_single, hg h]
  | add a b ha hb => simp_all
  | smul c a ha => simp_all

theorem centered_factor_support (i : ℕ) (a : FactorAlgebra) (ha : a.coeff 1 = 0)
    (g : FreeProduct) (hg : g ∈ (factorAlgebra i a).coeff.support) :
    ∃ h : Factor, h ≠ 1 ∧ factorEmbedding i h = g := by
  have hnonzero : (factorAlgebra i a).coeff g ≠ 0 := Finsupp.mem_support_iff.mp hg
  have hrange : ∃ h : Factor, factorEmbedding i h = g := by
    by_contra h
    push Not at h
    exact hnonzero (factorAlgebra_outside i a g h)
  obtain ⟨h, rfl⟩ := hrange
  refine ⟨h, ?_, rfl⟩
  intro hh
  subst h
  exact hnonzero (by simpa only [map_one, factorAlgebra_trace] using ha)

def factorRepresentation (i : ℕ) : FactorAlgebra →ₐ[ℂ] Operator :=
  representation.comp (factorAlgebra i)

theorem factorRepresentation_single (i : ℕ) (g : Factor) (c : ℂ) :
    factorRepresentation i (MonoidAlgebra.single g c) = c • regular (factorEmbedding i g) := by
  simp [factorRepresentation, factorAlgebra_single, representation_single]

theorem factorRepresentation_star_closed (i : ℕ) (a : FactorAlgebra) :
    ∃ b : FactorAlgebra, factorRepresentation i b = star (factorRepresentation i a) := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      refine ⟨MonoidAlgebra.single g⁻¹ 1, ?_⟩
      change factorRepresentation i (MonoidAlgebra.single g⁻¹ 1) =
        star (factorRepresentation i (MonoidAlgebra.single g 1))
      simp [factorRepresentation_single, regular_star]
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by simp [ha', hb']⟩
  | smul c a ha =>
      obtain ⟨a', ha'⟩ := ha
      exact ⟨star c • a', by simp [ha', star_smul]⟩

def FactorOperators (i : ℕ) : StarSubalgebra ℂ Operator where
  toSubalgebra := (factorRepresentation i).range
  star_mem' := by
    rintro T ⟨a, rfl⟩
    exact factorRepresentation_star_closed i a

theorem factorRepresentation_trace (i : ℕ) (a : FactorAlgebra) :
    vectorFunctional (factorRepresentation i a) = a.coeff 1 := by
  change vectorFunctional (representation (factorAlgebra i a)) = _
  rw [vectorFunctional_representation, factorAlgebra_trace]

/-- Every nonzero product coefficient comes from an actual choice of nonidentity factor letters. -/
theorem support_product_letters (l : List (ℕ × FactorAlgebra))
    (hzero : ∀ p ∈ l, p.2.coeff 1 = 0) (g : FreeProduct)
    (hg : g ∈ (l.map (fun p => factorAlgebra p.1 p.2)).prod.coeff.support) :
    ∃ letters : List (Σ _ : ℕ, Factor),
      letters.map Sigma.fst = l.map Prod.fst ∧
      (∀ a ∈ letters, a.2 ≠ 1) ∧
      (letters.map (fun a => factorEmbedding a.1 a.2)).prod = g := by
  revert hzero g
  induction l with
  | nil =>
      intro hzero g hg
      have hg' : g = 1 := by simpa [MonoidAlgebra.one_def] using hg
      subst g
      exact ⟨[], rfl, by simp, by simp⟩
  | cons p l ih =>
      intro hzero g hg
      change g ∈ (factorAlgebra p.1 p.2 *
        (l.map (fun p => factorAlgebra p.1 p.2)).prod).coeff.support at hg
      obtain ⟨x, hx, y, hy, hxy⟩ :=
        Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset _ _ hg)
      obtain ⟨a, ha, hax⟩ := centered_factor_support p.1 p.2
        (hzero p (by simp)) x hx
      obtain ⟨letters, hindices, hnonidentity, hproduct⟩ :=
        ih (fun q hq => hzero q (by simp [hq])) y hy
      refine ⟨⟨p.1, a⟩ :: letters, by simp [hindices], ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hnonidentity b hb
      · simpa only [List.map_cons, List.prod_cons, hax, hproduct] using hxy

/-- The complete normal-form argument, for all nonempty centered alternating products. -/
theorem centered_alternating_coefficient (l : List (ℕ × FactorAlgebra)) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => a.1 ≠ b.1))
    (hzero : ∀ p ∈ l, p.2.coeff 1 = 0) :
    (l.map (fun p => factorAlgebra p.1 p.2)).prod.coeff 1 = 0 := by
  by_contra h
  have hs : (1 : FreeProduct) ∈
      (l.map (fun p => factorAlgebra p.1 p.2)).prod.coeff.support :=
    Finsupp.mem_support_iff.mpr h
  obtain ⟨letters, hindices, hnonidentity, hproduct⟩ := support_product_letters l hzero 1 hs
  have hc : (letters.map Sigma.fst).IsChain (· ≠ ·) := by
    rw [hindices]
    exact (List.isChain_map Prod.fst).mpr hchain
  let w : Monoid.CoprodI.Word (fun _ : ℕ => Factor) :=
    ⟨letters, hnonidentity, (List.isChain_map Sigma.fst).mp hc⟩
  have hwprod : w.prod = 1 := hproduct
  have hw : w = Monoid.CoprodI.Word.empty := by
    apply Monoid.CoprodI.Word.equiv.symm.injective
    change w.prod = Monoid.CoprodI.Word.empty.prod
    rw [Monoid.CoprodI.Word.prod_empty]
    exact hwprod
  have hempty : letters = [] := congrArg Monoid.CoprodI.Word.toList hw
  apply hne
  apply List.map_eq_nil_iff.mp
  rw [← hindices, hempty]
  rfl

theorem lift_centered_list (l : List (ℕ × Operator))
    (hmem : ∀ p ∈ l, p.2 ∈ FactorOperators p.1 ∧ vectorFunctional p.2 = 0) :
    ∃ a : List (ℕ × FactorAlgebra),
      a.map Prod.fst = l.map Prod.fst ∧
      a.map (fun p => factorRepresentation p.1 p.2) = l.map Prod.snd ∧
      (∀ p ∈ a, p.2.coeff 1 = 0) := by
  revert hmem
  induction l with
  | nil => intro _; exact ⟨[], rfl, rfl, by simp⟩
  | cons p l ih =>
      intro hmem
      have hp := hmem p (by simp)
      obtain ⟨a, ha⟩ : ∃ a, factorRepresentation p.1 a = p.2 := hp.1
      obtain ⟨b, hindices, hoperators, hzero⟩ :=
        ih (fun q hq => hmem q (by simp [hq]))
      have ha0 : a.coeff 1 = 0 := by
        rw [← factorRepresentation_trace p.1 a, ha]
        exact hp.2
      refine ⟨(p.1, a) :: b, by simp [hindices], by simp [ha, hoperators], ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ha0
      · exact hzero q hq

/-- Standard scalar freeness of actual unital star-subalgebras: all centered alternating words. -/
def FreelyIndependent (factors : ℕ → StarSubalgebra ℂ Operator) : Prop :=
  ∀ l : List (ℕ × Operator), l ≠ [] → l.IsChain (fun a b => a.1 ≠ b.1) →
    (∀ p ∈ l, p.2 ∈ factors p.1 ∧ vectorFunctional p.2 = 0) →
    vectorFunctional (l.map Prod.snd).prod = 0

theorem factors_freely_independent : FreelyIndependent FactorOperators := by
  intro l hne hchain hmem
  obtain ⟨a, hindices, hoperators, hzero⟩ := lift_centered_list l hmem
  have hane : a ≠ [] := by
    intro h
    apply hne
    have hh : l.map Prod.snd = [] := by rw [← hoperators, h]; rfl
    exact List.map_eq_nil_iff.mp hh
  have hachain : a.IsChain (fun p q => p.1 ≠ q.1) := by
    apply (List.isChain_map Prod.fst).mp
    rw [hindices]
    exact (List.isChain_map Prod.fst).mpr hchain
  have hproduct : (a.map (fun p => factorRepresentation p.1 p.2)).prod =
      representation (a.map (fun p => factorAlgebra p.1 p.2)).prod := by
    simp only [map_list_prod, List.map_map, factorRepresentation, AlgHom.comp_apply,
      Function.comp_def]
  rw [← hoperators, hproduct, vectorFunctional_representation]
  exact centered_alternating_coefficient a hane hachain hzero

def factorX : FactorAlgebra :=
  MonoidAlgebra.single factorGenerator 1 + MonoidAlgebra.single factorGenerator⁻¹ 1

def randomVariable (i : ℕ) : Operator := factorRepresentation i factorX

theorem randomVariable_eq (i : ℕ) :
    randomVariable i = regular (generator i) + star (regular (generator i)) := by
  simp [randomVariable, factorX, factorRepresentation_single, generator, regular_star]

theorem randomVariable_mem (i : ℕ) : randomVariable i ∈ FactorOperators i :=
  ⟨factorX, rfl⟩

theorem randomVariable_selfAdjoint (i : ℕ) : IsSelfAdjoint (randomVariable i) := by
  change star (randomVariable i) = randomVariable i
  rw [randomVariable_eq]
  simp [star_add, add_comm]

theorem factorX_centered : factorX.coeff 1 = 0 := by
  simp [factorX, MonoidAlgebra.coeff_single, factorGenerator_ne_one]

theorem randomVariable_centered (i : ℕ) : vectorFunctional (randomVariable i) = 0 := by
  rw [randomVariable, factorRepresentation_trace, factorX_centered]

theorem factorX_square : factorX ^ 2 = factorX + 2 := by
  let u : FactorAlgebra := MonoidAlgebra.single factorGenerator 1
  have hu3 : u ^ 3 = 1 := by
    simp only [u, MonoidAlgebra.single_pow, factorGenerator_cube, one_pow]
    rfl
  have hinv : factorGenerator⁻¹ = factorGenerator ^ 2 := by decide +kernel
  have hx : factorX = u + u ^ 2 := by
    simp only [factorX, u, MonoidAlgebra.single_pow, one_pow, hinv]
  rw [hx]
  linear_combination (u + 2) * hu3

theorem factorX_cube : factorX ^ 3 = 3 * factorX + 2 := by
  linear_combination (factorX + 1) * factorX_square

theorem factorX_fourth : factorX ^ 4 = 5 * factorX + 6 := by
  linear_combination (factorX ^ 2 + factorX + 3) * factorX_square

theorem randomVariable_square (i : ℕ) :
    randomVariable i ^ 2 = randomVariable i + 2 := by
  simpa only [map_pow, map_add, map_ofNat, randomVariable] using
    congrArg (factorRepresentation i) factorX_square

theorem randomVariable_moment (i k : ℕ) :
    vectorFunctional (randomVariable i ^ k) = (factorX ^ k).coeff 1 := by
  rw [randomVariable, ← map_pow, factorRepresentation_trace]

/-- The full polynomial law is independent of the factor index, not an assigned moment table. -/
theorem randomVariable_polynomial_law (i j : ℕ) (p : Polynomial ℂ) :
    vectorFunctional (Polynomial.aeval (randomVariable i) p) =
      vectorFunctional (Polynomial.aeval (randomVariable j) p) := by
  simp only [randomVariable, Polynomial.aeval_algHom_apply, factorRepresentation_trace]

theorem randomVariable_second (i : ℕ) : vectorFunctional (randomVariable i ^ 2) = 2 := by
  rw [randomVariable_moment, factorX_square]
  simp [factorX_centered, MonoidAlgebra.coeff_ofNat]

theorem randomVariable_third (i : ℕ) : vectorFunctional (randomVariable i ^ 3) = 2 := by
  rw [randomVariable_moment, factorX_cube]
  simp [MonoidAlgebra.ofNat_def, factorX_centered]

theorem randomVariable_fourth (i : ℕ) : vectorFunctional (randomVariable i ^ 4) = 6 := by
  rw [randomVariable_moment, factorX_fourth]
  simp [MonoidAlgebra.ofNat_def, factorX_centered]

theorem uniform_fourth_moments : ∀ i, ‖vectorFunctional (randomVariable i ^ 4)‖ ≤ 6 := by
  intro i
  rw [randomVariable_fourth]
  norm_num

theorem centered_two (i j : ℕ) (hij : i ≠ j) (a b : Operator)
    (ha : a ∈ FactorOperators i) (hb : b ∈ FactorOperators j)
    (za : vectorFunctional a = 0) (zb : vectorFunctional b = 0) :
    vectorFunctional (a * b) = 0 := by
  have h := factors_freely_independent [(i,a),(j,b)] (by simp)
    (by simpa using hij) (by simp_all)
  simpa using h

theorem centered_three (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (a b c : Operator) (ha : a ∈ FactorOperators i) (hb : b ∈ FactorOperators j)
    (hc : c ∈ FactorOperators k) (za : vectorFunctional a = 0)
    (zb : vectorFunctional b = 0) (zc : vectorFunctional c = 0) :
    vectorFunctional (a * b * c) = 0 := by
  have h := factors_freely_independent [(i,a),(j,b),(k,c)] (by simp)
    (by simp [hij, hjk]) (by simp_all)
  simpa [mul_assoc] using h

theorem mixed_second (i j : ℕ) (hij : i ≠ j) :
    vectorFunctional (randomVariable i * randomVariable j) = 0 :=
  centered_two i j hij _ _ (randomVariable_mem i) (randomVariable_mem j)
    (randomVariable_centered i) (randomVariable_centered j)

theorem mixed_third (i j k : ℕ) :
    vectorFunctional (randomVariable i * randomVariable j * randomVariable k) =
      if i = j ∧ j = k then 2 else 0 := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simpa [pow_succ, pow_two] using randomVariable_third i
    · have hsq := randomVariable_square i
      have htwo : (2 : Operator) = (2 : ℂ) • (1 : Operator) := by
        simp only [two_smul]
        exact one_add_one_eq_two.symm
      rw [if_neg (by simpa using hik), ← pow_two, hsq, add_mul, htwo, smul_mul_assoc,
        one_mul, map_add, map_smul, mixed_second i k hik, randomVariable_centered, smul_zero,
        add_zero]
  · by_cases hjk : j = k
    · subst k
      have htwo : (2 : Operator) = (2 : ℂ) • (1 : Operator) := by
        simp only [two_smul]
        exact one_add_one_eq_two.symm
      rw [if_neg (by simp [hij]), mul_assoc, ← pow_two, randomVariable_square,
        mul_add, htwo, mul_smul_comm, mul_one, map_add, map_smul,
        mixed_second i j hij, randomVariable_centered, smul_zero, add_zero]
    · rw [if_neg (by simp [hij])]
      exact centered_three i j k hij hjk _ _ _ (randomVariable_mem i)
        (randomVariable_mem j) (randomVariable_mem k) (randomVariable_centered i)
        (randomVariable_centered j) (randomVariable_centered k)

def rawSum (n : ℕ) : Operator := ∑ i ∈ Finset.range n, randomVariable i

theorem rawSum_third (n : ℕ) : vectorFunctional (rawSum n ^ 3) = 2 * (n : ℂ) := by
  simp only [rawSum, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum, map_sum]
  simp only [mixed_third]
  trans ∑ k ∈ Finset.range n, (2 : ℂ)
  · apply Finset.sum_congr rfl
    intro k hk
    calc
      (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
          if i = j ∧ j = k then (2 : ℂ) else 0) =
          ∑ j ∈ Finset.range n, if j = k then (2 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [ite_and, Finset.mem_range.mp hj]
      _ = 2 := by simp [hk]
  · simp [mul_comm]

def normalizedSum (n : ℕ) : Operator :=
  (↑(Real.sqrt (2 * (n : ℝ))) : ℂ)⁻¹ • rawSum n

theorem normalizedSum_third (n : ℕ) (hn : 0 < n) :
    vectorFunctional (normalizedSum n ^ 3) = (↑(Real.sqrt (2 * (n : ℝ))) : ℂ)⁻¹ := by
  rw [normalizedSum, smul_pow, map_smul, rawSum_third, smul_eq_mul]
  have hs : (↑(Real.sqrt (2 * (n : ℝ))) : ℂ) ^ 2 = 2 * (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hne : (↑(Real.sqrt (2 * (n : ℝ))) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show 0 < 2 * (n : ℝ) by positivity)).ne'
  rw [← hs]
  field_simp

def normalizedFactorX : FactorAlgebra := (↑(Real.sqrt 2) : ℂ)⁻¹ • factorX

def unitVarianceVariable (i : ℕ) : Operator := factorRepresentation i normalizedFactorX

theorem unitVarianceVariable_eq (i : ℕ) :
    unitVarianceVariable i = (↑(Real.sqrt 2) : ℂ)⁻¹ • randomVariable i := by
  simp [unitVarianceVariable, normalizedFactorX, randomVariable]

theorem unitVarianceVariable_polynomial_law (i j : ℕ) (p : Polynomial ℂ) :
    vectorFunctional (Polynomial.aeval (unitVarianceVariable i) p) =
      vectorFunctional (Polynomial.aeval (unitVarianceVariable j) p) := by
  simp only [unitVarianceVariable, Polynomial.aeval_algHom_apply, factorRepresentation_trace]

theorem unitVarianceVariable_mem (i : ℕ) : unitVarianceVariable i ∈ FactorOperators i :=
  ⟨normalizedFactorX, rfl⟩

theorem unitVarianceVariable_centered (i : ℕ) :
    vectorFunctional (unitVarianceVariable i) = 0 := by
  rw [unitVarianceVariable_eq, map_smul, randomVariable_centered, smul_zero]

theorem unitVarianceVariable_selfAdjoint (i : ℕ) : IsSelfAdjoint (unitVarianceVariable i) := by
  change star (unitVarianceVariable i) = unitVarianceVariable i
  rw [unitVarianceVariable_eq, star_smul]
  simp [show star (randomVariable i) = randomVariable i from randomVariable_selfAdjoint i]

theorem unitVarianceVariable_second (i : ℕ) :
    vectorFunctional (unitVarianceVariable i ^ 2) = 1 := by
  rw [unitVarianceVariable_eq, smul_pow, map_smul, randomVariable_second, smul_eq_mul]
  have hs : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [inv_pow, hs]
  norm_num

theorem unitVarianceVariable_fourth (i : ℕ) :
    vectorFunctional (unitVarianceVariable i ^ 4) = 3 / 2 := by
  rw [unitVarianceVariable_eq, smul_pow, map_smul, randomVariable_fourth, smul_eq_mul]
  have hs : (↑(Real.sqrt 2) : ℂ) ^ 4 = 4 := by
    have h2 : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = ((↑(Real.sqrt 2) : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [h2]; norm_num
  rw [inv_pow, hs]
  norm_num

theorem normalizedSum_standard_form (n : ℕ) :
    normalizedSum n = (↑(Real.sqrt (n : ℝ)) : ℂ)⁻¹ •
      ∑ i ∈ Finset.range n, unitVarianceVariable i := by
  simp only [normalizedSum, rawSum, unitVarianceVariable_eq, ← Finset.smul_sum,
    smul_smul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul,
    mul_inv_rev]

section Semicircle

open MeasureTheory Set Filter

/-- The standard variance-one Wigner semicircle density, with its genuine compact support. -/
def semicircleDensity (x : ℝ) : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (4 - x ^ 2)

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ semicircleDensity x := by
  unfold semicircleDensity
  positivity

theorem semicircleDensity_continuous : Continuous semicircleDensity := by
  unfold semicircleDensity
  fun_prop

theorem semicircleDensity_scaled (x : ℝ) :
    semicircleDensity (2 * x) = Real.pi⁻¹ * Real.sqrt (1 - x ^ 2) := by
  rw [semicircleDensity, show 4 - (2 * x) ^ 2 = 4 * (1 - x ^ 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  field_simp

theorem semicircleDensity_integrable :
    Integrable semicircleDensity (volume.restrict (Icc (-2) 2)) :=
  semicircleDensity_continuous.integrableOn_Icc

theorem semicircleDensity_integral :
    ∫ x, semicircleDensity x ∂volume.restrict (Icc (-2) 2) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := semicircleDensity) (a := (-1 : ℝ)) (b := 1) (c := 2) (by norm_num)
  have hleft : (∫ x in (-1 : ℝ)..1, semicircleDensity (2 * x)) = 1 / 2 := by
    simp_rw [semicircleDensity_scaled]
    rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
    field_simp
  norm_num only [smul_eq_mul] at hscale
  linarith

def standardSemicircle : Measure ℝ :=
  (volume.restrict (Icc (-2) 2)).withDensity (fun x => ENNReal.ofReal (semicircleDensity x))

instance standardSemicircle_probability : IsProbabilityMeasure standardSemicircle where
  measure_univ := by
    rw [standardSemicircle, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal semicircleDensity_integrable
      (Eventually.of_forall semicircleDensity_nonneg), semicircleDensity_integral]
    norm_num

/-- Integrability is checked separately, so the cubic integral is not a default zero. -/
theorem standardSemicircle_integrable_third :
    Integrable (fun x : ℝ => x ^ 3) standardSemicircle := by
  rw [standardSemicircle, integrable_withDensity_iff_integrable_smul'
    (semicircleDensity_continuous.measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (semicircleDensity_nonneg _), smul_eq_mul]
  exact (semicircleDensity_continuous.mul (continuous_id.pow 3)).integrableOn_Icc

theorem standardSemicircle_third : (∫ x : ℝ, x ^ 3 ∂standardSemicircle) = 0 := by
  rw [standardSemicircle, integral_withDensity_eq_integral_toReal_smul
    (semicircleDensity_continuous.measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (semicircleDensity_nonneg _), smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  let F : ℝ → ℝ := fun x => semicircleDensity x * x ^ 3
  have hodd : ∀ x, F (-x) = -F x := by
    intro x
    dsimp [F, semicircleDensity]
    rw [neg_sq]
    ring
  have hcomp := intervalIntegral.integral_comp_neg (f := F) (a := (-2 : ℝ)) (b := 2)
  norm_num only [neg_neg] at hcomp
  simp only [hodd, intervalIntegral.integral_neg] at hcomp
  change (∫ x in (-2 : ℝ)..2, F x) = 0
  linarith

end Semicircle

theorem factorOperators_le_regularAlgebra (i : ℕ) : FactorOperators i ≤ RegularAlgebra := by
  rintro T ⟨a, rfl⟩
  exact ⟨factorAlgebra i a, rfl⟩

/-- The bounded positive unital tracial state is on the actual regular star-algebra. -/
def probabilityState : RegularAlgebra →L[ℂ] ℂ := trace.mkContinuous 1 (by
  intro a
  simpa using trace_bound a)

theorem probabilityState_one : probabilityState 1 = 1 := trace_one

theorem probabilityState_tracial (a b : RegularAlgebra) :
    probabilityState (a * b) = probabilityState (b * a) := trace_tracial a b

theorem probabilityState_positive (a : RegularAlgebra) :
    probabilityState (star a * a) = (‖(a : Operator) vacuum‖ : ℂ) ^ 2 := trace_positive a

def RegularFactors (i : ℕ) : StarSubalgebra ℂ RegularAlgebra :=
  (FactorOperators i).comap RegularAlgebra.subtype

def algebraVariable (i : ℕ) : RegularAlgebra :=
  ⟨unitVarianceVariable i, factorOperators_le_regularAlgebra i (unitVarianceVariable_mem i)⟩

theorem algebraVariable_mem (i : ℕ) : algebraVariable i ∈ RegularFactors i :=
  unitVarianceVariable_mem i

theorem regular_freeness (l : List (ℕ × RegularAlgebra)) (hne : l ≠ [])
    (hchain : l.IsChain (fun a b => a.1 ≠ b.1))
    (hmem : ∀ p ∈ l, p.2 ∈ RegularFactors p.1 ∧ probabilityState p.2 = 0) :
    probabilityState (l.map Prod.snd).prod = 0 := by
  let operators := l.map (fun p => (p.1, (p.2 : Operator)))
  have hone : operators ≠ [] := by simpa [operators] using hne
  have hch : operators.IsChain (fun a b => a.1 ≠ b.1) := by
    simpa only [operators, List.isChain_map] using hchain
  have hm : ∀ p ∈ operators, p.2 ∈ FactorOperators p.1 ∧ vectorFunctional p.2 = 0 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hmem q hq
  have h := factors_freely_independent operators hone hch hm
  have hprod : RegularAlgebra.subtype (l.map Prod.snd).prod = (operators.map Prod.snd).prod := by
    rw [map_list_prod]
    simp only [operators, List.map_map, Function.comp_def]
    rfl
  change vectorFunctional (RegularAlgebra.subtype (l.map Prod.snd).prod) = 0
  rw [hprod]
  exact h

theorem algebraVariable_selfAdjoint (i : ℕ) : IsSelfAdjoint (algebraVariable i) := by
  apply Subtype.ext
  exact unitVarianceVariable_selfAdjoint i

theorem algebraVariable_centered (i : ℕ) : probabilityState (algebraVariable i) = 0 :=
  unitVarianceVariable_centered i

theorem algebraVariable_second (i : ℕ) : probabilityState (algebraVariable i ^ 2) = 1 :=
  unitVarianceVariable_second i

theorem algebraVariable_fourth (i : ℕ) : probabilityState (algebraVariable i ^ 4) = 3 / 2 :=
  unitVarianceVariable_fourth i

theorem algebraVariable_uniform_fourth :
    ∀ i, ‖probabilityState (algebraVariable i ^ 4)‖ ≤ 2 := by
  intro i
  rw [algebraVariable_fourth]
  norm_num

theorem algebraVariable_polynomial_law (i j : ℕ) (p : Polynomial ℂ) :
    probabilityState (Polynomial.aeval (algebraVariable i) p) =
      probabilityState (Polynomial.aeval (algebraVariable j) p) := by
  change vectorFunctional (RegularAlgebra.subtype (Polynomial.aeval (algebraVariable i) p)) =
    vectorFunctional (RegularAlgebra.subtype (Polynomial.aeval (algebraVariable j) p))
  have heval (k : ℕ) : RegularAlgebra.subtype (Polynomial.aeval (algebraVariable k) p) =
      Polynomial.aeval (unitVarianceVariable k) p :=
    (Polynomial.aeval_algHom_apply RegularAlgebra.subtype (algebraVariable k) p).symm
  rw [heval i, heval j]
  exact unitVarianceVariable_polynomial_law i j p

def cltSum (n : ℕ) : RegularAlgebra := (↑(Real.sqrt (n : ℝ)) : ℂ)⁻¹ •
  ∑ i ∈ Finset.range n, algebraVariable i

theorem cltSum_operator (n : ℕ) : (cltSum n : Operator) = normalizedSum n := by
  rw [normalizedSum_standard_form]
  simp [cltSum, algebraVariable]

theorem cltSum_third (n : ℕ) (hn : 0 < n) :
    probabilityState (cltSum n ^ 3) = (↑(Real.sqrt (2 * (n : ℝ))) : ℂ)⁻¹ := by
  change vectorFunctional (RegularAlgebra.subtype (cltSum n ^ 3)) = _
  have hpow : RegularAlgebra.subtype (cltSum n ^ 3) = normalizedSum n ^ 3 :=
    (map_pow RegularAlgebra.subtype (cltSum n) 3).trans
      (congrArg (fun T : Operator => T ^ 3) (cltSum_operator n))
  rw [hpow]
  exact normalizedSum_third n hn

def thirdMomentError (n : ℕ) : ℂ := probabilityState (cltSum n ^ 3) -
  (↑(∫ x : ℝ, x ^ 3 ∂standardSemicircle) : ℂ)

theorem thirdMomentError_norm (n : ℕ) (hn : 0 < n) :
    ‖thirdMomentError n‖ = (Real.sqrt (2 * (n : ℝ)))⁻¹ := by
  rw [thirdMomentError, standardSemicircle_third, Complex.ofReal_zero, sub_zero,
    cltSum_third n hn]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]

theorem no_harmonic_bound (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ C * ‖(n : ℝ)⁻¹‖ < ‖thirdMomentError n‖ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C ^ 2)
  let n := m + N + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hN : N ≤ n := by dsimp [n]; omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlarge : 2 * C ^ 2 < (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hs : 0 < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsq : (C * Real.sqrt (2 * (n : ℝ))) ^ 2 < (n : ℝ) ^ 2 := by
    rw [mul_pow, hs2]
    nlinarith [mul_pos (sub_pos.mpr hlarge) hnr]
  have hprod : C * Real.sqrt (2 * (n : ℝ)) < (n : ℝ) :=
    (sq_lt_sq₀ (mul_nonneg hC hs.le) hnr.le).mp hsq
  have hdiv : C / (n : ℝ) < 1 / Real.sqrt (2 * (n : ℝ)) := by
    apply (div_lt_div_iff₀ hnr hs).mpr
    simpa using hprod
  refine ⟨n, hN, hn, ?_⟩
  rw [thirdMomentError_norm n hn]
  simpa [one_div, Real.norm_eq_abs, abs_of_pos hnr, div_eq_mul_inv] using hdiv

theorem not_harmonic_moment_rate :
    ¬ Asymptotics.IsBigO Filter.atTop thirdMomentError (fun n : ℕ => (n : ℝ)⁻¹) := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h.exists_nonneg
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound.bound
  obtain ⟨n, hn, _, hfail⟩ := no_harmonic_bound C hC N
  exact not_lt_of_ge (hN n hn) hfail

theorem complete_counterexample :
    probabilityState 1 = 1 ∧
    (∀ a b : RegularAlgebra, probabilityState (a * b) = probabilityState (b * a)) ∧
    (∀ a : RegularAlgebra, probabilityState (star a * a) = (‖(a : Operator) vacuum‖ : ℂ) ^ 2) ∧
    (∀ l : List (ℕ × RegularAlgebra), l ≠ [] → l.IsChain (fun a b => a.1 ≠ b.1) →
      (∀ p ∈ l, p.2 ∈ RegularFactors p.1 ∧ probabilityState p.2 = 0) →
      probabilityState (l.map Prod.snd).prod = 0) ∧
    (∀ i, algebraVariable i ∈ RegularFactors i ∧ IsSelfAdjoint (algebraVariable i) ∧
      probabilityState (algebraVariable i) = 0 ∧ probabilityState (algebraVariable i ^ 2) = 1 ∧
      probabilityState (algebraVariable i ^ 4) = 3 / 2) ∧
    (∀ i, ‖probabilityState (algebraVariable i ^ 4)‖ ≤ 2) ∧
    (∀ i j (p : Polynomial ℂ), probabilityState (Polynomial.aeval (algebraVariable i) p) =
      probabilityState (Polynomial.aeval (algebraVariable j) p)) ∧
    MeasureTheory.IsProbabilityMeasure standardSemicircle ∧
    MeasureTheory.Integrable (fun x : ℝ => x ^ 3) standardSemicircle ∧
    (∫ x : ℝ, x ^ 3 ∂standardSemicircle) = 0 ∧
    ¬ Asymptotics.IsBigO Filter.atTop thirdMomentError (fun n : ℕ => (n : ℝ)⁻¹) :=
  ⟨probabilityState_one, probabilityState_tracial, probabilityState_positive, regular_freeness,
    fun i => ⟨algebraVariable_mem i, algebraVariable_selfAdjoint i, algebraVariable_centered i,
      algebraVariable_second i, algebraVariable_fourth i⟩,
    algebraVariable_uniform_fourth, algebraVariable_polynomial_law, inferInstance, standardSemicircle_integrable_third,
    standardSemicircle_third, not_harmonic_moment_rate⟩

end TLMC7730
