import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Order.Preorder.Chain
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set

namespace Conjecture9783

attribute [local instance] Classical.propDecidable

/-- The standard internal definition of AF approximation by closed finite-dimensional stages. -/
def ApproximatelyFinite (A : Type) [CStarAlgebra A] : Prop :=
  ∃ S : ℕ → StarSubalgebra ℂ A, Monotone S ∧
    (∀ n, FiniteDimensional ℂ (S n)) ∧ (∀ n, IsClosed (S n : Set A)) ∧
    Dense (⋃ n, (S n : Set A))

def complexStages : ℕ → StarSubalgebra ℂ ℂ := fun _ => ⊤

def stageScalarEquiv (n : ℕ) : complexStages n ≃⋆ₐ[ℂ] ℂ where
  toFun x := x.val
  invFun z := ⟨z, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

theorem complex_approximatelyFinite : ApproximatelyFinite ℂ := by
  refine ⟨complexStages, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact le_rfl
  · intro n
    exact FiniteDimensional.of_injective (complexStages n).subtype.toAlgHom.toLinearMap
      Subtype.val_injective
  · intro n
    exact isClosed_univ
  · simpa only [complexStages, StarSubalgebra.coe_top, Set.iUnion_const] using
      (dense_univ : Dense (Set.univ : Set ℂ))

/-- A concrete full matrix block, rather than merely the label 'dimension one'. -/
def scalarMatrixEquiv : ℂ ≃⋆ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ where
  toFun z _ _ := z
  invFun M := M 0 0
  left_inv _ := rfl
  right_inv M := by ext i j; fin_cases i; fin_cases j; rfl
  map_mul' z w := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  map_star' _ := by ext i j; fin_cases i; fin_cases j; rfl
  map_smul' _ _ := rfl

def stageMatrixEquiv (n : ℕ) :
    complexStages n ≃⋆ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ :=
  (stageScalarEquiv n).trans scalarMatrixEquiv

def connecting (_ : ℕ) : ℂ →⋆ₐ[ℂ] ℂ := StarAlgHom.id ℂ ℂ

theorem connecting_identity (n : ℕ) (z : ℂ) : connecting n z = z := rfl

theorem internal_external_stage_compatibility (n : ℕ) (x : complexStages n) :
    (((stageScalarEquiv (n + 1)).symm (connecting n (stageScalarEquiv n x))) : ℂ) = x.val :=
  rfl

def matrixConnecting (n : ℕ) :
    Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ :=
  (scalarMatrixEquiv : ℂ →⋆ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ).comp
    ((connecting n).comp (scalarMatrixEquiv.symm : Matrix (Fin 1) (Fin 1) ℂ →⋆ₐ[ℂ] ℂ))

theorem matrixConnecting_identity (n : ℕ) : matrixConnecting n = StarAlgHom.id ℂ _ := by
  ext M i j
  fin_cases i
  fin_cases j
  rfl

/-- Every map out of a stage is continuous, as required in the C-star category. -/
theorem cocone_map_continuous {B : Type} [CStarAlgebra B] (f : ℂ →⋆ₐ[ℂ] B) :
    Continuous f := f.toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-- C is the actual direct limit of the constant identity system, with all inclusions identity. -/
theorem constant_system_universal (B : Type) [CStarAlgebra B]
    (f : ℕ → ℂ →⋆ₐ[ℂ] B)
    (hf : ∀ n, (f (n + 1)).comp (connecting n) = f n) :
    ∃! g : ℂ →⋆ₐ[ℂ] B, ∀ n, g.comp (connecting n) = f n := by
  have heq : ∀ n, f n = f 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hstep : f (n + 1) = f n := by simpa [connecting] using hf n
      exact hstep.trans ih
  refine ⟨f 0, ?_, ?_⟩
  · intro n
    simpa [connecting] using (heq n).symm
  · intro g hg
    simpa [connecting] using hg 0

/-- The same limit property also allows nonunital targets and nonunital star maps. -/
theorem constant_system_universal_nonunital (B : Type) [NonUnitalCStarAlgebra B]
    (f : ℕ → ℂ →⋆ₙₐ[ℂ] B)
    (hf : ∀ n, (f (n + 1)).comp (NonUnitalStarAlgHom.id ℂ ℂ) = f n) :
    ∃! g : ℂ →⋆ₙₐ[ℂ] B,
      (∀ n, g.comp (NonUnitalStarAlgHom.id ℂ ℂ) = f n) ∧ Continuous g := by
  have heq : ∀ n, f n = f 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hstep : f (n + 1) = f n := by simpa using hf n
      exact hstep.trans ih
  refine ⟨f 0, ⟨?_, ?_⟩, ?_⟩
  · intro n
    simpa using (heq n).symm
  · let L : ℂ →ₗ[ℂ] B :=
      { toFun := f 0
        map_add' := map_add (f 0)
        map_smul' := map_smul (f 0) }
    exact L.continuous_of_finiteDimensional
  · intro g hg
    simpa using hg.1 0

/-- Actual multiplicity of the unique simple block: the image of the rank-one unit corner. -/
def edgeMultiplicity (n : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (connecting n).toAlgHom.toLinearMap)

theorem edgeMultiplicity_one (n : ℕ) : edgeMultiplicity n = 1 := by
  change Module.finrank ℂ (LinearMap.range (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) = 1
  rw [LinearMap.finrank_range_of_inj Function.injective_id, Module.finrank_self]

instance bratteliQuiver : Quiver ℕ where
  Hom n m := Fin (if m = n + 1 then edgeMultiplicity n else 0)

def uniqueEdge (n : ℕ) : n ⟶ n + 1 := ⟨0, by simp [edgeMultiplicity_one]⟩

def rayPath : (n : ℕ) → Quiver.Path 0 n
  | 0 => .nil
  | n + 1 => (rayPath n).cons (uniqueEdge n)

theorem rayPath_length (n : ℕ) : (rayPath n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rayPath] using congrArg Nat.succ ih

def pathDepth : ℕ∞ := ⨆ (a : ℕ) (b : ℕ) (p : Quiver.Path a b), (p.length : ℕ∞)

theorem pathDepth_infinite : pathDepth = ⊤ := by
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  have h : ((rayPath n).length : ℕ∞) ≤ pathDepth :=
    le_iSup_of_le 0 (le_iSup_of_le n (le_iSup_of_le (rayPath n) le_rfl))
  simpa [rayPath_length] using h

/-- Closed two-sided ideals; commutativity makes Mathlib's Ideal the appropriate notion. -/
def ClosedIdeal (A : Type) [CommRing A] [TopologicalSpace A] :=
  {I : Ideal A // IsClosed (I : Set A)}

instance {A : Type} [CommRing A] [TopologicalSpace A] : PartialOrder (ClosedIdeal A) :=
  inferInstanceAs (PartialOrder {I : Ideal A // IsClosed (I : Set A)})

def zeroIdeal : ClosedIdeal ℂ := ⟨⊥, by simp⟩
def wholeIdeal : ClosedIdeal ℂ := ⟨⊤, isClosed_univ⟩

theorem every_ideal (I : ClosedIdeal ℂ) : I = zeroIdeal ∨ I = wholeIdeal := by
  rcases Ideal.eq_bot_or_top I.val with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem zero_ne_whole : zeroIdeal ≠ wholeIdeal := by
  intro h
  have hi : (⊥ : Ideal ℂ) = ⊤ := congrArg Subtype.val h
  exact bot_ne_top hi

def idealsEquiv : ClosedIdeal ℂ ≃ Fin 2 where
  toFun I := if I = zeroIdeal then 0 else 1
  invFun i := if i = 0 then zeroIdeal else wholeIdeal
  left_inv I := by rcases every_ideal I with rfl | rfl <;> simp [zero_ne_whole.symm]
  right_inv i := by fin_cases i <;> simp [zero_ne_whole.symm]

instance : Fintype (ClosedIdeal ℂ) := Fintype.ofEquiv (Fin 2) idealsEquiv.symm

theorem closedIdeal_card : Fintype.card (ClosedIdeal ℂ) = 2 :=
  (Fintype.card_congr idealsEquiv).trans (Fintype.card_fin 2)

theorem all_ideals_comparable (I J : ClosedIdeal ℂ) : I ≤ J ∨ J ≤ I := by
  rcases every_ideal I with rfl | rfl <;> rcases every_ideal J with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inl (show (⊥ : Ideal ℂ) ≤ ⊤ from bot_le)
  · exact Or.inr (show (⊥ : Ideal ℂ) ≤ ⊤ from bot_le)
  · exact Or.inl le_rfl

theorem all_ideals_chain : IsChain (· ≤ ·) (Set.univ : Set (ClosedIdeal ℂ)) := by
  intro I _ J _ _
  exact all_ideals_comparable I J

theorem maximal_chain_is_all (s : Set (ClosedIdeal ℂ))
    (hs : IsMaxChain (· ≤ ·) s) : s = Set.univ :=
  hs.2 all_ideals_chain (Set.subset_univ s)

theorem strict_chain_size_bound (n : ℕ) (f : Fin n → ClosedIdeal ℂ) (hf : StrictMono f) :
    n ≤ 2 := by
  have h := Fintype.card_le_of_injective f hf.injective
  simpa [closedIdeal_card] using h

def idealChainLength {A : Type} [CommRing A] [TopologicalSpace A] : ℕ∞ :=
  ⨆ (n : ℕ) (f : Fin (n + 1) → ClosedIdeal A) (_ : StrictMono f), (n : ℕ∞)

theorem idealChainLength_le_one : idealChainLength (A := ℂ) ≤ 1 := by
  apply iSup_le
  intro n
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  have hn := strict_chain_size_bound (n + 1) f hf
  exact_mod_cast (show n ≤ 1 by omega)

def twoIdealChain (i : Fin 2) : ClosedIdeal ℂ := if i = 0 then zeroIdeal else wholeIdeal

theorem twoIdealChain_strict : StrictMono twoIdealChain := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num at hab ⊢
  change (⊥ : Ideal ℂ) < ⊤
  exact bot_lt_top

theorem idealChainLength_one : idealChainLength (A := ℂ) = 1 := by
  apply le_antisymm idealChainLength_le_one
  exact le_iSup_of_le 1 (le_iSup_of_le twoIdealChain
    (le_iSup_of_le twoIdealChain_strict le_rfl))

def idealChainElements {A : Type} [CommRing A] [TopologicalSpace A] : ℕ∞ :=
  ⨆ (n : ℕ) (f : Fin n → ClosedIdeal A) (_ : StrictMono f), (n : ℕ∞)

theorem idealChainElements_two : idealChainElements (A := ℂ) = 2 := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact_mod_cast strict_chain_size_bound n f hf
  · exact le_iSup_of_le 2 (le_iSup_of_le twoIdealChain
      (le_iSup_of_le twoIdealChain_strict le_rfl))

/-- A necessary restriction of the source's universal depth equality to this actual AF diagram. -/
def DepthEqualityClause : Prop :=
  ApproximatelyFinite ℂ → idealChainLength (A := ℂ) = pathDepth

theorem disprove_depth_equality : ¬DepthEqualityClause := by
  intro h
  have hbad := h complex_approximatelyFinite
  rw [idealChainLength_one, pathDepth_infinite] at hbad
  exact ENat.coe_ne_top 1 hbad

/-- The restriction to constant one-block presentations of AF algebras isomorphic to C.
Each supplied isomorphism identifies the sole stage summand with M_1(C),
and its identity connecting maps have the ray diagram above. -/
def OneBlockDepthClause : Prop :=
  ∀ (A : Type) [CommCStarAlgebra A], ApproximatelyFinite A →
    Nonempty (ℂ ≃⋆ₐ[ℂ] A) → idealChainLength (A := A) = pathDepth

theorem conjecture_9783_false : ¬OneBlockDepthClause := by
  intro h
  have hbad := h ℂ complex_approximatelyFinite ⟨StarAlgEquiv.refl⟩
  rw [idealChainLength_one, pathDepth_infinite] at hbad
  exact ENat.coe_ne_top 1 hbad

theorem elements_convention_false : idealChainElements (A := ℂ) ≠ pathDepth := by
  rw [idealChainElements_two, pathDepth_infinite]
  exact ENat.coe_ne_top 2

#print axioms complex_approximatelyFinite
#print axioms scalarMatrixEquiv
#print axioms stageMatrixEquiv
#print axioms edgeMultiplicity_one
#print axioms matrixConnecting_identity
#print axioms constant_system_universal
#print axioms constant_system_universal_nonunital
#print axioms pathDepth_infinite
#print axioms idealChainLength_one
#print axioms idealChainElements_two
#print axioms maximal_chain_is_all
#print axioms disprove_depth_equality
#print axioms conjecture_9783_false

end Conjecture9783
