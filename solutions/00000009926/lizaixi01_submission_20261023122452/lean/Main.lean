import Mathlib.CategoryTheory.Skeletal
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Real.Basic

namespace TLMC9926
open CategoryTheory
universe u v
noncomputable section
open Classical
attribute [local instance] Classical.propDecidable

/-- Actual vector-space-valued persistence modules; morphisms are natural maps. -/
abbrev Persistence (J : Type u) [Category.{v} J] := J ⥤ ModuleCat.{0} ℚ
abbrev IsoClasses (J : Type u) [Category.{v} J] := Skeleton (Persistence J)

variable {J : Type u} [Category.{v} J]

def classInvariant (M : Persistence J) : IsoClasses J := toSkeleton M

theorem class_eq_iff (M N : Persistence J) :
    classInvariant M=classInvariant N ↔ Nonempty (M≅N) :=
  toSkeleton_eq_toSkeleton_iff

/-- Every component is a genuine finite-dimensional rational vector space. -/
def PointwiseFinite (M : Persistence J) : Prop :=
  ∀ j, FiniteDimensional ℚ (M.obj j)

def zeroModule : Persistence J :=
  (Functor.const J).obj (ModuleCat.of ℚ (Fin 0→ℚ))
def oneModule : Persistence J :=
  (Functor.const J).obj (ModuleCat.of ℚ ℚ)

theorem zero_pfd : PointwiseFinite (zeroModule : Persistence J) := by
  intro j; change FiniteDimensional ℚ (Fin 0→ℚ); infer_instance
theorem one_pfd : PointwiseFinite (oneModule : Persistence J) := by
  intro j; change FiniteDimensional ℚ ℚ; infer_instance

theorem zero_not_iso_one (j : J) :
    ¬Nonempty ((zeroModule : Persistence J)≅oneModule) := by
  rintro ⟨e⟩
  let l : (Fin 0→ℚ) ≃ₗ[ℚ] ℚ := (e.app j).toLinearEquiv
  have h : (1 : ℚ)=0 := l.symm.injective (Subsingleton.elim _ _)
  exact one_ne_zero h

/-- No numeric, computability or locality restriction is added to 'invariant'. -/
def IsInvariant {A : Type*} (I : Persistence J→A) : Prop :=
  ∀ M N, Nonempty (M≅N) → I M=I N

def IsComplete {A : Type*} (I : Persistence J→A) : Prop :=
  ∀ M N, I M=I N ↔ Nonempty (M≅N)

theorem class_isInvariant : IsInvariant (@classInvariant J _) := by
  intro M N h; exact (class_eq_iff M N).mpr h

theorem class_complete : IsComplete (@classInvariant J _) := class_eq_iff

def constantInvariant (_ : Persistence J) : IsoClasses J := classInvariant zeroModule

theorem constant_isInvariant : IsInvariant (@constantInvariant J _) := by
  intro M N _; rfl

theorem invariants_distinct (j : J) :
    (@classInvariant J _)≠constantInvariant := by
  intro h
  have he := congrFun h oneModule
  change classInvariant oneModule=classInvariant zeroModule at he
  have hi := (class_eq_iff oneModule zeroModule).mp he
  exact zero_not_iso_one j (hi.map Iso.symm)

def twoFamily : Finset (Persistence J→IsoClasses J) :=
  {classInvariant,constantInvariant}

theorem twoFamily_card (j : J) : (twoFamily (J:=J)).card=2 := by
  exact Finset.card_pair (invariants_distinct j)

def InvariantFamily (s : Finset (Persistence J→IsoClasses J)) : Prop :=
  ∀ I∈s, IsInvariant I

def CompleteFamily (s : Finset (Persistence J→IsoClasses J)) : Prop :=
  ∀ M N, (∀ I∈s, I M=I N) ↔ Nonempty (M≅N)

theorem twoFamily_invariant : InvariantFamily (twoFamily (J:=J)) := by
  intro I hI
  simp only [twoFamily,Finset.mem_insert,Finset.mem_singleton] at hI
  rcases hI with rfl|rfl
  · exact class_isInvariant
  · exact constant_isInvariant

theorem twoFamily_complete : CompleteFamily (twoFamily (J:=J)) := by
  intro M N
  constructor
  · intro h
    exact (class_eq_iff M N).mp (h classInvariant (by simp [twoFamily]))
  · intro h I hI
    exact twoFamily_invariant I hI M N h

theorem no_two_invariant_lower_bound (j : J) :
    ¬(∀ s : Finset (Persistence J→IsoClasses J), s.card=2 → InvariantFamily s →
      ∃ M N, ¬Nonempty (M≅N) ∧ ∀ I∈s, I M=I N) := by
  intro h
  obtain ⟨M,N,hne,heq⟩ := h twoFamily (twoFamily_card j) twoFamily_invariant
  exact hne ((twoFamily_complete M N).mp heq)

/-- Restriction to any genuine subclass of the same persistence modules. -/
def classOn (S : Persistence J→Prop) (M : {M // S M}) : IsoClasses J :=
  classInvariant M.val
def constantOn (S : Persistence J→Prop) (_ : {M // S M}) : IsoClasses J :=
  classInvariant zeroModule

theorem classOn_complete (S : Persistence J→Prop) (M N : {M // S M}) :
    classOn S M=classOn S N ↔ Nonempty (M.val≅N.val) := class_eq_iff M.val N.val

def twoFamilyOn (S : Persistence J→Prop) : Finset ({M // S M}→IsoClasses J) :=
  {classOn S,constantOn S}

theorem restricted_distinct (S : Persistence J→Prop)
    (h1 : S oneModule) (j : J) : classOn S≠constantOn S := by
  intro h
  have he := congrFun h ⟨oneModule,h1⟩
  change classInvariant oneModule=classInvariant zeroModule at he
  exact zero_not_iso_one j (((class_eq_iff oneModule zeroModule).mp he).map Iso.symm)

theorem restricted_family_card (S : Persistence J→Prop)
    (h1 : S oneModule) (j : J) : (twoFamilyOn S).card=2 :=
  Finset.card_pair (restricted_distinct S h1 j)

theorem restricted_family_invariant (S : Persistence J→Prop) :
    ∀ I∈twoFamilyOn S, ∀ M N : {M // S M}, Nonempty (M.val≅N.val) → I M=I N := by
  intro I hI M N h
  simp only [twoFamilyOn,Finset.mem_insert,Finset.mem_singleton] at hI
  rcases hI with rfl|rfl
  · exact (classOn_complete S M N).mpr h
  · rfl

theorem restricted_family_complete (S : Persistence J→Prop) (M N : {M // S M}) :
    (∀ I∈twoFamilyOn S, I M=I N) ↔ Nonempty (M.val≅N.val) := by
  constructor
  · intro h
    exact (classOn_complete S M N).mp (h (classOn S) (by simp [twoFamilyOn]))
  · intro h I hi
    exact restricted_family_invariant S I hi M N h

theorem pfd_two_complete (j : J) :
    ∃ s : Finset ({M : Persistence J // PointwiseFinite M}→IsoClasses J),
      s.card=2 ∧
      (∀ I∈s, ∀ M N, Nonempty (M.val≅N.val) → I M=I N) ∧
      (∀ M N, (∀ I∈s,I M=I N) ↔ Nonempty (M.val≅N.val)) :=
  ⟨twoFamilyOn PointwiseFinite,restricted_family_card PointwiseFinite one_pfd j,
    restricted_family_invariant PointwiseFinite,restricted_family_complete PointwiseFinite⟩

theorem pfd_no_two_invariant_lower_bound (j : J) :
    ¬(∀ s : Finset ({M : Persistence J // PointwiseFinite M}→IsoClasses J),
      s.card=2 →
      (∀ I∈s, ∀ M N, Nonempty (M.val≅N.val) → I M=I N) →
      ∃ M N, ¬Nonempty (M.val≅N.val) ∧ ∀ I∈s,I M=I N) := by
  intro h
  obtain ⟨s,hcard,hinv,hcomplete⟩ := pfd_two_complete j
  obtain ⟨M,N,hne,heq⟩ := h s hcard hinv
  exact hne ((hcomplete M N).mp heq)

abbrev DiscretePlane := ℕ×ℕ
abbrev ContinuousPlane := ℝ×ℝ

theorem discrete_two_parameter_counterexample :
    ¬(∀ s : Finset ({M : Persistence DiscretePlane // PointwiseFinite M}→IsoClasses DiscretePlane),
      s.card=2 →
      (∀ I∈s, ∀ M N, Nonempty (M.val≅N.val) → I M=I N) →
      ∃ M N, ¬Nonempty (M.val≅N.val) ∧ ∀ I∈s,I M=I N) :=
  pfd_no_two_invariant_lower_bound (0,0)

theorem real_two_parameter_counterexample :
    ¬(∀ s : Finset ({M : Persistence ContinuousPlane // PointwiseFinite M}→IsoClasses ContinuousPlane),
      s.card=2 →
      (∀ I∈s, ∀ M N, Nonempty (M.val≅N.val) → I M=I N) →
      ∃ M N, ¬Nonempty (M.val≅N.val) ∧ ∀ I∈s,I M=I N) :=
  pfd_no_two_invariant_lower_bound (0,0)

end
end TLMC9926
