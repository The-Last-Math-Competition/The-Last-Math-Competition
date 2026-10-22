import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases

/-! Actual first-order syntax and models in the empty language. The source's
custom definition of a universal sentence is a sentence characterizing one
structure up to isomorphism; no target/signature restriction is supplied. -/
namespace TLMC5026
open FirstOrder
open FirstOrder.Language

abbrev L := FirstOrder.Language.empty

instance emptyInterpretation (M : Type*) : L.Structure M := Language.emptyStructure

theorem interpretation_unique (M : Type*) (i j : L.Structure M) : i=j :=
  Subsingleton.elim _ _

def equalityBody : L.BoundedFormula Empty 2 :=
  .equal (.var (.inr 1)) (.var (.inr 0))

def singletonSentence : L.Sentence := equalityBody.all.ex

def universalSingletonSentence : L.Sentence := equalityBody.all.all

/-- Count actual quantifier constructors; derived existential syntax is
expanded into negation/universal/negation, without adding extra binders. -/
def binderCount {n : ℕ} : L.BoundedFormula Empty n → ℕ
  | .falsum => 0
  | .equal _ _ => 0
  | .rel _ _ => 0
  | .imp φ ψ => binderCount φ + binderCount ψ
  | .all φ => binderCount φ + 1

/-- Maximum size of an actual bound-variable context occurring in the AST.
This is not the free-variable count of a closed sentence. -/
def contextWidth {n : ℕ} : L.BoundedFormula Empty n → ℕ
  | .falsum => n
  | .equal _ _ => n
  | .rel _ _ => n
  | .imp φ ψ => max (contextWidth φ) (contextWidth ψ)
  | .all φ => max n (contextWidth φ)

theorem actual_body_variables :
    equalityBody = FirstOrder.Language.BoundedFormula.equal
      (FirstOrder.Language.Term.var (Sum.inr (1:Fin 2)))
      (FirstOrder.Language.Term.var (Sum.inr (0:Fin 2))) := rfl

theorem actual_two_binder_syntax :
    singletonSentence = equalityBody.all.ex ∧
    binderCount singletonSentence = 2 ∧ contextWidth singletonSentence = 2 := by
  exact ⟨rfl,rfl,rfl⟩

theorem universal_two_binder_syntax :
    universalSingletonSentence = equalityBody.all.all ∧
    binderCount universalSingletonSentence = 2 ∧
    contextWidth universalSingletonSentence = 2 := by
  exact ⟨rfl,rfl,rfl⟩

theorem singleton_realize (M : Type*) [L.Structure M] :
    (M ⊨ singletonSentence) ↔ ∃ x : M, ∀ y : M, y=x := by
  simp [singletonSentence,equalityBody,Sentence.Realize,Formula.Realize,
    BoundedFormula.realize_ex,BoundedFormula.Realize,Term.realize,Fin.snoc]

theorem universal_realize (M : Type*) [L.Structure M] :
    (M ⊨ universalSingletonSentence) ↔ ∀ x y : M, y=x := by
  simp [universalSingletonSentence,equalityBody,Sentence.Realize,Formula.Realize,
    BoundedFormula.Realize,Term.realize,Fin.snoc]

theorem singleton_model : Unit ⊨ singletonSentence := by
  apply (singleton_realize Unit).mpr
  exact ⟨Unit.unit,fun y => Subsingleton.elim _ _⟩

noncomputable def singletonModelEquiv (M : Type*) [L.Structure M]
    (hM : M ⊨ singletonSentence) :
    M ≃[L] Unit := by
  let hex := (singleton_realize M).mp hM
  let x := Classical.choose hex
  have hx := Classical.choose_spec hex
  exact { toEquiv := {
    toFun := fun _ => Unit.unit
    invFun := fun _ => x
    left_inv := fun y => (hx y).symm
    right_inv := fun y => Subsingleton.elim _ _ } }

theorem singleton_iff_actual_model_iso (M : Type*) [L.Structure M] :
    (M ⊨ singletonSentence) ↔ Nonempty (M ≃[L] Unit) := by
  constructor
  · exact fun h => ⟨singletonModelEquiv M h⟩
  · rintro ⟨e⟩
    apply (singleton_realize M).mpr
    refine ⟨e.symm Unit.unit,fun y => ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _

theorem empty_not_model : ¬ (Empty ⊨ singletonSentence) := by
  rw [singleton_realize]
  rintro ⟨x,_⟩
  exact x.elim

theorem any_two_models_isomorphic (M N : Type*) [L.Structure M] [L.Structure N]
    (hM : M ⊨ singletonSentence) (hN : N ⊨ singletonSentence) :
    Nonempty (M ≃[L] N) := by
  let e : M ≃ N := (singletonModelEquiv M hM).toEquiv.trans
    (singletonModelEquiv N hN).toEquiv.symm
  exact ⟨{ toEquiv := e }⟩

theorem universal_iff_singleton_nonempty (M : Type*) [L.Structure M] [Nonempty M] :
    (M ⊨ universalSingletonSentence) ↔ (M ⊨ singletonSentence) := by
  rw [universal_realize,singleton_realize]
  constructor
  · intro h; exact ⟨Classical.choice inferInstance,fun y => h _ y⟩
  · rintro ⟨x,hx⟩ a b
    exact (hx b).trans (hx a).symm

theorem actual_two_variable_counterexample :
    ∃ φ : L.Sentence, binderCount φ = 2 ∧ contextWidth φ = 2 ∧
      (Unit ⊨ φ) ∧ ∀ (M : Type) [L.Structure M], (M ⊨ φ) → Nonempty (M ≃[L] Unit) := by
  refine ⟨singletonSentence,actual_two_binder_syntax.2.1,
    actual_two_binder_syntax.2.2,singleton_model,?_⟩
  intro M _ h
  exact ⟨singletonModelEquiv M h⟩

theorem no_global_four_variable_lower_bound :
    ¬ (∀ φ : L.Sentence,
      (Unit ⊨ φ) →
      (∀ (M : Type) [L.Structure M], (M ⊨ φ) → Nonempty (M ≃[L] Unit)) →
      4 ≤ contextWidth φ) := by
  intro h
  have hb := h singletonSentence singleton_model
    (fun M _ hM => ⟨singletonModelEquiv M hM⟩)
  rw [actual_two_binder_syntax.2.2] at hb
  exact (by decide : ¬ 4≤2) hb

end TLMC5026
