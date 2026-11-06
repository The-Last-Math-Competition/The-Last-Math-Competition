import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.LanguageMap
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.FinCases

namespace TLMC1876
open FirstOrder FirstOrder.Language
universe u
noncomputable section

abbrev G := Equiv.Perm (Fin 5)

/-- Actual identity, inverse and multiplication symbols with their true arities. -/
inductive GroupSymbol : ℕ→Type
  | one : GroupSymbol 0
  | inv : GroupSymbol 1
  | mul : GroupSymbol 2

def groupLanguage : Language := ⟨GroupSymbol,fun _ => Empty⟩

instance groupInterpretation : groupLanguage.Structure G where
  funMap := fun {_} f xs => match f with
    | .one => 1
    | .inv => (xs 0)⁻¹
    | .mul => xs 0*xs 1
  RelMap := fun {_} r => r.elim

abbrev L := groupLanguage.withConstants G
instance namedGroupInterpretation : L.Structure G := inferInstance

def oneSymbol : L.Constants := Sum.inl GroupSymbol.one
def invSymbol : L.Functions 1 := Sum.inl GroupSymbol.inv
def mulSymbol : L.Functions 2 := Sum.inl GroupSymbol.mul

/-- The whole actual group is the definable domain x=x. -/
def domainFormula : L.Formula (Fin 1) := (Term.var 0).equal (Term.var 0)
def unitGraph : L.Formula (Fin 1) := oneSymbol.term.equal (Term.var 0)
def inverseGraph : L.Formula (Fin 2) :=
  (invSymbol.apply₁ (Term.var 0)).equal (Term.var 1)
def multiplicationGraph : L.Formula (Fin 3) :=
  (mulSymbol.apply₂ (Term.var 0) (Term.var 1)).equal (Term.var 2)

theorem domain_definable (v : Fin 1→G) : domainFormula.Realize v := by
  simp [domainFormula]
theorem unit_graph_realize (v : Fin 1→G) :
    unitGraph.Realize v ↔ 1=v 0 := by rfl
theorem inverse_graph_realize (v : Fin 2→G) :
    inverseGraph.Realize v ↔ (v 0)⁻¹=v 1 := by rfl
theorem multiplication_graph_realize (v : Fin 3→G) :
    multiplicationGraph.Realize v ↔ v 0*v 1=v 2 := by rfl

def nameValue (M : Type u) [L.Structure M] (g : G) : M :=
  Structure.funMap (groupLanguage.con g) Fin.elim0

def coverBody : L.BoundedFormula Empty 1 :=
  BoundedFormula.iSup (fun g : G =>
    BoundedFormula.equal (Term.var (Sum.inr 0))
      (Term.func (groupLanguage.con g) Fin.elim0))
def coverSentence : L.Sentence := coverBody.all

theorem cover_realize (M : Type u) [L.Structure M] :
    (M⊨coverSentence) ↔ Function.Surjective (nameValue M) := by
  simp [coverSentence,coverBody,Sentence.Realize,Formula.Realize,
    BoundedFormula.Realize,Term.realize,nameValue,Function.Surjective,eq_comm,Fin.snoc]
  constructor
  all_goals
    intro h a
    obtain ⟨g,hg⟩ := h a
    refine ⟨g,?_⟩
    convert hg using 1
    exact congrArg (Structure.funMap (groupLanguage.con g)) (Subsingleton.elim _ _)

theorem actual_cover : G⊨coverSentence := by
  rw [cover_realize]
  exact fun g => ⟨g,rfl⟩

def T : L.Theory := L.completeTheory G
theorem theory_complete : T.IsComplete := completeTheory.isComplete L G
theorem actual_model : G⊨T := by change G⊨L.completeTheory G; infer_instance

theorem every_model_nonempty (M : Type u) [L.Structure M] : Nonempty M :=
  ⟨nameValue M 1⟩

theorem every_model_finite (M : Type u) [L.Structure M] [M⊨T] : Finite M := by
  have hmem : coverSentence∈T := (mem_completeTheory).mpr actual_cover
  have hcov : M⊨coverSentence := T.realize_sentence_of_mem hmem
  exact Finite.of_surjective (nameValue M) ((cover_realize M).mp hcov)

/-- The genuine independence pattern, with arbitrary finite x/y tuple arities.
This is the pattern definition of NIP, not a finiteness predicate. -/
def HasIP (M : Type u) [L.Structure M] {m n : ℕ}
    (φ : L.Formula (Fin m ⊕ Fin n)) : Prop :=
  ∃ a : ℕ→(Fin m→M), ∃ b : Set ℕ→(Fin n→M),
    ∀ i s, φ.Realize (Sum.elim (a i) (b s)) ↔ i∈s

def DependentModel (M : Type u) [L.Structure M] : Prop :=
  ∀ m n : ℕ, ∀ φ : L.Formula (Fin m ⊕ Fin n), ¬HasIP M φ

theorem finite_model_dependent (M : Type u) [L.Structure M] [Finite M] :
    DependentModel M := by
  intro m n φ h
  obtain ⟨a,b,h⟩ := h
  have ha : Function.Injective a := by
    intro i j he
    have hi : φ.Realize (Sum.elim (a i) (b {i})) := (h i {i}).mpr (by simp)
    rw [he] at hi
    simpa using ((h j {i}).mp hi).symm
  have : Finite ℕ := Finite.of_injective a ha
  exact not_finite ℕ

/-- The full two-row ICT pattern: each witness selects exactly one index
in each row. Sequences need not even be indiscernible for our obstruction. -/
def HasICT (M : Type u) [L.Structure M] {m n : ℕ}
    (φ : L.Formula (Fin 1 ⊕ Fin m)) (ψ : L.Formula (Fin 1 ⊕ Fin n)) : Prop :=
  ∃ a : ℕ→(Fin m→M), ∃ b : ℕ→(Fin n→M), ∃ c : ℕ→ℕ→M,
    ∀ i j,
      (∀ i', φ.Realize (Sum.elim (fun _ => c i j) (a i')) ↔ i=i') ∧
      (∀ j', ψ.Realize (Sum.elim (fun _ => c i j) (b j')) ↔ j=j')

/-- Standard singleton-x, two-formula dp-minimality criterion. -/
def DpMinimalModel (M : Type u) [L.Structure M] : Prop :=
  ∀ m n : ℕ, ∀ φ : L.Formula (Fin 1 ⊕ Fin m),
    ∀ ψ : L.Formula (Fin 1 ⊕ Fin n), ¬HasICT M φ ψ

theorem finite_model_dpMinimal (M : Type u) [L.Structure M] [Finite M] :
    DpMinimalModel M := by
  intro m n φ ψ h
  obtain ⟨a,b,c,h⟩ := h
  have hc : Function.Injective (fun i => c i 0) := by
    intro i j he
    change c i 0=c j 0 at he
    have hi : φ.Realize (Sum.elim (fun _ => c i 0) (a i)) := (h i 0).1 i |>.mpr rfl
    rw [he] at hi
    exact ((h j 0).1 i).mp hi |>.symm
  have : Finite ℕ := Finite.of_injective (fun i => c i 0) hc
  exact not_finite ℕ

def DependentTheory (S : L.Theory) : Prop :=
  ∀ (M : Type u) [L.Structure M] [M⊨S], DependentModel M
def DpMinimalTheory (S : L.Theory) : Prop :=
  ∀ (M : Type u) [L.Structure M] [M⊨S], DpMinimalModel M

theorem theory_dependent : DependentTheory.{u} T := by
  intro M _ _
  have := every_model_finite M
  exact finite_model_dependent M

theorem theory_dpMinimal : DpMinimalTheory.{u} T := by
  intro M _ _
  have := every_model_finite M
  exact finite_model_dpMinimal M

theorem group_not_solvable : ¬Group.IsSolvable G := Equiv.Perm.not_isSolvable_fin_5

theorem actual_counterexample :
    T.IsComplete ∧ (G⊨T) ∧ DependentTheory.{u} T ∧ DpMinimalTheory.{u} T ∧
    (∀ v : Fin 1→G,domainFormula.Realize v) ∧
    (∀ v : Fin 1→G,unitGraph.Realize v ↔ 1=v 0) ∧
    (∀ v : Fin 2→G,inverseGraph.Realize v ↔ (v 0)⁻¹=v 1) ∧
    (∀ v : Fin 3→G,multiplicationGraph.Realize v ↔ v 0*v 1=v 2) ∧
    ¬Group.IsSolvable G :=
  ⟨theory_complete,actual_model,theory_dependent,theory_dpMinimal,domain_definable,
    unit_graph_realize,inverse_graph_realize,multiplication_graph_realize,group_not_solvable⟩

end
end TLMC1876
