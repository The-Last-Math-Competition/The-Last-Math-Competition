import Mathlib.Order.Atoms
import Mathlib.Order.ModularLattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.IntervalCases

namespace Conjecture8551

/-- The partition lattice on a three-element set: bottom, three pair merges, top. -/
inductive ThreePartitions where
  | discrete | pair01 | pair02 | pair12 | indiscrete
  deriving DecidableEq, Fintype

open ThreePartitions

def refines (x y : ThreePartitions) : Prop :=
  x = discrete ∨ y = indiscrete ∨ x = y

instance : DecidableRel refines := fun _ _ => by unfold refines; infer_instance

instance : PartialOrder ThreePartitions where
  le := refines
  le_refl x := Or.inr (Or.inr rfl)
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := ThreePartitions) (· ≤ ·) := fun _ _ => inferInstanceAs (Decidable (refines _ _))

instance : DecidableRel (α := ThreePartitions) (· < ·) :=
  fun _ _ => decidable_of_iff _ lt_iff_le_not_le.symm

def join (x y : ThreePartitions) : ThreePartitions :=
  if x = discrete then y else if y = discrete then x else if x = y then x else indiscrete

def meet (x y : ThreePartitions) : ThreePartitions :=
  if x = indiscrete then y else if y = indiscrete then x else if x = y then x else discrete

instance : Lattice ThreePartitions where
  sup := join
  inf := meet
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder ThreePartitions where
  bot := discrete
  top := indiscrete
  bot_le := by decide
  le_top := by decide

instance : IsModularLattice ThreePartitions where
  sup_inf_le_assoc_of_le := by decide

theorem atoms_join (x : ThreePartitions) :
    IsLUB {a : ThreePartitions | IsAtom a ∧ a ≤ x} x := by
  revert x
  unfold IsLUB IsLeast upperBounds lowerBounds IsAtom
  simp only [Set.mem_setOf_eq]
  decide

instance : IsAtomistic ThreePartitions where
  isLUB_atoms x := ⟨{a | IsAtom a ∧ a ≤ x}, atoms_join x, fun _ h => h.1⟩

def rank : ThreePartitions → ℕ
  | discrete => 0
  | indiscrete => 2
  | _ => 1

theorem rank_cover : ∀ a b : ThreePartitions,
    a < b → (∀ c, a < c → ¬c < b) → rank b = rank a + 1 := by decide

/-- Explicit block labels; equality of labels is membership in the same partition block. -/
def blockLabel : ThreePartitions → Fin 3 → Fin 3
  | discrete, i => i
  | pair01, i => if i = 2 then 1 else 0
  | pair02, i => if i = 1 then 1 else 0
  | pair12, i => if i = 0 then 0 else 1
  | indiscrete, _ => 0

def partition (x : ThreePartitions) : Setoid (Fin 3) :=
  Setoid.ker (blockLabel x)

theorem refinement_semantics : ∀ x y : ThreePartitions,
    x ≤ y ↔ ∀ i j : Fin 3, (partition x).r i j → (partition y).r i j := by
  change ∀ x y, x ≤ y ↔ ∀ i j, blockLabel x i = blockLabel x j →
    blockLabel y i = blockLabel y j
  decide

theorem all_partitions (s : Setoid (Fin 3)) : ∃ x, partition x = s := by
  have hs01 : s.r 1 0 ↔ s.r 0 1 := ⟨s.symm, s.symm⟩
  have hs02 : s.r 2 0 ↔ s.r 0 2 := ⟨s.symm, s.symm⟩
  have hs12 : s.r 2 1 ↔ s.r 1 2 := ⟨s.symm, s.symm⟩
  have h00 : s.r (0 : Fin 3) 0 := s.refl _
  have h11 : s.r (1 : Fin 3) 1 := s.refl _
  have h22 : s.r (2 : Fin 3) 2 := s.refl _
  by_cases h01 : s.r 0 1 <;> by_cases h02 : s.r 0 2 <;> by_cases h12 : s.r 1 2
  · refine ⟨indiscrete, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [partition, Setoid.ker, Function.onFun, blockLabel]

  · exact False.elim (h12 (s.trans (s.symm h01) h02))
  · exact False.elim (h02 (s.trans h01 h12))
  · refine ⟨pair01, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [partition, Setoid.ker, Function.onFun, blockLabel]
  · exact False.elim (h01 (s.trans h02 (s.symm h12)))
  · refine ⟨pair02, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [partition, Setoid.ker, Function.onFun, blockLabel]
  · refine ⟨pair12, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [partition, Setoid.ker, Function.onFun, blockLabel]
  · refine ⟨discrete, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [partition, Setoid.ker, Function.onFun, blockLabel]

noncomputable def partitionOrderIso : ThreePartitions ≃o Setoid (Fin 3) where
  toFun := partition
  invFun s := Classical.choose (all_partitions s)
  left_inv x := by
    have he := Classical.choose_spec (all_partitions (partition x))
    apply le_antisymm
    · exact (refinement_semantics _ _).mpr (fun i j hij => he ▸ hij)
    · exact (refinement_semantics _ _).mpr (fun i j hij => he.symm ▸ hij)
  right_inv s := Classical.choose_spec (all_partitions s)
  map_rel_iff' := by
    intro x y
    exact (refinement_semantics x y).symm

def mu : ThreePartitions → ℤ
  | discrete => 1
  | indiscrete => 2
  | _ => -1

/-- The defining bottom-row recurrence of the incidence-algebra Mobius function. -/
def IsMobiusRow {α : Type} [Fintype α] [DecidableEq α] [PartialOrder α]
    [OrderBot α] [DecidableRel (α := α) (· ≤ ·)] (m : α → ℤ) : Prop :=
  ∀ x, ∑ y ∈ Finset.univ.filter (· ≤ x), m y = if x = ⊥ then 1 else 0

theorem mu_recurrence : IsMobiusRow mu := by unfold IsMobiusRow; decide

theorem mu_unique (m : ThreePartitions → ℤ) (hm : IsMobiusRow m) : m = mu := by
  change ∀ x, ∑ y ∈ Finset.univ.filter (fun y => refines y x), m y =
    if x = discrete then 1 else 0 at hm
  have hu : (Finset.univ : Finset ThreePartitions) =
      {discrete, pair01, pair02, pair12, indiscrete} := by decide
  have hd := hm discrete
  have h01 := hm pair01
  have h02 := hm pair02
  have h12 := hm pair12
  have ht := hm indiscrete
  simp [hu, refines, Finset.filter_insert, Finset.filter_singleton] at hd h01 h02 h12 ht
  funext x
  cases x <;> simp only [mu] <;> omega

open Polynomial

noncomputable def characteristic {α : Type} [Fintype α] [PartialOrder α] [OrderTop α]
    (r : α → ℕ) (m : α → ℤ) : Polynomial ℝ :=
  ∑ x, C (m x : ℝ) * X ^ (r ⊤ - r x)

theorem characteristic_eq : characteristic rank mu = (X - 1) * (X - 2) := by
  have hu : (Finset.univ : Finset ThreePartitions) =
      {discrete, pair01, pair02, pair12, indiscrete} := by decide
  simp [characteristic, hu, rank, mu]
  ring

def IsRankFunction {α : Type} [PartialOrder α] [OrderBot α] (r : α → ℕ) : Prop :=
  r ⊥ = 0 ∧ ∀ a b, a ⋖ b → r b = r a + 1

theorem rank_function : IsRankFunction rank :=
  ⟨rfl, fun a b h => rank_cover a b h.lt (fun _ h1 h2 => h.2 h1 h2)⟩

/-- Consecutive distinct nonzero real roots must have opposite signs.
This necessary condition of alternating root signs ignores any zero roots. -/
def AlternatingRootSigns (p : Polynomial ℝ) : Prop :=
  ∀ a b : ℝ, a < b → a ≠ 0 → b ≠ 0 → p.eval a = 0 → p.eval b = 0 →
    (∀ c : ℝ, a < c → c < b → p.eval c ≠ 0) → a * b < 0

theorem roots_iff (t : ℝ) : (characteristic rank mu).eval t = 0 ↔ t = 1 ∨ t = 2 := by
  rw [characteristic_eq]
  simp [mul_eq_zero, sub_eq_zero]

theorem not_alternating : ¬AlternatingRootSigns (characteristic rank mu) := by
  intro h
  have hgap : ∀ c : ℝ, 1 < c → c < 2 → (characteristic rank mu).eval c ≠ 0 := by
    intro c h1 h2 hc
    rcases (roots_iff c).mp hc with rfl | rfl <;> exact (lt_irrefl _ (by assumption))
  have hbad := h 1 2 (by norm_num) (by norm_num) (by norm_num)
    ((roots_iff 1).mpr (Or.inl rfl)) ((roots_iff 2).mpr (Or.inr rfl)) hgap
  norm_num at hbad

/-- The root-sign clause under the standard characteristic-polynomial interpretation. -/
def RootSignClause : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] [Lattice α] [BoundedOrder α]
    [DecidableRel (α := α) (· ≤ ·)] [IsAtomistic α] [IsUpperModularLattice α]
    (r : α → ℕ) (m : α → ℤ), IsRankFunction r → IsMobiusRow m →
      AlternatingRootSigns (characteristic r m)

theorem disprove_root_sign_clause : ¬RootSignClause := by
  intro h
  exact not_alternating (h ThreePartitions rank mu rank_function mu_recurrence)

abbrev triangle : SimpleGraph (Fin 3) := ⊤

def triangleColoringEquiv (q : ℕ) : triangle.Coloring (Fin q) ≃ (Fin 3 ↪ Fin q) where
  toFun c := ⟨c, fun _ _ h => by
    by_contra hn
    exact c.valid hn h⟩
  invFun f := SimpleGraph.Coloring.mk f (fun h => f.injective.ne h)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

theorem triangle_coloring_count (q : ℕ) :
    Fintype.card (triangle.Coloring (Fin q)) = q * (q - 1) * (q - 2) := by
  rw [Fintype.card_congr (triangleColoringEquiv q), Fintype.card_embedding_eq]
  simp [Nat.descFactorial_succ, mul_comm, mul_left_comm, mul_assoc]

noncomputable def triangleChromatic : Polynomial ℝ := X * characteristic rank mu

theorem triangle_chromatic_counts (q : ℕ) :
    triangleChromatic.eval (q : ℝ) = (Fintype.card (triangle.Coloring (Fin q)) : ℝ) := by
  rw [triangle_coloring_count]
  by_cases hq : 2 ≤ q
  · have hq1 : 1 ≤ q := by omega
    simp [triangleChromatic, characteristic_eq, Nat.cast_sub hq, Nat.cast_sub hq1,
      mul_assoc]
  · interval_cases q <;> norm_num [triangleChromatic, characteristic_eq]

theorem triangle_roots_iff (t : ℝ) : triangleChromatic.eval t = 0 ↔
    t = 0 ∨ t = 1 ∨ t = 2 := by
  simp [triangleChromatic, characteristic_eq, mul_eq_zero, sub_eq_zero]

theorem triangle_not_alternating : ¬AlternatingRootSigns triangleChromatic := by
  intro h
  have hgap : ∀ c : ℝ, 1 < c → c < 2 → triangleChromatic.eval c ≠ 0 := by
    intro c h1 h2 hc
    rcases (triangle_roots_iff c).mp hc with rfl | rfl | rfl <;> norm_num at *
  have hbad := h 1 2 (by norm_num) (by norm_num) (by norm_num)
    ((triangle_roots_iff 1).mpr (Or.inr (Or.inl rfl)))
    ((triangle_roots_iff 2).mpr (Or.inr (Or.inr rfl))) hgap
  norm_num at hbad

def GraphRootSignClause : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (p : Polynomial ℝ),
    (∀ q : ℕ, p.eval (q : ℝ) = (Fintype.card (G.Coloring (Fin q)) : ℝ)) →
      AlternatingRootSigns p

theorem disprove_graph_root_sign_clause : ¬GraphRootSignClause := by
  intro h
  exact triangle_not_alternating (h (Fin 3) triangle triangleChromatic triangle_chromatic_counts)

#print axioms all_partitions
#print axioms partitionOrderIso
#print axioms characteristic_eq
#print axioms mu_unique
#print axioms disprove_root_sign_clause
#print axioms triangle_chromatic_counts
#print axioms disprove_graph_root_sign_clause

end Conjecture8551
