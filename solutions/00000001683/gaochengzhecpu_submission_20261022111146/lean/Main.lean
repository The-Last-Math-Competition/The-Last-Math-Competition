import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Conjecture1683

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A simple 3-uniform hypergraph, represented by a symmetric irreflexive
Boolean relation on triples. This is equivalent to a set of 3-element subsets. -/
structure Hypergraph3 (V : Type*) [DecidableEq V] where
  edge : V → V → V → Bool
  swap12 : ∀ a b c, edge a b c = edge b a c
  swap23 : ∀ a b c, edge a b c = edge a c b
  noRepeat : ∀ a b, edge a a b = false

def Edge {V : Type*} [DecidableEq V] (H : Hypergraph3 V) (a b c : V) : Prop :=
  H.edge a b c = true

instance {V : Type*} [DecidableEq V] (H : Hypergraph3 V) (a b c : V) :
    Decidable (Edge H a b c) := inferInstanceAs (Decidable (H.edge a b c = true))

/-- A vertex bijection preserving exactly the unordered triples. -/
def IsIso {V : Type*} [DecidableEq V] (H K : Hypergraph3 V) (e : V ≃ V) : Prop :=
  ∀ a b c, Edge H a b c ↔ Edge K (e a) (e b) (e c)

/-- Equal vertex decks, including multiplicity: the outer bijection matches the cards;
the inner bijection restricts to an isomorphism on the complements. -/
def Hypomorphic {V : Type*} [DecidableEq V] (H K : Hypergraph3 V) : Prop :=
  ∃ matchCards : V ≃ V, ∀ v, ∃ e : V ≃ V, e v = matchCards v ∧
    ∀ a b c, a ≠ v → b ≠ v → c ≠ v →
      (Edge H a b c ↔ Edge K (e a) (e b) (e c))

def ReconstructionClaim : Prop :=
  ∀ n : ℕ, 8 ≤ n → ∀ H K : Hypergraph3 (Fin n),
    Hypomorphic H K → ∃ e, IsIso H K e

def codegree {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (a b : V) : ℕ :=
  Fintype.card {c : V // Edge H a b c}

/-- Twice the usual vertex degree, because the other two vertices are ordered. -/
def doubleDegree {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (a : V) : ℕ :=
  Fintype.card {p : V × V // Edge H a p.1 p.2}

theorem codegree_preserved {V : Type*} [Fintype V] [DecidableEq V]
    {H K : Hypergraph3 V} {e : V ≃ V} (h : IsIso H K e) (a b : V) :
    codegree H a b = codegree K (e a) (e b) :=
  Fintype.card_congr (Equiv.subtypeEquiv e (fun c => h a b c))

theorem doubleDegree_preserved {V : Type*} [Fintype V] [DecidableEq V]
    {H K : Hypergraph3 V} {e : V ≃ V} (h : IsIso H K e) (a : V) :
    doubleDegree H a = doubleDegree K (e a) :=
  Fintype.card_congr (Equiv.subtypeEquiv (e.prodCongr e) (fun p => h a p.1 p.2))

def X : Hypergraph3 (Fin 9) where
  edge := fun a b c => Nat.testBit 724973468784811889797230906767087399767752871133660820790564329874415300919925825338186519849929637330447910343745238991275281366820734139417097157663448037512568652691528161217354619215185762068095675346909449979904 (a.val * 81 + b.val * 9 + c.val)
  swap12 := by decide
  swap23 := by decide
  noRepeat := by decide

theorem deg_X (a : Fin 9) : doubleDegree X a = ![16,18,18,20,20,20,20,18,18] a := by
  fin_cases a <;> decide

theorem codeg_X (a b : Fin 9) : codegree X a b = ![![0,2,2,2,2,2,2,2,2],![2,0,3,3,2,1,3,2,2],![2,3,0,2,3,3,1,2,2],![2,3,2,0,3,4,2,1,3],![2,2,3,3,0,2,4,3,1],![2,1,3,4,2,0,3,3,2],![2,3,1,2,4,3,0,2,3],![2,2,2,1,3,3,2,0,3],![2,2,2,3,1,2,3,3,0]] a b := by
  fin_cases a <;> fin_cases b <;> decide

def Y : Hypergraph3 (Fin 9) where
  edge := fun a b c => Nat.testBit 714200751553095787913999835863218955778146069227499466586749188636012136007175204310744568676953188850887857959549551566390617998718466951361299478272318208908094538113209720626545668451991677318472728517795981172736 (a.val * 81 + b.val * 9 + c.val)
  swap12 := by decide
  swap23 := by decide
  noRepeat := by decide

theorem deg_Y (a : Fin 9) : doubleDegree Y a = ![16,18,18,20,20,20,20,18,18] a := by
  fin_cases a <;> decide

theorem codeg_Y (a b : Fin 9) : codegree Y a b = ![![0,2,2,2,2,2,2,2,2],![2,0,2,3,3,1,2,2,3],![2,2,0,3,3,2,1,3,2],![2,3,3,0,2,4,3,1,2],![2,3,3,2,0,3,4,2,1],![2,1,2,4,3,0,2,3,3],![2,2,1,3,4,2,0,3,3],![2,2,3,1,2,3,3,0,2],![2,3,2,2,1,3,3,2,0]] a b := by
  fin_cases a <;> fin_cases b <;> decide

def cardPerm0 : Fin 9 ≃ Fin 9 where
  toFun := ![0,1,2,3,4,5,6,7,8]
  invFun := ![0,1,2,3,4,5,6,7,8]
  left_inv := by decide
  right_inv := by decide

def cardPerm1 : Fin 9 ≃ Fin 9 where
  toFun := ![0,1,8,7,6,5,4,3,2]
  invFun := ![0,1,8,7,6,5,4,3,2]
  left_inv := by decide
  right_inv := by decide

def cardPerm2 : Fin 9 ≃ Fin 9 where
  toFun := ![0,7,2,5,8,3,6,1,4]
  invFun := ![0,7,2,5,8,3,6,1,4]
  left_inv := by decide
  right_inv := by decide

def cardPerm3 : Fin 9 ≃ Fin 9 where
  toFun := ![0,5,8,3,6,1,4,7,2]
  invFun := ![0,5,8,3,6,1,4,7,2]
  left_inv := by decide
  right_inv := by decide

def cardPerm4 : Fin 9 ≃ Fin 9 where
  toFun := ![0,7,6,5,4,3,2,1,8]
  invFun := ![0,7,6,5,4,3,2,1,8]
  left_inv := by decide
  right_inv := by decide

theorem same_deck : Hypomorphic X Y := by
  refine ⟨Equiv.refl _, ?_⟩
  intro v
  fin_cases v
  · exact ⟨cardPerm0, by decide, by decide⟩
  · exact ⟨cardPerm1, by decide, by decide⟩
  · exact ⟨cardPerm2, by decide, by decide⟩
  · exact ⟨cardPerm3, by decide, by decide⟩
  · exact ⟨cardPerm4, by decide, by decide⟩
  · exact ⟨cardPerm1, by decide, by decide⟩
  · exact ⟨cardPerm2, by decide, by decide⟩
  · exact ⟨cardPerm3, by decide, by decide⟩
  · exact ⟨cardPerm4, by decide, by decide⟩


private theorem fin9_cases (x : Fin 9) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 := by
  fin_cases x <;> simp

theorem not_isomorphic : ¬ ∃ e, IsIso X Y e := by
  rintro ⟨e, h⟩
  rcases fin9_cases (e 0) with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
  · rcases fin9_cases (e 1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · have ht := doubleDegree_preserved h 1
      rw [deg_X, deg_Y, h1] at ht
      exact (by decide : ¬ ((18 : ℕ) = 16)) ht
    · rcases fin9_cases (e 2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 16)) ht
      · have ht := e.injective (h2.trans h1.symm)
        exact (by decide : (2 : Fin 9) ≠ 1) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · rcases fin9_cases (e 3) with h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 16)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have bad : ¬ (Edge X 3 1 2 ↔ Edge Y 3 1 8) := by decide
          apply bad
          simpa only [h3, h1, h2] using h 3 1 2
        · have ht := codegree_preserved h 3 2
          rw [codeg_X, codeg_Y, h3, h2] at ht
          exact (by decide : ¬ ((2 : ℕ) = 1)) ht
        · have ht := codegree_preserved h 3 1
          rw [codeg_X, codeg_Y, h3, h1] at ht
          exact (by decide : ¬ ((3 : ℕ) = 1)) ht
        · have ht := codegree_preserved h 3 1
          rw [codeg_X, codeg_Y, h3, h1] at ht
          exact (by decide : ¬ ((3 : ℕ) = 2)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
    · rcases fin9_cases (e 2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 16)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · have ht := e.injective (h2.trans h1.symm)
        exact (by decide : (2 : Fin 9) ≠ 1) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · rcases fin9_cases (e 4) with h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 16)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 3)) ht
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 3)) ht
        · have bad : ¬ (Edge X 4 1 2 ↔ Edge Y 5 2 7) := by decide
          apply bad
          simpa only [h4, h1, h2] using h 4 1 2
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 1)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
    · have ht := doubleDegree_preserved h 1
      rw [deg_X, deg_Y, h1] at ht
      exact (by decide : ¬ ((18 : ℕ) = 20)) ht
    · have ht := doubleDegree_preserved h 1
      rw [deg_X, deg_Y, h1] at ht
      exact (by decide : ¬ ((18 : ℕ) = 20)) ht
    · have ht := doubleDegree_preserved h 1
      rw [deg_X, deg_Y, h1] at ht
      exact (by decide : ¬ ((18 : ℕ) = 20)) ht
    · have ht := doubleDegree_preserved h 1
      rw [deg_X, deg_Y, h1] at ht
      exact (by decide : ¬ ((18 : ℕ) = 20)) ht
    · rcases fin9_cases (e 2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 16)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · rcases fin9_cases (e 4) with h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 16)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 1)) ht
        · have bad : ¬ (Edge X 4 1 2 ↔ Edge Y 4 7 2) := by decide
          apply bad
          simpa only [h4, h1, h2] using h 4 1 2
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 3)) ht
        · have ht := codegree_preserved h 4 1
          rw [codeg_X, codeg_Y, h4, h1] at ht
          exact (by decide : ¬ ((2 : ℕ) = 3)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 4
          rw [deg_X, deg_Y, h4] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := e.injective (h2.trans h1.symm)
        exact (by decide : (2 : Fin 9) ≠ 1) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
    · rcases fin9_cases (e 2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 16)) ht
      · rcases fin9_cases (e 3) with h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 16)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := codegree_preserved h 3 1
          rw [codeg_X, codeg_Y, h3, h1] at ht
          exact (by decide : ¬ ((3 : ℕ) = 2)) ht
        · have ht := codegree_preserved h 3 1
          rw [codeg_X, codeg_Y, h3, h1] at ht
          exact (by decide : ¬ ((3 : ℕ) = 1)) ht
        · have ht := codegree_preserved h 3 2
          rw [codeg_X, codeg_Y, h3, h2] at ht
          exact (by decide : ¬ ((2 : ℕ) = 1)) ht
        · have bad : ¬ (Edge X 3 1 2 ↔ Edge Y 6 8 1) := by decide
          apply bad
          simpa only [h3, h1, h2] using h 3 1 2
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
        · have ht := doubleDegree_preserved h 3
          rw [deg_X, deg_Y, h3] at ht
          exact (by decide : ¬ ((20 : ℕ) = 18)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := doubleDegree_preserved h 2
        rw [deg_X, deg_Y, h2] at ht
        exact (by decide : ¬ ((18 : ℕ) = 20)) ht
      · have ht := codegree_preserved h 2 1
        rw [codeg_X, codeg_Y, h2, h1] at ht
        exact (by decide : ¬ ((3 : ℕ) = 2)) ht
      · have ht := e.injective (h2.trans h1.symm)
        exact (by decide : (2 : Fin 9) ≠ 1) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 18)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 18)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 20)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 20)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 20)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 20)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 18)) ht
  · have ht := doubleDegree_preserved h 0
    rw [deg_X, deg_Y, h0] at ht
    exact (by decide : ¬ ((16 : ℕ) = 18)) ht

theorem conjecture1683_false : ¬ ReconstructionClaim := by
  intro h
  exact not_isomorphic (h 9 (by decide) X Y same_deck)

/-- The actual unordered edge sets, included to expose the bit encoding. -/
def edgesX : Finset (Finset (Fin 9)) :=
  {{0,1,2}, {0,1,6}, {0,2,5}, {0,3,4}, {0,3,8}, {0,4,7}, {0,5,6}, {0,7,8},
   {1,2,3}, {1,2,8}, {1,3,5}, {1,3,6}, {1,4,6}, {1,4,7}, {1,7,8},
   {2,3,4}, {2,4,6}, {2,4,7}, {2,5,7}, {2,5,8}, {3,4,5}, {3,5,7},
   {3,5,8}, {3,6,8}, {4,5,6}, {4,6,8}, {5,6,7}, {6,7,8}}

def edgesY : Finset (Finset (Fin 9)) :=
  {{0,1,4}, {0,1,8}, {0,2,3}, {0,2,7}, {0,3,6}, {0,4,5}, {0,5,8}, {0,6,7},
   {1,2,3}, {1,2,8}, {1,3,5}, {1,3,6}, {1,4,6}, {1,4,7}, {1,7,8},
   {2,3,4}, {2,4,6}, {2,4,7}, {2,5,7}, {2,5,8}, {3,4,5}, {3,5,7},
   {3,5,8}, {3,6,8}, {4,5,6}, {4,6,8}, {5,6,7}, {6,7,8}}

theorem edgesX_uniform : ∀ s ∈ edgesX, s.card = 3 := by decide
theorem edgesY_uniform : ∀ s ∈ edgesY, s.card = 3 := by decide
theorem edgesX_card : edgesX.card = 28 := by decide
theorem edgesY_card : edgesY.card = 28 := by decide

/-- All 729 ordered triples agree with the displayed unordered edge set. -/
theorem edgeX_iff_mem (a b c : Fin 9) :
    Edge X a b c ↔ ({a,b,c} : Finset (Fin 9)) ∈ edgesX := by
  revert a b c
  decide

theorem edgeY_iff_mem (a b c : Fin 9) :
    Edge Y a b c ↔ ({a,b,c} : Finset (Fin 9)) ∈ edgesY := by
  revert a b c
  decide

/-- Every pair of distinct vertices lies in exactly one triple. -/
def IsSteinerTripleSystem {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) : Prop :=
  ∀ a b, a ≠ b → codegree H a b = 1

theorem X_not_steiner : ¬ IsSteinerTripleSystem X := by
  intro h
  have ht := h 0 1 (by decide)
  rw [codeg_X] at ht
  exact (by decide : ¬ ((2 : ℕ) = 1)) ht

theorem Y_not_steiner : ¬ IsSteinerTripleSystem Y := by
  intro h
  have ht := h 0 1 (by decide)
  rw [codeg_Y] at ht
  exact (by decide : ¬ ((2 : ℕ) = 1)) ht

def CounterexamplesAreSteiner : Prop :=
  ∀ n : ℕ, 8 ≤ n → ∀ H K : Hypergraph3 (Fin n),
    Hypomorphic H K → (¬ ∃ e, IsIso H K e) →
      IsSteinerTripleSystem H ∧ IsSteinerTripleSystem K

theorem steiner_clause_false : ¬ CounterexamplesAreSteiner := by
  intro h
  exact X_not_steiner (h 9 (by decide) X Y same_deck not_isomorphic).1

#print axioms same_deck
#print axioms not_isomorphic
#print axioms conjecture1683_false
#print axioms edgeX_iff_mem
#print axioms edgeY_iff_mem
#print axioms X_not_steiner
#print axioms Y_not_steiner
#print axioms steiner_clause_false

end Conjecture1683
