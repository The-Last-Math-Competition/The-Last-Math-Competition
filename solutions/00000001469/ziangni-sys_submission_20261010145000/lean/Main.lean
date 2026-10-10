import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace BinaryUniqueGame

/-- Genuine binary Unique Games: an edge relation and label-permutation constraints,
with the opposite orientation carrying the inverse permutation. -/
structure Game (V : Type*) where
  graph : SimpleGraph V
  constraint : V → V → Equiv.Perm Bool
  inverse : ∀ u v, graph.Adj u v → constraint v u = (constraint u v).symm

abbrev Labeling (V : Type*) := V → Bool

def flip {V : Type*} (a : Labeling V) : Labeling V := fun v => !(a v)

/-- Every permutation of two labels commutes with their interchange. -/
theorem permutation_complement : ∀ p : Equiv.Perm Bool, ∀ b : Bool, p (!b) = !(p b) := by
  decide

def satisfied {V : Type*} (g : Game V) (a : Labeling V) (u v : V) : Prop :=
  g.constraint u v (a u) = a v

theorem edge_invariant {V : Type*} (g : Game V) (a : Labeling V) (u v : V) :
    satisfied g (flip a) u v ↔ satisfied g a u v := by
  unfold satisfied flip
  rw [permutation_complement]
  exact Bool.not_inj_iff

/-- Counting oriented satisfied edges doubles the usual undirected objective,
without changing optimality or near-optimal thresholds. -/
noncomputable def score {V : Type*} [Fintype V] (g : Game V) (a : Labeling V) : ℕ := by
  classical
  exact ∑ u : V, ∑ v : V, if g.graph.Adj u v ∧ satisfied g a u v then 1 else 0

theorem score_invariant {V : Type*} [Fintype V] (g : Game V) (a : Labeling V) :
    score g (flip a) = score g a := by
  classical
  unfold score
  simp only [edge_invariant]

theorem flip_distinct {V : Type*} [Nonempty V] (a : Labeling V) : flip a ≠ a := by
  intro h
  let v : V := Classical.choice inferInstance
  have hv := congrFun h v
  change Bool.not (a v) = a v at hv
  cases hval : a v <;> simp [hval] at hv

def optimal {V : Type*} [Fintype V] (g : Game V) (a : Labeling V) : Prop :=
  ∀ b, score g b ≤ score g a

theorem optimal_flip {V : Type*} [Fintype V] (g : Game V) (a : Labeling V)
    (ha : optimal g a) : optimal g (flip a) := by
  unfold optimal at ha ⊢
  rw [score_invariant]
  exact ha

theorem no_unique_optimal {V : Type*} [Fintype V] [Nonempty V] (g : Game V) :
    ¬ ∃! a : Labeling V, optimal g a := by
  rintro ⟨a,ha,hunique⟩
  exact flip_distinct a (hunique (flip a) (optimal_flip g a ha))

/-- Every score-based near-optimality threshold has no unique qualifying labeling. -/
theorem no_unique_near_optimal {V : Type*} [Fintype V] [Nonempty V]
    (g : Game V) (q : ℕ) : ¬ ∃! a : Labeling V, q ≤ score g a := by
  rintro ⟨a,ha,hunique⟩
  apply flip_distinct a
  apply hunique
  rwa [score_invariant]

/-- The complete two-vertex graph, with a genuine identity-permutation instance. -/
def exampleGame : Game (Fin 2) where
  graph := ⊤
  constraint _ _ := Equiv.refl Bool
  inverse _ _ _ := rfl

theorem example_has_edge : exampleGame.graph.Adj 0 1 := by
  simp [exampleGame]

/-- No choice of constraints on two vertices can remove the complement obstruction. -/
theorem every_two_vertex_game_fails (g : Game (Fin 2)) (q : ℕ) :
    ¬ ∃! a : Labeling (Fin 2), q ≤ score g a := no_unique_near_optimal g q

theorem small_size : Fintype.card (Fin 2) ≤ 2^40 := by norm_num

#print axioms permutation_complement
#print axioms score_invariant
#print axioms flip_distinct
#print axioms no_unique_optimal
#print axioms no_unique_near_optimal
#print axioms every_two_vertex_game_fails
#print axioms small_size
end BinaryUniqueGame
