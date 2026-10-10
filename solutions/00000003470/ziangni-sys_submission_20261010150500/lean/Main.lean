import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace CliqueTreeCount
abbrev Vertex := Fin 2
def G : SimpleGraph Vertex := ⊤

/-- A faithful induced-cycle embedding: adjacency is exactly cyclic consecutiveness. -/
def inducedCycle (n : ℕ) (f : Fin n → Vertex) : Prop :=
  Function.Injective f ∧ ∀ i j : Fin n, i ≠ j →
    (G.Adj (f i) (f j) ↔ ((i.val+1)%n=j.val ∨ (j.val+1)%n=i.val))

def chordal : Prop := ∀ n : ℕ, 4 ≤ n → ¬ ∃ f : Fin n → Vertex, inducedCycle n f

theorem actual_chordal : chordal := by
  intro n hn ⟨f,hf,hc⟩
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

/-- The standard successor-neighbor clique condition for an elimination ordering. -/
def PEO (p : Equiv.Perm Vertex) : Prop :=
  ∀ i j k : Vertex, i < j → i < k → j ≠ k →
    G.Adj (p i) (p j) → G.Adj (p i) (p k) → G.Adj (p j) (p k)

theorem every_ordering (p : Equiv.Perm Vertex) : PEO p := by
  intro i j k hij hik hjk h1 h2
  simp only [G, SimpleGraph.top_adj]
  exact p.injective.ne hjk

/-- Exact count of all valid permutations of the two actual vertices. -/
noncomputable def peoCount : ℕ := by
  classical
  exact (Finset.univ.filter PEO).card

theorem peo_count_two : peoCount = 2 := by
  classical
  unfold peoCount
  have h : Finset.univ.filter PEO = (Finset.univ : Finset (Equiv.Perm Vertex)) := by
    ext p
    simp [every_ordering]
  rw [h, Finset.card_univ, Fintype.card_perm]
  norm_num

def maximalClique (s : Finset Vertex) : Prop :=
  G.IsClique (s : Set Vertex) ∧
    ∀ t : Finset Vertex, G.IsClique (t : Set Vertex) → s ⊆ t → t = s

noncomputable instance : DecidablePred maximalClique := Classical.decPred _

theorem unique_maximal_clique : ∀ s : Finset Vertex, maximalClique s ↔ s = Finset.univ := by
  intro s
  have hc : G.IsClique (Finset.univ : Finset Vertex) := by
    intro a ha b hb hab
    simpa [G] using hab
  constructor
  · intro h
    exact (h.2 Finset.univ hc (Finset.subset_univ s)).symm
  · intro h
    subst s
    refine ⟨hc, ?_⟩
    intro t ht hs
    exact Finset.Subset.antisymm (Finset.subset_univ t) hs

abbrev CliqueVertex := {s : Finset Vertex // maximalClique s}

noncomputable instance : Fintype CliqueVertex := inferInstance
instance : Nonempty CliqueVertex := ⟨⟨Finset.univ, (unique_maximal_clique _).2 rfl⟩⟩
instance : Subsingleton CliqueVertex := ⟨by
  intro a b
  apply Subtype.ext
  exact ((unique_maximal_clique a.val).1 a.property).trans
    ((unique_maximal_clique b.val).1 b.property).symm⟩

/-- With a single actual maximal clique, its tree is the one-vertex graph. -/
def cliqueTree : SimpleGraph CliqueVertex := ⊥

theorem any_clique_graph_equals_tree (t : SimpleGraph CliqueVertex) : t = cliqueTree := by
  ext u v
  have h : u = v := Subsingleton.elim _ _
  subst v
  simp [cliqueTree]

theorem clique_vertex_count : Fintype.card CliqueVertex = 1 := Fintype.card_eq_one_iff.mpr ⟨Classical.choice inferInstance, fun _ => Subsingleton.elim _ _⟩

/-- A local rotation is a permutation of actual incident neighbors. On the one-vertex
clique tree there are no neighbors, so the unique empty permutation is the cyclic order. -/
abbrev RotationSystem := (v : CliqueVertex) → Equiv.Perm {w : CliqueVertex // cliqueTree.Adj v w}

noncomputable instance : Fintype RotationSystem := by
  classical
  unfold RotationSystem
  infer_instance

theorem rotation_count_one : Fintype.card RotationSystem = 1 := by
  classical
  rw [Fintype.card_pi]
  have he : ∀ v : CliqueVertex, Fintype.card {w : CliqueVertex // cliqueTree.Adj v w} = 0 := by
    intro v
    simp [cliqueTree]
  simp [Fintype.card_perm, he]

instance : Subsingleton (SimpleGraph CliqueVertex) := ⟨fun a b =>
  (any_clique_graph_equals_tree a).trans (any_clique_graph_equals_tree b).symm⟩

noncomputable instance : Fintype (SimpleGraph CliqueVertex) :=
  Fintype.ofSubsingleton cliqueTree

/-- Product over the sole maximal-clique tree's actual embedding count. -/
noncomputable def embeddingProduct : ℕ :=
  ∏ _ : SimpleGraph CliqueVertex, Fintype.card RotationSystem

theorem embedding_product_one : embeddingProduct = 1 := by
  simp [embeddingProduct, rotation_count_one]

theorem count_mismatch : peoCount ≠ embeddingProduct := by
  rw [peo_count_two, embedding_product_one]
  norm_num

#print axioms actual_chordal
#print axioms peo_count_two
#print axioms unique_maximal_clique
#print axioms any_clique_graph_equals_tree
#print axioms rotation_count_one
#print axioms count_mismatch
end CliqueTreeCount
