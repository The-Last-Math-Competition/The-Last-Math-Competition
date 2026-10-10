import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

noncomputable section
namespace SingleEdgeDesign

-- Complete2-uniform hypergraph on v labelled vertices: all2-element subsets.
abbrev Edge (v : ℕ) := {e : Finset (Fin v) // e.card = 2}
abbrev Block (v : ℕ) := Finset (Edge v)
abbrev Family (v : ℕ) := Finset (Block v)

-- Blocks in the specified isomorphism class have exactly one edge.
-- The usual unordered decomposition is an edge partition, including coverage.
def IsDecomposition (v : ℕ) (D : Family v) : Prop :=
  (∀ B ∈ D, B.card = 1) ∧
  (∀ e : Edge v, ∃ B ∈ D, e ∈ B) ∧
  (∀ B ∈ D, ∀ C ∈ D, B ≠ C → Disjoint B C)

def canonical (v : ℕ) : Family v := Finset.univ.image (fun e : Edge v => {e})

theorem canonical_valid (v : ℕ) : IsDecomposition v (canonical v) := by
  classical
  constructor
  · intro B hB
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hB
    simp
  constructor
  · intro e
    exact ⟨{e}, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, by simp⟩
  · intro B hB C hC hne
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hC
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
    intro h
    subst f
    exact hne rfl

theorem unique_decomposition (v : ℕ) (D : Family v) (hD : IsDecomposition v D) :
    D = canonical v := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨e,rfl⟩ := Finset.card_eq_one.mp (hD.1 B hB)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  · intro hB
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C,hC,heC⟩ := hD.2.1 e
    obtain ⟨f,rfl⟩ := Finset.card_eq_one.mp (hD.1 C hC)
    have h : e = f := Finset.mem_singleton.mp heC
    subst f
    exact hC

abbrev Decomposition (v : ℕ) := {D : Family v // IsDecomposition v D}

instance (v : ℕ) : Unique (Decomposition v) where
  default := ⟨canonical v, canonical_valid v⟩
  uniq D := Subtype.ext (unique_decomposition v D.val D.property)

noncomputable instance (v : ℕ) : Fintype (Decomposition v) := Fintype.ofFinite _

theorem exact_count (v : ℕ) : Fintype.card (Decomposition v) = 1 := Fintype.card_unique

theorem prime_count (v : ℕ) (_hv : Nat.Prime v) :
    Fintype.card (Decomposition v) = 1 := exact_count v

theorem arbitrarily_large_prime_counterexamples (N : ℕ) :
    ∃ p, N ≤ p ∧ Nat.Prime p ∧ Fintype.card (Decomposition p) = 1 := by
  obtain ⟨p,hp,hle⟩ := Nat.exists_infinite_primes N
  exact ⟨p,hp,hle,exact_count p⟩

#print axioms canonical_valid
#print axioms unique_decomposition
#print axioms exact_count
#print axioms arbitrarily_large_prime_counterexamples
end SingleEdgeDesign
