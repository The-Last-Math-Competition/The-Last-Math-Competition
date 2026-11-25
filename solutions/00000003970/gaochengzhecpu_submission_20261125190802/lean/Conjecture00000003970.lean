/-
  ==============================================================================
  Conjecture 00000003970 — Complete Formal Resolution Across All Interpretations
  The Last Math Competition — Core Lean 4.19.0 (Zero External Dependencies)
  ==============================================================================

  Statement (`SOURCE.md`):
    "Definition: The subgraph count vector is the sequence of the numbers of
     subgraphs of each order. Conjecture: There exist two graphs whose counts of
     all connected subgraphs coincide while their adjacency spectra differ; the
     minimal vertex number for such a separation is 6 or 7, and all cases can be
     completely enumerated. (minimal subgraph-count spectrum separation)"

  Summary of Machine-Verified Resolution (Grand Trichotomy):
    Across ALL THREE standard mathematical interpretations of "counts of all
    connected subgraphs coincide", the conjectured minimal vertex number "6 or 7"
    is REFUTED (`n_min ∉ {6, 7}`):

    1. **Reading I — Connected Induced Subgraph Count Vector `c^ind(G)`**:
       - Existence: **TRUE**.
       - Exact minimal vertex number: **`n_min = 5`** (strictly below `6` or `7`),
         both among all simple graphs AND among connected simple graphs!
       - Complete enumeration at `n = 5`: **4 unordered pairs** (1 disconnected
         pair `K₃ ⊔ 2K₁` vs `P₃ ⊔ K₂` and 3 connected pairs), proved exhaustive
         up to isomorphism (`complete_enum_connInduced_5`).

    2. **Reading II — Connected Non-Induced (Edge-Subset) Subgraph Count Vector `c^sub(G)`**:
       - Existence: **TRUE**.
       - Exact minimal vertex number: **`n_min = 8`** (strictly above `6` or `7`),
         both among all simple graphs AND among connected simple graphs!
       - Zero separating pairs exist for ANY `1 ≤ n ≤ 7` (`no_connEdgeSubgraph_sep_le_7`),
         and explicit minimal pairs (disconnected forests at `m = 5` and connected
         graphs at `m = 12`) exist at `n = 8` (`exists_connEdgeSubgraph_sep_8`).

    3. **Reading III — Isomorphism-Class Counts of All Connected Subgraphs (`N_ind` / `N_sub`)**:
       - Existence: **FALSE (IMPOSSIBLE at every vertex order `n ∈ ℕ`)**!
       - By the Whitney–Lovász connected subgraph algebra, equality of connected
         subgraph counts (either induced `indIsoCount` or non-induced `subIsoCount`)
         reconstructs `G` up to isomorphism (`GraphIso G₁ G₂`) and forces identical
         characteristic polynomials `charPoly G₁ = charPoly G₂`!

    4. **Diagnostic Origin of `{6, 7}`**:
       - Requiring `c^ind` equality PLUS identical degree sequence raises `n_min`
         from `5` to **`6`** (`exists_connInduced_sameDeg_sep_6`);
       - Dropping "connected" and using the unrestricted subgraph count vector
         `s^sub(G)` (`allEdgeSubgraphVec`) yields **`n_min = 7`**
         (`no_allEdgeSubgraph_sep_le_6` & `sep_allEdge_pair_G7`).
-/

import Conjecture00000003970.CountList
import Conjecture00000003970.Graph
import Conjecture00000003970.CharPoly
import Conjecture00000003970.SubgraphCounts
import Conjecture00000003970.IsoCountReconstruction
import Conjecture00000003970.FastSubgraphEval
import Conjecture00000003970.CanonCertsData
import Conjecture00000003970.CanonGraphs
import Conjecture00000003970.FastPackedEval
import Conjecture00000003970.InducedOrderSeparation
import Conjecture00000003970.EdgeSubgraphOrderSeparation

namespace Conjecture00000003970

/-- Predicate: vertex order `n` admits a `c^ind` vs. adjacency-spectrum separation. -/
def HasInducedOrderSeparation (n : Nat) : Prop :=
  ∃ G₁ G₂ : SimpleGraphN n,
    connInducedVec G₁ = connInducedVec G₂ ∧ charPoly G₁ ≠ charPoly G₂

/-- Predicate: vertex order `n` admits a `c^sub` vs. adjacency-spectrum separation. -/
def HasEdgeSubgraphOrderSeparation (n : Nat) : Prop :=
  ∃ G₁ G₂ : SimpleGraphN n,
    connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂ ∧ charPoly G₁ ≠ charPoly G₂

/-- **Master Theorem I (Reading I — `n_min(c^ind) = 5 ∉ {6, 7}` + Complete Classification):**
    `5` is the exact minimal vertex number for connected induced subgraph count vector
    vs. adjacency-spectrum separation, refuting "minimal vertex number is 6 or 7",
    and all `n = 5` separating pairs are classified into the exact 4 canonical pairs. -/
theorem resolution_reading_I_induced_order_vector :
    (∀ n ≤ 4, ¬ HasInducedOrderSeparation n) ∧
    HasInducedOrderSeparation 5 ∧
    (∃ G₁ G₂ : SimpleGraphN 5,
      IsConnectedGraph G₁ ∧ IsConnectedGraph G₂ ∧
      connInducedVec G₁ = connInducedVec G₂ ∧ charPoly G₁ ≠ charPoly G₂) ∧
    (∀ G₁ G₂ : SimpleGraphN 5,
      (connInducedVec G₁ = connInducedVec G₂ ∧ charPoly G₁ ≠ charPoly G₂) ↔
        IsMinimalInducedSepPair5 G₁ G₂) := by
  refine ⟨?_, ?_, exists_connInduced_sep_5, complete_enum_connInduced_5⟩
  · intro n hn ⟨G₁, G₂, hv, hne⟩
    exact hne (no_connInduced_sep_le_4 hn G₁ G₂ hv).2
  · rcases exists_connInduced_sep_5 with ⟨G₁, G₂, _, _, hv, hne⟩
    exact ⟨G₁, G₂, hv, hne⟩

/-- **Master Theorem II (Reading II — `n_min(c^sub) = 8 ∉ {6, 7}`):**
    `8` is the exact minimal vertex number for connected non-induced (edge-subset)
    subgraph count vector vs. adjacency-spectrum separation: NO separating pair exists
    for ANY `n ≤ 7` (in particular at `n = 6` or `n = 7`), whereas both disconnected
    and connected separating pairs exist at `n = 8`. -/
theorem resolution_reading_II_edge_subgraph_order_vector :
    (∀ n ≤ 7, ¬ HasEdgeSubgraphOrderSeparation n) ∧
    HasEdgeSubgraphOrderSeparation 8 ∧
    (∃ G₁ G₂ : SimpleGraphN 8,
      IsConnectedGraph G₁ ∧ IsConnectedGraph G₂ ∧
      connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂ ∧ charPoly G₁ ≠ charPoly G₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn ⟨G₁, G₂, hv, hne⟩
    exact hne (no_connEdgeSubgraph_sep_le_7 hn G₁ G₂ hv).2
  · rcases exists_connEdgeSubgraph_sep_8 with ⟨G₁, G₂, _, _, hv, _, hne⟩
    exact ⟨G₁, G₂, hv, hne⟩
  · rcases exists_connEdgeSubgraph_sep_8 with ⟨G₁, G₂, hc1, hc2, hv, _, hne⟩
    exact ⟨G₁, G₂, hc1, hc2, hv, hne⟩

/-- **Master Theorem III (Reading III — Impossibility at All `n ∈ ℕ` for Isomorphism-Class Counts):**
    For ALL `n₁, n₂ ∈ ℕ` and ALL `G₁ : SimpleGraphN n₁`, `G₂ : SimpleGraphN n₂`,
    equality of connected subgraph isomorphism counts (induced OR non-induced)
    forces `G₁ ≅ G₂` and identical adjacency spectra; no separation exists at ANY `n`. -/
theorem resolution_reading_III_isomorphism_class_counts :
    (¬ ∃ (n : Nat) (G₁ G₂ : SimpleGraphN n),
      (∀ k (H : SimpleGraphN k), IsConnectedGraph H → indIsoCount H G₁ = indIsoCount H G₂) ∧
      charPoly G₁ ≠ charPoly G₂) ∧
    (¬ ∃ (n : Nat) (G₁ G₂ : SimpleGraphN n),
      (∀ k (H : SimpleGraphN k), IsConnectedGraph H → subIsoCount H G₁ = subIsoCount H G₂) ∧
      charPoly G₁ ≠ charPoly G₂) :=
  ⟨no_conn_indIsoCount_spectrum_separation, no_conn_subIsoCount_spectrum_separation⟩

end Conjecture00000003970
