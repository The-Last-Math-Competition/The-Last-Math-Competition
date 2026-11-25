/-
  Conjecture 00000003970 — Reading II: Connected Non-Induced (Edge-Subset)
  Subgraph Order-Vector `c^sub(G)` & Bonus Unrestricted Vector `s^sub(G)`
  Complete Resolution:
    1. NO separating pair for `connEdgeSubgraphVec` exists for ANY `n ≤ 7`
       (`no_connEdgeSubgraph_sep_le_7`), REFUTING both `n = 6` and `n = 7`!
    2. Separating pairs DO exist at `n = 8` — both disconnected (`G8_Claw2K2` vs `G8_P4_P3_K1`,
       `m = 5` forests) AND connected (`G8_Conn_A` vs `G8_Conn_B`, `m = 12`, which simultaneously
       share `connEdgeSubgraphVec` and `allEdgeSubgraphVec`), proving `n_min(c^sub) = 8`!
    3. Bonus Diagnostic Theorem (`n_min(s^sub) = 7`): for the unrestricted subgraph count vector
       `allEdgeSubgraphVec` (matching Sentence 1 of `SOURCE.md` without connectedness),
       NO separating pair exists for `n ≤ 6`, and a connected separating pair exists at `n = 7`!
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.FastPackedEval

namespace Conjecture00000003970

/-! ### Part 1: Non-Existence of `c^sub` Separation for All `n ≤ 7` (Including `n = 6` and `n = 7`) -/

theorem inj_connEdge_1 :
    (nmInsertBST (fastConnEdgeKey32 1) canonBST1 .empty).isSome = true := rfl
theorem inj_connEdge_2 :
    (nmInsertBST (fastConnEdgeKey32 2) canonBST2 .empty).isSome = true := rfl
theorem inj_connEdge_3 :
    (nmInsertBST (fastConnEdgeKey32 3) canonBST3 .empty).isSome = true := rfl
theorem inj_connEdge_4 :
    (nmInsertBST (fastConnEdgeKey32 4) canonBST4 .empty).isSome = true := rfl
theorem inj_connEdge_5 :
    (nmInsertBST (fastConnEdgeKey32 5) canonBST5 .empty).isSome = true := rfl

set_option maxHeartbeats 2000000 in
theorem inj_connEdge_6 :
    (nmInsertBST (fastConnEdgeKey32 6) canonBST6 .empty).isSome = true := rfl

set_option maxHeartbeats 40000000 in
theorem inj_connEdge_7 :
    (nmInsertBST (fastConnEdgeKey32 7) canonBST7 .empty).isSome = true := rfl

theorem no_connEdge_sep_of_canon {n : Nat} (hn : n ≤ 8) {bst : NatBST}
    (hred : ∀ G : SimpleGraphN n, ∃ m ∈ bstToList bst, GraphIso G (graphOfAdjMask n m))
    (hinj : (nmInsertBST (fastConnEdgeKey32 n) bst .empty).isSome = true)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  rcases hred G₁ with ⟨m₁, hm₁, hiso₁⟩
  rcases hred G₂ with ⟨m₂, hm₂, hiso₂⟩
  have hv₁ := hiso₁.connEdgeSubgraphVec_eq
  have hv₂ := hiso₂.connEdgeSubgraphVec_eq
  have hf : fastConnEdgeSubgraphVec (graphOfAdjMask n m₁) = fastConnEdgeSubgraphVec (graphOfAdjMask n m₂) := by
    rw [← connEdgeSubgraphVec_eq_fast, ← connEdgeSubgraphVec_eq_fast]
    exact hv₁.symm.trans (hvec.trans hv₂)
  have hk : fastConnEdgeKey32 n m₁ = fastConnEdgeKey32 n m₂ := by
    rw [fastConnEdgeKey32_eq hn m₁, fastConnEdgeKey32_eq hn m₂, hf]
  have hm_eq : m₁ = m₂ := nmInsertBST_sound hinj m₁ hm₁ m₂ hm₂ hk
  subst hm_eq
  have hiso : GraphIso G₁ G₂ := hiso₁.trans hiso₂.symm
  exact ⟨hiso, hiso.charPoly_eq⟩

/-- **Theorem II.1 (Minimality Lower Bound `n ≥ 8` for `c^sub`, Refuting `6` and `7`):**
    For EVERY `n ≤ 7` and ALL `G₁, G₂ : SimpleGraphN n`, equal connected edge-subset
    subgraph count vectors force `G₁ ≅ G₂` and identical characteristic polynomials! -/
theorem no_connEdgeSubgraph_sep_le_7 {n : Nat} (hn : n ≤ 7)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  match n with
  | 0 =>
    have hG : G₁ = G₂ := SimpleGraphN.ext (funext fun u => u.elim0)
    subst hG; exact ⟨GraphIso.refl G₁, rfl⟩
  | 1 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_1 inj_connEdge_1 G₁ G₂ hvec
  | 2 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_2 inj_connEdge_2 G₁ G₂ hvec
  | 3 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_3 inj_connEdge_3 G₁ G₂ hvec
  | 4 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_4 inj_connEdge_4 G₁ G₂ hvec
  | 5 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_5 inj_connEdge_5 G₁ G₂ hvec
  | 6 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_6 inj_connEdge_6 G₁ G₂ hvec
  | 7 => exact no_connEdge_sep_of_canon (by omega) canon_reduction_7 inj_connEdge_7 G₁ G₂ hvec
  | _ + 8 => omega

/-! ### Part 2: Explicit Minimal Separating Pairs at `n = 8` (Disconnected & Connected) -/

/-- Minimal Disconnected Forest Witness A (`n = 8, m = 5`): `K_{1,3} ⊔ 2K₂`, edges `01,06,07,23,45`. -/
def G8_Claw2K2 : SimpleGraphN 8 := graphOfAdjMask 8 72356798707270082

/-- Minimal Disconnected Forest Witness B (`n = 8, m = 5`): `P₄ ⊔ P₃ ⊔ K₁`, edges `01,04,15,23,26`. -/
def G8_P4_P3_K1 : SimpleGraphN 8 := graphOfAdjMask 8 1128103296901394

set_option maxHeartbeats 2000000 in
theorem sep_forest_pair_G8 :
    connEdgeSubgraphVec G8_Claw2K2 = [8, 5, 3, 1, 0, 0, 0, 0] ∧
    connEdgeSubgraphVec G8_P4_P3_K1 = [8, 5, 3, 1, 0, 0, 0, 0] ∧
    polyEval (charPoly G8_Claw2K2) 1 = 0 ∧
    polyEval (charPoly G8_P4_P3_K1) 1 = 1 ∧
    charPoly G8_Claw2K2 ≠ charPoly G8_P4_P3_K1 := by
  have h1 : connEdgeSubgraphVec G8_Claw2K2 = [8, 5, 3, 1, 0, 0, 0, 0] :=
    (connEdgeSubgraphVec_mask_eq (by omega) 72356798707270082).trans rfl
  have h2 : connEdgeSubgraphVec G8_P4_P3_K1 = [8, 5, 3, 1, 0, 0, 0, 0] :=
    (connEdgeSubgraphVec_mask_eq (by omega) 1128103296901394).trans rfl
  have he1 : polyEval (charPoly G8_Claw2K2) 1 = 0 :=
    (polyEval_charPoly_eq_fast G8_Claw2K2 1).trans rfl
  have he2 : polyEval (charPoly G8_P4_P3_K1) 1 = 1 :=
    (polyEval_charPoly_eq_fast G8_P4_P3_K1 1).trans rfl
  refine ⟨h1, h2, he1, he2, fun hcp => ?_⟩
  exact absurd (he1.symm.trans ((congrArg (fun p => polyEval p 1) hcp).trans he2)) (by decide)

/-- Minimal Connected Witness A (`n = 8, m = 12`), edges `01,02,03,04,12,13,24,25,26,35,56,57`. -/
def G8_Conn_A : SimpleGraphN 8 := graphOfAdjMask 8 2316200430816922910

/-- Minimal Connected Witness B (`n = 8, m = 12`), edges `01,02,03,04,07,12,13,24,25,35,36,56`. -/
def G8_Conn_B : SimpleGraphN 8 := graphOfAdjMask 8 83400179129191838

set_option maxHeartbeats 4000000 in
theorem sep_conn_pair_G8 :
    IsConnectedGraph G8_Conn_A ∧ IsConnectedGraph G8_Conn_B ∧
    connEdgeSubgraphVec G8_Conn_A = [8, 12, 34, 102, 298, 716, 1086, 592] ∧
    connEdgeSubgraphVec G8_Conn_B = [8, 12, 34, 102, 298, 716, 1086, 592] ∧
    allEdgeSubgraphVec G8_Conn_A = [8, 40, 162, 558, 1618, 3712, 5760, 4096] ∧
    allEdgeSubgraphVec G8_Conn_B = [8, 40, 162, 558, 1618, 3712, 5760, 4096] ∧
    polyEval (charPoly G8_Conn_A) 1 = 6 ∧
    polyEval (charPoly G8_Conn_B) 1 = 14 ∧
    charPoly G8_Conn_A ≠ charPoly G8_Conn_B := by
  have hcA : IsConnectedGraph G8_Conn_A := (isConnectedGraph_iff_fast G8_Conn_A).mpr rfl
  have hcB : IsConnectedGraph G8_Conn_B := (isConnectedGraph_iff_fast G8_Conn_B).mpr rfl
  have hvA : connEdgeSubgraphVec G8_Conn_A = [8, 12, 34, 102, 298, 716, 1086, 592] :=
    (connEdgeSubgraphVec_mask_eq (by omega) 2316200430816922910).trans rfl
  have hvB : connEdgeSubgraphVec G8_Conn_B = [8, 12, 34, 102, 298, 716, 1086, 592] :=
    (connEdgeSubgraphVec_mask_eq (by omega) 83400179129191838).trans rfl
  have haA : allEdgeSubgraphVec G8_Conn_A = [8, 40, 162, 558, 1618, 3712, 5760, 4096] :=
    (allEdgeSubgraphVec_mask_eq (by omega) 2316200430816922910).trans rfl
  have haB : allEdgeSubgraphVec G8_Conn_B = [8, 40, 162, 558, 1618, 3712, 5760, 4096] :=
    (allEdgeSubgraphVec_mask_eq (by omega) 83400179129191838).trans rfl
  have heA : polyEval (charPoly G8_Conn_A) 1 = 6 :=
    (polyEval_charPoly_eq_fast G8_Conn_A 1).trans rfl
  have heB : polyEval (charPoly G8_Conn_B) 1 = 14 :=
    (polyEval_charPoly_eq_fast G8_Conn_B 1).trans rfl
  refine ⟨hcA, hcB, hvA, hvB, haA, haB, heA, heB, fun hcp => ?_⟩
  exact absurd (heA.symm.trans ((congrArg (fun p => polyEval p 1) hcp).trans heB)) (by decide)

/-- **Theorem II.2 (Existence at `n = 8`, Connected & Simultaneous):**
    There exist two connected 8-vertex simple graphs that simultaneously share
    `connEdgeSubgraphVec` and `allEdgeSubgraphVec`, while their adjacency
    characteristic polynomials differ! -/
theorem exists_connEdgeSubgraph_sep_8 :
    ∃ G₁ G₂ : SimpleGraphN 8,
      IsConnectedGraph G₁ ∧ IsConnectedGraph G₂ ∧
      connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂ ∧
      allEdgeSubgraphVec G₁ = allEdgeSubgraphVec G₂ ∧
      charPoly G₁ ≠ charPoly G₂ :=
  ⟨G8_Conn_A, G8_Conn_B,
   sep_conn_pair_G8.1, sep_conn_pair_G8.2.1,
   sep_conn_pair_G8.2.2.1.trans sep_conn_pair_G8.2.2.2.1.symm,
   sep_conn_pair_G8.2.2.2.2.1.trans sep_conn_pair_G8.2.2.2.2.2.1.symm,
   sep_conn_pair_G8.2.2.2.2.2.2.2.2⟩

/-! ### Part 3: Bonus Diagnostic Theorem (`n_min(s^sub) = 7` for Unrestricted `allEdgeSubgraphVec`) -/

theorem inj_allEdge_1 :
    (nmInsertBST (fastAllEdgeKey32 1) canonBST1 .empty).isSome = true := rfl
theorem inj_allEdge_2 :
    (nmInsertBST (fastAllEdgeKey32 2) canonBST2 .empty).isSome = true := rfl
theorem inj_allEdge_3 :
    (nmInsertBST (fastAllEdgeKey32 3) canonBST3 .empty).isSome = true := rfl
theorem inj_allEdge_4 :
    (nmInsertBST (fastAllEdgeKey32 4) canonBST4 .empty).isSome = true := rfl
theorem inj_allEdge_5 :
    (nmInsertBST (fastAllEdgeKey32 5) canonBST5 .empty).isSome = true := rfl

set_option maxHeartbeats 2000000 in
theorem inj_allEdge_6 :
    (nmInsertBST (fastAllEdgeKey32 6) canonBST6 .empty).isSome = true := rfl

theorem no_allEdge_sep_of_canon {n : Nat} (hn : n ≤ 8) {bst : NatBST}
    (hred : ∀ G : SimpleGraphN n, ∃ m ∈ bstToList bst, GraphIso G (graphOfAdjMask n m))
    (hinj : (nmInsertBST (fastAllEdgeKey32 n) bst .empty).isSome = true)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : allEdgeSubgraphVec G₁ = allEdgeSubgraphVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  rcases hred G₁ with ⟨m₁, hm₁, hiso₁⟩
  rcases hred G₂ with ⟨m₂, hm₂, hiso₂⟩
  have hf : fastAllEdgeSubgraphVec (graphOfAdjMask n m₁) = fastAllEdgeSubgraphVec (graphOfAdjMask n m₂) := by
    rw [← allEdgeSubgraphVec_eq_fast, ← allEdgeSubgraphVec_eq_fast]
    exact hiso₁.allEdgeSubgraphVec_eq.symm.trans (hvec.trans hiso₂.allEdgeSubgraphVec_eq)
  have hk : fastAllEdgeKey32 n m₁ = fastAllEdgeKey32 n m₂ := by
    rw [fastAllEdgeKey32_eq hn m₁, fastAllEdgeKey32_eq hn m₂, hf]
  have hm_eq : m₁ = m₂ := nmInsertBST_sound hinj m₁ hm₁ m₂ hm₂ hk
  subst hm_eq
  have hiso : GraphIso G₁ G₂ := hiso₁.trans hiso₂.symm
  exact ⟨hiso, hiso.charPoly_eq⟩

theorem no_allEdgeSubgraph_sep_le_6 {n : Nat} (hn : n ≤ 6)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : allEdgeSubgraphVec G₁ = allEdgeSubgraphVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  match n with
  | 0 =>
    have hG : G₁ = G₂ := SimpleGraphN.ext (funext fun u => u.elim0)
    subst hG; exact ⟨GraphIso.refl G₁, rfl⟩
  | 1 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_1 inj_allEdge_1 G₁ G₂ hvec
  | 2 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_2 inj_allEdge_2 G₁ G₂ hvec
  | 3 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_3 inj_allEdge_3 G₁ G₂ hvec
  | 4 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_4 inj_allEdge_4 G₁ G₂ hvec
  | 5 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_5 inj_allEdge_5 G₁ G₂ hvec
  | 6 => exact no_allEdge_sep_of_canon (by omega) canon_reduction_6 inj_allEdge_6 G₁ G₂ hvec
  | _ + 7 => omega

def G7_AllSub_A : SimpleGraphN 7 := graphOfAdjMask 7 14028508521670

def G7_AllSub_B : SimpleGraphN 7 := graphOfAdjMask 7 213881062573206

set_option maxHeartbeats 2000000 in
theorem sep_allEdge_pair_G7 :
    IsConnectedGraph G7_AllSub_A ∧ IsConnectedGraph G7_AllSub_B ∧
    allEdgeSubgraphVec G7_AllSub_A = [7, 29, 87, 196, 328, 384, 256] ∧
    allEdgeSubgraphVec G7_AllSub_B = [7, 29, 87, 196, 328, 384, 256] ∧
    polyEval (charPoly G7_AllSub_A) 1 = 0 ∧
    polyEval (charPoly G7_AllSub_B) 1 = 12 ∧
    charPoly G7_AllSub_A ≠ charPoly G7_AllSub_B := by
  have hcA : IsConnectedGraph G7_AllSub_A := (isConnectedGraph_iff_fast G7_AllSub_A).mpr rfl
  have hcB : IsConnectedGraph G7_AllSub_B := (isConnectedGraph_iff_fast G7_AllSub_B).mpr rfl
  have haA : allEdgeSubgraphVec G7_AllSub_A = [7, 29, 87, 196, 328, 384, 256] :=
    (allEdgeSubgraphVec_mask_eq (by omega) 14028508521670).trans rfl
  have haB : allEdgeSubgraphVec G7_AllSub_B = [7, 29, 87, 196, 328, 384, 256] :=
    (allEdgeSubgraphVec_mask_eq (by omega) 213881062573206).trans rfl
  have heA : polyEval (charPoly G7_AllSub_A) 1 = 0 :=
    (polyEval_charPoly_eq_fast G7_AllSub_A 1).trans rfl
  have heB : polyEval (charPoly G7_AllSub_B) 1 = 12 :=
    (polyEval_charPoly_eq_fast G7_AllSub_B 1).trans rfl
  refine ⟨hcA, hcB, haA, haB, heA, heB, fun hcp => ?_⟩
  exact absurd (heA.symm.trans ((congrArg (fun p => polyEval p 1) hcp).trans heB)) (by decide)

end Conjecture00000003970
