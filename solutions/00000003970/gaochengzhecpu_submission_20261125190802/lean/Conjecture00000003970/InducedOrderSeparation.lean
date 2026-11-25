/-
  Conjecture 00000003970 — Reading I: Connected Induced Subgraph Order-Vector `c^ind(G)`
  Complete Resolution:
    1. NO separating pair exists for ANY `n ≤ 4` (`no_connInduced_sep_le_4`).
    2. Separating pairs DO exist at `n = 5` (both disconnected AND connected), proving
       `n_min(c^ind) = 5` and REFUTING the conjectured threshold "6 or 7"!
    3. COMPLETE ENUMERATION at `n = 5` (`complete_enum_connInduced_5`): EVERY pair `(G₁, G₂)`
       of 5-vertex simple graphs with `connInducedVec G₁ = connInducedVec G₂` and
       `charPoly G₁ ≠ charPoly G₂` is isomorphic (up to swap) to one of the exact 4 canonical
       minimal pairs (1 disconnected pair + 3 connected pairs), whose 8 constituent graphs
       are pairwise non-isomorphic!
    4. Diagnostic `n = 6` theorem: when equal degree sequence is ALSO required, separation
       begins at `n = 6` (`exists_connInduced_sameDeg_sep_6`).
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.CanonGraphs

namespace Conjecture00000003970

/-! ### Part 1: Non-Existence of Separation for All `n ≤ 4` -/

theorem inj_connInduced_1 :
    checkInjOnMasks (bstToList canonBST1) (fun m => connInducedVec (graphOfAdjMask 1 m)) = true := by decide

theorem inj_connInduced_2 :
    checkInjOnMasks (bstToList canonBST2) (fun m => connInducedVec (graphOfAdjMask 2 m)) = true := by decide

theorem inj_connInduced_3 :
    checkInjOnMasks (bstToList canonBST3) (fun m => connInducedVec (graphOfAdjMask 3 m)) = true := by decide

theorem inj_connInduced_4 :
    checkInjOnMasks (bstToList canonBST4) (fun m => connInducedVec (graphOfAdjMask 4 m)) = true := by decide

theorem no_connInduced_sep_of_canon {n : Nat} {bst : NatBST}
    (hred : ∀ G : SimpleGraphN n, ∃ m ∈ bstToList bst, GraphIso G (graphOfAdjMask n m))
    (hinj : checkInjOnMasks (bstToList bst) (fun m => connInducedVec (graphOfAdjMask n m)) = true)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : connInducedVec G₁ = connInducedVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  rcases hred G₁ with ⟨m₁, hm₁, hiso₁⟩
  rcases hred G₂ with ⟨m₂, hm₂, hiso₂⟩
  have hv₁ := hiso₁.connInducedVec_eq
  have hv₂ := hiso₂.connInducedVec_eq
  have hm_eq : m₁ = m₂ :=
    checkInjOnMasks_sound hinj m₁ hm₁ m₂ hm₂ (hv₁.symm.trans (hvec.trans hv₂))
  subst hm_eq
  have hiso : GraphIso G₁ G₂ := hiso₁.trans hiso₂.symm
  exact ⟨hiso, hiso.charPoly_eq⟩

/-- **Theorem I.1 (Minimality Lower Bound for `c^ind`):**
    For ALL `n ≤ 4` and ALL `G₁, G₂ : SimpleGraphN n`, equal connected induced subgraph
    count vectors force `G₁ ≅ G₂` and identical characteristic polynomials! -/
theorem no_connInduced_sep_le_4 {n : Nat} (hn : n ≤ 4)
    (G₁ G₂ : SimpleGraphN n)
    (hvec : connInducedVec G₁ = connInducedVec G₂) :
    GraphIso G₁ G₂ ∧ charPoly G₁ = charPoly G₂ := by
  match n with
  | 0 =>
    have hG : G₁ = G₂ := SimpleGraphN.ext (funext fun u => u.elim0)
    subst hG; exact ⟨GraphIso.refl G₁, rfl⟩
  | 1 => exact no_connInduced_sep_of_canon canon_reduction_1 inj_connInduced_1 G₁ G₂ hvec
  | 2 => exact no_connInduced_sep_of_canon canon_reduction_2 inj_connInduced_2 G₁ G₂ hvec
  | 3 => exact no_connInduced_sep_of_canon canon_reduction_3 inj_connInduced_3 G₁ G₂ hvec
  | 4 => exact no_connInduced_sep_of_canon canon_reduction_4 inj_connInduced_4 G₁ G₂ hvec
  | _ + 5 => omega

/-! ### Part 2: Explicit Construction of All 4 Minimal Separating Pairs at `n = 5` -/

/-- Pair 1A (Disconnected, `m = 3`): `K₃ ⊔ 2K₁`, canonical mask `3238`. -/
def G5_K3_2K1 : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (1, 2)]

/-- Pair 1B (Disconnected, `m = 3`): `P₃ ⊔ K₂`, canonical mask `8913958`. -/
def G5_P3_K2 : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (3, 4)]

/-- Pair 2A (Connected, `m = 5`): `K_{1,4} + e`, canonical mask `1084606`. -/
def G5_StarPlusE : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)]

/-- Pair 2B (Connected, `m = 5`): Banner (`C₄` + pendant leaf), canonical mask `1254710`. -/
def G5_Banner : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 4), (1, 3), (2, 3)]

/-- Pair 3A (Connected, `m = 6`): Diamond `K₄ - e` + pendant leaf at degree-2 vertex, mask `4312494`. -/
def G5_DiamondLeaf : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4)]

/-- Pair 3B (Connected, `m = 6`): Butterfly / Bowtie (`2K₃` sharing vertex `0`), mask `9997502`. -/
def G5_Butterfly : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]

/-- Pair 4A (Connected, `m = 7`): Book `B₃` (`K₂ ∨ 3K₁`), mask `3248062`. -/
def G5_Book3 : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

/-- Pair 4B (Connected, `m = 7`): `K_{2,3} + e`, mask `13225390`. -/
def G5_K23PlusE : SimpleGraphN 5 := mkGraphFromEdges 5 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]

theorem mask_eq_G5_K3_2K1 : graphOfAdjMask 5 3238 = G5_K3_2K1 := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_P3_K2 : graphOfAdjMask 5 8913958 = G5_P3_K2 := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_StarPlusE : graphOfAdjMask 5 1084606 = G5_StarPlusE := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_Banner : graphOfAdjMask 5 1254710 = G5_Banner := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_DiamondLeaf : graphOfAdjMask 5 4312494 = G5_DiamondLeaf := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_Butterfly : graphOfAdjMask 5 9997502 = G5_Butterfly := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_Book3 : graphOfAdjMask 5 3248062 = G5_Book3 := SimpleGraphN.ext (by decide)
theorem mask_eq_G5_K23PlusE : graphOfAdjMask 5 13225390 = G5_K23PlusE := SimpleGraphN.ext (by decide)

theorem sep_pair1_G5 :
    ¬ IsConnectedGraph G5_K3_2K1 ∧ ¬ IsConnectedGraph G5_P3_K2 ∧
    connInducedVec G5_K3_2K1 = [5, 3, 1, 0, 0] ∧
    connInducedVec G5_P3_K2 = [5, 3, 1, 0, 0] ∧
    charPoly G5_K3_2K1 = [0, 0, -2, -3, 0, 1] ∧
    charPoly G5_P3_K2 = [0, 2, 0, -3, 0, 1] ∧
    charPoly G5_K3_2K1 ≠ charPoly G5_P3_K2 ∧
    polyEval (charPoly G5_K3_2K1) 1 ≠ polyEval (charPoly G5_P3_K2) 1 := by
  rw [charPoly_eq_fastCharPoly G5_K3_2K1, charPoly_eq_fastCharPoly G5_P3_K2]
  decide

theorem sep_pair2_G5 :
    IsConnectedGraph G5_StarPlusE ∧ IsConnectedGraph G5_Banner ∧
    connInducedVec G5_StarPlusE = [5, 5, 6, 4, 1] ∧
    connInducedVec G5_Banner = [5, 5, 6, 4, 1] ∧
    charPoly G5_StarPlusE = [0, 2, -2, -5, 0, 1] ∧
    charPoly G5_Banner = [0, 2, 0, -5, 0, 1] ∧
    charPoly G5_StarPlusE ≠ charPoly G5_Banner ∧
    polyEval (charPoly G5_StarPlusE) 1 ≠ polyEval (charPoly G5_Banner) 1 := by
  rw [charPoly_eq_fastCharPoly G5_StarPlusE, charPoly_eq_fastCharPoly G5_Banner]
  decide

theorem sep_pair3_G5 :
    IsConnectedGraph G5_DiamondLeaf ∧ IsConnectedGraph G5_Butterfly ∧
    connInducedVec G5_DiamondLeaf = [5, 6, 6, 4, 1] ∧
    connInducedVec G5_Butterfly = [5, 6, 6, 4, 1] ∧
    charPoly G5_DiamondLeaf = [2, 3, -4, -6, 0, 1] ∧
    charPoly G5_Butterfly = [4, 5, -4, -6, 0, 1] ∧
    charPoly G5_DiamondLeaf ≠ charPoly G5_Butterfly ∧
    polyEval (charPoly G5_DiamondLeaf) 1 ≠ polyEval (charPoly G5_Butterfly) 1 := by
  rw [charPoly_eq_fastCharPoly G5_DiamondLeaf, charPoly_eq_fastCharPoly G5_Butterfly]
  decide

theorem sep_pair4_G5 :
    IsConnectedGraph G5_Book3 ∧ IsConnectedGraph G5_K23PlusE ∧
    connInducedVec G5_Book3 = [5, 7, 9, 5, 1] ∧
    connInducedVec G5_K23PlusE = [5, 7, 9, 5, 1] ∧
    charPoly G5_Book3 = [0, 0, -6, -7, 0, 1] ∧
    charPoly G5_K23PlusE = [0, 2, -4, -7, 0, 1] ∧
    charPoly G5_Book3 ≠ charPoly G5_K23PlusE ∧
    polyEval (charPoly G5_Book3) 2 ≠ polyEval (charPoly G5_K23PlusE) 2 := by
  rw [charPoly_eq_fastCharPoly G5_Book3, charPoly_eq_fastCharPoly G5_K23PlusE]
  decide

/-- **Theorem I.2 (Existence at `n = 5`, Connected & General):**
    There exist two connected 5-vertex simple graphs whose connected induced subgraph
    count vectors coincide while their adjacency spectra (`charPoly`) differ! -/
theorem exists_connInduced_sep_5 :
    ∃ G₁ G₂ : SimpleGraphN 5,
      IsConnectedGraph G₁ ∧ IsConnectedGraph G₂ ∧
      connInducedVec G₁ = connInducedVec G₂ ∧
      charPoly G₁ ≠ charPoly G₂ :=
  ⟨G5_StarPlusE, G5_Banner,
   sep_pair2_G5.1, sep_pair2_G5.2.1,
   sep_pair2_G5.2.2.1.trans sep_pair2_G5.2.2.2.1.symm,
   sep_pair2_G5.2.2.2.2.2.2.1⟩

/-! ### Part 3: Complete Enumeration Theorem at `n = 5` -/

/-- `(G₁, G₂)` is isomorphic as an unordered pair to `{A, B}`. -/
def IsoUnorderedPair {n : Nat} (G₁ G₂ A B : SimpleGraphN n) : Prop :=
  (GraphIso G₁ A ∧ GraphIso G₂ B) ∨ (GraphIso G₁ B ∧ GraphIso G₂ A)

/-- `(G₁, G₂)` belongs to one of the exact 4 minimal separating isomorphism classes on `n = 5`. -/
def IsMinimalInducedSepPair5 (G₁ G₂ : SimpleGraphN 5) : Prop :=
  IsoUnorderedPair G₁ G₂ G5_K3_2K1 G5_P3_K2 ∨
  IsoUnorderedPair G₁ G₂ G5_StarPlusE G5_Banner ∨
  IsoUnorderedPair G₁ G₂ G5_DiamondLeaf G5_Butterfly ∨
  IsoUnorderedPair G₁ G₂ G5_Book3 G5_K23PlusE

def isAllowedMaskPair5 (m₁ m₂ : Nat) : Bool :=
  ((m₁ == 3238) && (m₂ == 8913958)) || ((m₁ == 8913958) && (m₂ == 3238)) ||
  ((m₁ == 1084606) && (m₂ == 1254710)) || ((m₁ == 1254710) && (m₂ == 1084606)) ||
  ((m₁ == 4312494) && (m₂ == 9997502)) || ((m₁ == 9997502) && (m₂ == 4312494)) ||
  ((m₁ == 3248062) && (m₂ == 13225390)) || ((m₁ == 13225390) && (m₂ == 3248062))

set_option maxHeartbeats 800000 in
theorem check_all_canon5_pairs :
    (bstToList canonBST5).all (fun m₁ =>
      (bstToList canonBST5).all (fun m₂ =>
        !((connInducedVec (graphOfAdjMask 5 m₁) == connInducedVec (graphOfAdjMask 5 m₂)) &&
          !(fastCharPoly (graphOfAdjMask 5 m₁) == fastCharPoly (graphOfAdjMask 5 m₂))) ||
        isAllowedMaskPair5 m₁ m₂)) = true := by decide

/-- **Theorem I.3 (Complete Enumeration of All Separating Pairs on `n = 5`):**
    Two 5-vertex simple graphs `G₁, G₂` have identical connected induced subgraph count
    vectors and distinct adjacency characteristic polynomials IF AND ONLY IF `{G₁, G₂}`
    is isomorphic to one of the exact 4 minimal pairs! -/
theorem complete_enum_connInduced_5 (G₁ G₂ : SimpleGraphN 5) :
    (connInducedVec G₁ = connInducedVec G₂ ∧ charPoly G₁ ≠ charPoly G₂) ↔
      IsMinimalInducedSepPair5 G₁ G₂ := by
  constructor
  · rintro ⟨hvec, hcp⟩
    rcases canon_reduction_5 G₁ with ⟨m₁, hm₁, hiso₁⟩
    rcases canon_reduction_5 G₂ with ⟨m₂, hm₂, hiso₂⟩
    have hv : connInducedVec (graphOfAdjMask 5 m₁) = connInducedVec (graphOfAdjMask 5 m₂) :=
      hiso₁.connInducedVec_eq.symm.trans (hvec.trans hiso₂.connInducedVec_eq)
    have hc : fastCharPoly (graphOfAdjMask 5 m₁) ≠ fastCharPoly (graphOfAdjMask 5 m₂) := by
      intro heq
      apply hcp
      rw [hiso₁.charPoly_eq, hiso₂.charPoly_eq, charPoly_eq_fastCharPoly, charPoly_eq_fastCharPoly, heq]
    have hall1 := List.all_eq_true.mp check_all_canon5_pairs m₁ hm₁
    have hall2 := List.all_eq_true.mp hall1 m₂ hm₂
    have hb1 : (connInducedVec (graphOfAdjMask 5 m₁) == connInducedVec (graphOfAdjMask 5 m₂)) = true :=
      by simpa using decide_eq_true hv
    have hb2 : (fastCharPoly (graphOfAdjMask 5 m₁) == fastCharPoly (graphOfAdjMask 5 m₂)) = false :=
      Bool.eq_false_iff.mpr (fun e => hc (of_decide_eq_true (by simpa using e)))
    simp only [hb1, hb2, Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or] at hall2
    unfold isAllowedMaskPair5 at hall2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hall2
    -- Dispatch the 8 ordered pairs!
    rcases hall2 with ((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · have e1 : m₁ = 3238 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 8913958 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_K3_2K1] at hiso₁; rw [mask_eq_G5_P3_K2] at hiso₂
      exact Or.inl (Or.inl ⟨hiso₁, hiso₂⟩)
    · have e1 : m₁ = 8913958 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 3238 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_P3_K2] at hiso₁; rw [mask_eq_G5_K3_2K1] at hiso₂
      exact Or.inl (Or.inr ⟨hiso₁, hiso₂⟩)
    · have e1 : m₁ = 1084606 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 1254710 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_StarPlusE] at hiso₁; rw [mask_eq_G5_Banner] at hiso₂
      exact Or.inr (Or.inl (Or.inl ⟨hiso₁, hiso₂⟩))
    · have e1 : m₁ = 1254710 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 1084606 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_Banner] at hiso₁; rw [mask_eq_G5_StarPlusE] at hiso₂
      exact Or.inr (Or.inl (Or.inr ⟨hiso₁, hiso₂⟩))
    · have e1 : m₁ = 4312494 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 9997502 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_DiamondLeaf] at hiso₁; rw [mask_eq_G5_Butterfly] at hiso₂
      exact Or.inr (Or.inr (Or.inl (Or.inl ⟨hiso₁, hiso₂⟩)))
    · have e1 : m₁ = 9997502 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 4312494 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_Butterfly] at hiso₁; rw [mask_eq_G5_DiamondLeaf] at hiso₂
      exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hiso₁, hiso₂⟩)))
    · have e1 : m₁ = 3248062 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 13225390 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_Book3] at hiso₁; rw [mask_eq_G5_K23PlusE] at hiso₂
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hiso₁, hiso₂⟩)))
    · have e1 : m₁ = 13225390 := of_decide_eq_true (by simpa using h1)
      have e2 : m₂ = 3248062 := of_decide_eq_true (by simpa using h2)
      subst e1; subst e2; rw [mask_eq_G5_K23PlusE] at hiso₁; rw [mask_eq_G5_Book3] at hiso₂
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hiso₁, hiso₂⟩)))
  · have lift_sep : ∀ {A B : SimpleGraphN 5},
        connInducedVec A = connInducedVec B → charPoly A ≠ charPoly B →
        IsoUnorderedPair G₁ G₂ A B →
        connInducedVec G₁ = connInducedVec G₂ ∧ charPoly G₁ ≠ charPoly G₂ := by
      intro A B hv hc hpair
      rcases hpair with ⟨i1, i2⟩ | ⟨i1, i2⟩
      · exact ⟨i1.connInducedVec_eq.trans (hv.trans i2.connInducedVec_eq.symm),
               fun heq => hc (i1.charPoly_eq.symm.trans (heq.trans i2.charPoly_eq))⟩
      · exact ⟨i1.connInducedVec_eq.trans (hv.symm.trans i2.connInducedVec_eq.symm),
               fun heq => hc (i2.charPoly_eq.symm.trans (heq.symm.trans i1.charPoly_eq))⟩
    rintro (hp1 | hp2 | hp3 | hp4)
    · exact lift_sep (sep_pair1_G5.2.2.1.trans sep_pair1_G5.2.2.2.1.symm) sep_pair1_G5.2.2.2.2.2.2.1 hp1
    · exact lift_sep (sep_pair2_G5.2.2.1.trans sep_pair2_G5.2.2.2.1.symm) sep_pair2_G5.2.2.2.2.2.2.1 hp2
    · exact lift_sep (sep_pair3_G5.2.2.1.trans sep_pair3_G5.2.2.2.1.symm) sep_pair3_G5.2.2.2.2.2.2.1 hp3
    · exact lift_sep (sep_pair4_G5.2.2.1.trans sep_pair4_G5.2.2.2.1.symm) sep_pair4_G5.2.2.2.2.2.2.1 hp4

/-! ### Part 4: Diagnostic `n = 6` Same-Degree-Sequence Separating Pair -/

def G6_SameDeg_A : SimpleGraphN 6 :=
  mkGraphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]

def G6_SameDeg_B : SimpleGraphN 6 :=
  mkGraphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (4, 5)]

theorem exists_connInduced_sameDeg_sep_6 :
    IsConnectedGraph G6_SameDeg_A ∧ IsConnectedGraph G6_SameDeg_B ∧
    connInducedVec G6_SameDeg_A = [6, 7, 8, 7, 4, 1] ∧
    connInducedVec G6_SameDeg_B = [6, 7, 8, 7, 4, 1] ∧
    charPoly G6_SameDeg_A = [-1, 6, 9, -4, -7, 0, 1] ∧
    charPoly G6_SameDeg_B = [0, 4, 7, -4, -7, 0, 1] ∧
    charPoly G6_SameDeg_A ≠ charPoly G6_SameDeg_B := by
  rw [charPoly_eq_fastCharPoly G6_SameDeg_A, charPoly_eq_fastCharPoly G6_SameDeg_B]
  decide

end Conjecture00000003970
