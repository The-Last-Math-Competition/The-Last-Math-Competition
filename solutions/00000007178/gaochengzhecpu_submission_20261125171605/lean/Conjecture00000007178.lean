/-
  Conjecture 00000007178 — Master Resolution File
  Complete formal resolution (positive non-vacuity theorems + multi-model refutations)
  of Conjecture 00000007178 in Core Lean 4.19.0.
-/

import Conjecture00000007178.Algebra
import Conjecture00000007178.MatrixRank
import Conjecture00000007178.BipartiteCompletion
import Conjecture00000007178.SymmetricCycles
import Conjecture00000007178.SpectralGraphMinRank

namespace Conjecture00000007178

universe u

open CommRingR FieldR

/-- Master Positive Non-Vacuity Theorem (`conjecture_00000007178_positive_nonvacuity`):
Establishes the genuine positive completion regimes across all models over arbitrary fields `F`:
1. Every everywhere-nonzero partial matrix on an acyclic bipartite forest pattern (with at least
   one specified entry, witnessed concretely by the `5`-edge spanning tree `T₅`) has exact
   minimum completion rank `1`.
2. On the odd `3`-cycle `C₃` with free diagonal, EVERY everywhere-nonzero symmetric edge assignment
   admits an exact symmetric and general rank-`1` completion (`smr = mr = 1`).
3. For spectral graph minimum rank `mr_F(G)`, `mr_F(G) = 1` holds universally iff `G` satisfies
   `ActiveCliqueProp G` (excluding acyclic `P₃` and `2K₂`). -/
theorem conjecture_00000007178_positive_nonvacuity (F : Type u) [FieldR F] :
    -- (1) Universal rank-1 completion on the 5-edge spanning tree `T₅`
    (∀ P : PartialMatrix F 3 3, P.spec = spec_T5 → P.EverywhereNonzero → IsMinCompletionRank F P 1) ∧
    -- (2) Universal rank-1 symmetric completion on odd cycle `C₃` with free diagonal
    (∀ a01 a02 a12 : F, a01 ≠ 0 → a02 ≠ 0 → a12 ≠ 0 →
      let P : PartialMatrix F 3 3 := {
        spec := spec_C3_freeDiag
        val  := fun i j =>
          match i.val, j.val with
          | 0, 1 => a01 | 1, 0 => a01
          | 0, 2 => a02 | 2, 0 => a02
          | 1, 2 => a12 | 2, 1 => a12
          | _, _ => 0
      }
      IsMinCompletionRank F P 1 ∧ IsMinSymCompletionRank F P 1) ∧
    -- (3) Universal characterization of `mr_F(G) = 1`
    (∀ (n : Nat) (G : SimpleGraph n), (∃ i₀ j₀, G.adj i₀ j₀ = true) →
      (IsGraphMinRank F G 1 ↔ ActiveCliqueProp G)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hspec hnz
    have hf : IsForestSpec P.spec := by rw [hspec]; exact spec_T5_isForest
    have hne : ∃ i₀ j₀, P.spec i₀ j₀ = true := ⟨0, 0, by rw [hspec]; rfl⟩
    exact forest_partial_matrix_minRank_one P hf hnz hne
  · intro a01 a02 a12 h01 h02 h12
    exact freeDiag_odd_C3_always_rank_one a01 a02 a12 h01 h02 h12
  · intro n G hne
    exact graph_minRank_one_iff_activeClique G hne

/-- Master Polymorphic Refutation Theorem (`conjecture_00000007178_complete_refutation`):
For EVERY field `F` with `char(F) ≠ 2` (`1 + 1 ≠ 0`), BOTH Claim I (purely combinatorial
characterization of minimum-rank completion) and Claim II (cycle-parity obstruction) are FALSE
across every standard matrix-completion and spectral-graph reading:
1. **Bipartite Partial Matrices (Even `6`-Cycle `E_{C_6}`, zero odd cycles):**
   `P_C6_plus` and `P_C6_alpha (-1)` share the exact same chordless even `6`-cycle pattern,
   are everywhere-nonzero, and satisfy `LocallyRankAtMost F 1` on ALL submatrices, yet
   `mr_F(P_C6_plus) = 1 ≠ 2 = mr_F(P_C6_alpha (-1))`.
2. **Unit-Diagonal Symmetric Partial Matrices (Chordality vs. Cycle Parity):**
   - On even `C₄`, `S_C4_plus` has `mr = smr = 1`, whereas `S_C4_minus` has all clique blocks
     symmetric of rank `1` yet `mr = 2` and `smr = 3`.
   - Both odd `C₅` AND even `C₆` satisfy `LocallyRankAtMost F 1` across ALL submatrices yet
     fail rank-`1` completability (`length ≥ 4`, NOT parity, is the boundary).
3. **Free-Diagonal Symmetric Partial Matrices:**
   - Even `C₄` obstructs (`mr = smr = 1` vs `2`), AND
   - Purely-odd-cycle Butterfly `B₂` (two `C₃` triangles sharing a vertex, ZERO even cycles)
     ALSO obstructs (`mr = smr = 1` vs `2`).
4. **Haemers Minrank Reversal:**
   Bipartite even `C₆` has `minrank_F(C₆) = 3 > 2 = minrank_F(C₆^c)`. -/
theorem conjecture_00000007178_complete_refutation (F : Type u) [FieldR F]
    (hchar : (1 : F) + 1 ≠ 0) :
    -- (1) Even C_6 bipartite partial matrix separation (1 vs 2)
    (PartialMatrix.SamePattern (P_C6_plus F) (P_C6_alpha (-1 : F)) ∧
     PartialMatrix.LocallyRankAtMost F 1 (P_C6_alpha (-1 : F)) ∧
     IsMinCompletionRank F (P_C6_plus F) 1 ∧
     IsMinCompletionRank F (P_C6_alpha (-1 : F)) 2) ∧
    -- (2) Unit-diagonal C_4 separation (1 vs 2 and 3) + both odd C_5 and even C_6 obstruct
    (IsMinCompletionRank F (S_C4_plus F) 1 ∧
     IsMinCompletionRank F (S_C4_minus F) 2 ∧
     IsMinSymCompletionRank F (S_C4_minus F) 3 ∧
     PartialMatrix.LocallyRankAtMost F 1 (S_C5_minus F) ∧
     (∀ M, (S_C5_minus F).IsCompletion M → ¬ HasRankAtMost F 1 M) ∧
     PartialMatrix.LocallyRankAtMost F 1 (S_C6_minus F) ∧
     (∀ M, (S_C6_minus F).IsCompletion M → ¬ HasRankAtMost F 1 M)) ∧
    -- (3) Free-diagonal double refutation: BOTH even C_4 AND purely-odd Butterfly B_2 obstruct
    (IsMinSymCompletionRank F (P_C4_free_plus F) 1 ∧
     IsMinSymCompletionRank F (P_C4_free_minus F) 2 ∧
     IsMinSymCompletionRank F (P_Butterfly_plus F) 1 ∧
     IsMinSymCompletionRank F (P_Butterfly_minus F) 2) ∧
    -- (4) Haemers minrank cycle-parity reversal
    (IsHaemersMinRank F G_C6 3 ∧ IsHaemersMinRank F G_C6_compl 2) := by
  have hc6 := even_C6_refutes_combinatorial_and_parity (F := F)
    (α := -1) neg_one_ne_zero (neg_one_ne_one hchar)
  have hfree4 := freeDiag_even_C4_obstruction (F := F) hchar
  have hfreeB := freeDiag_butterfly_odd_cycles_obstruct (F := F) hchar
  refine ⟨⟨hc6.1, hc6.2.2.2.2.1, hc6.2.2.2.2.2.1, hc6.2.2.2.2.2.2⟩, ?_, ?_, haemers_C6_vs_complement F⟩
  · refine ⟨(S_C4_plus_minRank_one F).1,
            S_C4_minus_minRank_two hchar,
            S_C4_minus_minSymRank_three hchar,
            S_C5_minus_locallyRankOne F,
            S_C5_minus_not_rank_one hchar,
            S_C6_minus_locallyRankOne F,
            S_C6_minus_not_rank_one hchar⟩
  · exact ⟨hfree4.2.1, hfree4.2.2.2, hfreeB.2.1, hfreeB.2.2.2⟩

/-- Master Concrete Field-Separation & Non-Vacuity Instantiation (`conjecture_00000007178_field_separation`):
Instantiates all theorems on concrete fields `𝔽₂`, `𝔽₃`, and `𝔽₄` (with ZERO hypotheses!):
1. On the `5`-vertex chordal simple graph `G₅`, `mr_{𝔽₂}(G₅) = 3` whereas `mr_{𝔽₃}(G₅) = 2`
   AND `mr_{𝔽₄}(G₅) = 2` (even within characteristic `2`!).
2. On the `7 × 7` Fano zero-nonzero pattern `Z_Fano`, `mr_{𝔽₂}^{znz}(Z_Fano) = 3` and
   `mr_{𝔽₄}^{znz}(Z_Fano) = 3` (holds over ALL char-`2` fields), whereas
   `mr_{𝔽₃}^{znz}(Z_Fano) = 4` (holds over ALL char-`≠ 2` fields).
3. Even in characteristic `2` (`𝔽₄`), `P_C6_plus` vs `P_C6_alpha ω` separates `mr = 1` from `mr = 2`
   on the incomplete chordless even `6`-cycle `spec_C6`! -/
theorem conjecture_00000007178_field_separation :
    IsGraphMinRank F2 G5 3 ∧
    IsGraphMinRank F3 G5 2 ∧
    IsGraphMinRank F4 G5 2 ∧
    IsZNZMinRank F2 Z_Fano 3 ∧
    IsZNZMinRank F4 Z_Fano 3 ∧
    IsZNZMinRank F3 Z_Fano 4 ∧
    IsMinCompletionRank F4 (P_C6_plus F4) 1 ∧
    IsMinCompletionRank F4 (P_C6_alpha F4.omega) 2 ∧
    IsMinCompletionRank F3 (P_C6_plus F3) 1 ∧
    IsMinCompletionRank F3 (P_C6_alpha (-1 : F3)) 2 := by
  refine ⟨G5_minRank_F2_eq_three,
          G5_minRank_card_ge_three_eq_two F3.card_ge_three,
          G5_minRank_card_ge_three_eq_two F4.card_ge_three,
          fano_znz_minRank_char_two F2.char_two,
          fano_znz_minRank_char_two F4.char_two,
          fano_znz_minRank_char_ne_two F3.char_ne_two,
          P_C6_plus_minRank_one F4,
          P_C6_alpha_minRank_two (by decide) (by decide),
          P_C6_plus_minRank_one F3,
          P_C6_alpha_minRank_two neg_one_ne_zero (neg_one_ne_one F3.char_ne_two)⟩

end Conjecture00000007178
