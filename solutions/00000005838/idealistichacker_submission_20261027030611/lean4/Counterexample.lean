import BlockTheory
import Involution
import C2Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section

namespace Counterexample5838

abbrev SplitField := AlgebraicClosure (ZMod 2)

abbrev CentralizerAlgebra := MonoidAlgebra SplitField Involution5838.centralizer

theorem prime_two : Nat.Prime 2 := by decide

theorem splitting_field_characteristic : CharP SplitField 2 := inferInstance

theorem splitting_field_algebraically_closed : IsAlgClosed SplitField := inferInstance

theorem centralizer_idempotents :
    ∀ e : CentralizerAlgebra, IsIdempotentElem e → e = 0 ∨ e = 1 :=
  BlockTheory5838.idempotents_of_ringEquiv
    (Involution5838.centralizerAlgebraEquiv SplitField).toRingEquiv
    (C2Algebra5838.char2idempotent_only_zero_one (K := SplitField))

theorem centralizer_block_count : Nat.card (BlockTheory5838.Block CentralizerAlgebra) = 1 :=
  BlockTheory5838.block_count_one centralizer_idempotents

theorem centralizer_blocks_finite : Finite (BlockTheory5838.Block CentralizerAlgebra) :=
  BlockTheory5838.blocks_finite centralizer_idempotents

theorem selected_blocks_finite (P : BlockTheory5838.Block CentralizerAlgebra → Prop) :
    Finite {b : BlockTheory5838.Block CentralizerAlgebra // P b} :=
  BlockTheory5838.block_subset_finite centralizer_idempotents P

theorem any_selection_not_half_count (P : BlockTheory5838.Block CentralizerAlgebra → Prop) :
    2 * Nat.card {b : BlockTheory5838.Block CentralizerAlgebra // P b} ≠
      Nat.card (BlockTheory5838.Block CentralizerAlgebra) :=
  BlockTheory5838.no_half_count centralizer_idempotents P

theorem any_selection_not_half_rational (P : BlockTheory5838.Block CentralizerAlgebra → Prop) :
    (Nat.card {b : BlockTheory5838.Block CentralizerAlgebra // P b} : ℚ) ≠
      (Nat.card (BlockTheory5838.Block CentralizerAlgebra) : ℚ) / 2 :=
  BlockTheory5838.no_half_rational centralizer_idempotents P

theorem any_selection_not_half_real (P : BlockTheory5838.Block CentralizerAlgebra → Prop) :
    (Nat.card {b : BlockTheory5838.Block CentralizerAlgebra // P b} : ℝ) ≠
      (Nat.card (BlockTheory5838.Block CentralizerAlgebra) : ℝ) / 2 := by
  intro he
  have hmul : (2 : ℝ) * (Nat.card {b : BlockTheory5838.Block CentralizerAlgebra // P b} : ℝ) =
      (Nat.card (BlockTheory5838.Block CentralizerAlgebra) : ℝ) := by linarith
  have hn : 2 * Nat.card {b : BlockTheory5838.Block CentralizerAlgebra // P b} =
      Nat.card (BlockTheory5838.Block CentralizerAlgebra) := by exact_mod_cast hmul
  exact any_selection_not_half_count P hn

def HalfBlockClause (G : Type*) [Group G] [Finite G]
    (K : Type*) [Field K] [CharP K 2] [IsAlgClosed K]
    (selected : ∀ s : G, BlockTheory5838.Block (MonoidAlgebra K (Subgroup.centralizer {s})) → Prop) : Prop :=
  ∀ s : G, s ≠ 1 → s * s = 1 →
    (Nat.card {b : BlockTheory5838.Block (MonoidAlgebra K (Subgroup.centralizer {s})) // selected s b} : ℚ) =
      (Nat.card (BlockTheory5838.Block (MonoidAlgebra K (Subgroup.centralizer {s}))) : ℚ) / 2

theorem half_clause_false_for_every_selection
    (selected : ∀ s : Involution5838.G,
      BlockTheory5838.Block (MonoidAlgebra SplitField (Subgroup.centralizer {s})) → Prop) :
    ¬ HalfBlockClause Involution5838.G SplitField selected := by
  intro h
  have hi := h Involution5838.involution Involution5838.involution_ne_one
    Involution5838.involution_square
  exact any_selection_not_half_rational (selected Involution5838.involution) hi

end Counterexample5838
