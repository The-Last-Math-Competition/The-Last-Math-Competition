/-
  Conjecture 00000007625 — Main Entry Point & Complete Resolution Summary

  English:
    Definition: Idempotents as projection structure.
    Conjecture: The count law of idempotent decompositions is the minimal-ideal
    count; the realization of minimality is the matrix factor; and the minimal
    realization of matrix factors is the center decomposition.
    (minimal-ideal-count idempotent decomposition)

  Chinese:
    定义：幂等元为投影结构。猜想：幂等分解的个数律为极小理想数；且极小的实现为矩阵因子；
    且矩阵因子的极小实现为中心分解。（幂等分解极小理想数）

  Verdict: FALSE (Refuted across noncommutative matrix / split Clifford
  algebras, division Clifford algebras, and non-semisimple / degenerate
  Clifford algebras; with an exact Positive Theorem characterizing the
  central block / split commutative semisimple Wedderburn-Artin regime).
-/

import Conjecture00000007625.Basic
import Conjecture00000007625.Positive
import Conjecture00000007625.MatrixCounterexample
import Conjecture00000007625.Obstructions

namespace Conjecture00000007625

/-- **End-to-End Resolution Bundle (`conjecture_00000007625_resolution`)**:
    Packages together:
    1. Positive Non-Vacuity Theorem on `F_3^(m+1)` (and `Cl_{1,0}(F_3) ≅ F_3^2`).
    2. Master Six-Way Separation on `M_2(F_3) ≅ Cl_{1,1}(F_3)` (`1, 2, 4, 6, 12, 14`),
       refuting Clause 1 under every ring-theoretic reading.
    3. Infinite Decomposition Family in `M_2(ℤ)` (no finite count `k`).
    4. Division-Algebra Obstructions `Cl_{0,1}(F_3) ≅ F_9` and `H(ℤ) = Cl_{0,2}(ℤ)`
       (not isomorphic to `M_{n+1}(F_3)` or `M_{n+1}(ℤ)` for any `n`).
    5. Non-Semisimple / Degenerate Clifford Counterexamples `F_3[ε]/(ε^2)` and
       commutative `F_3[x, y]/(x^2, xy, y^2)` (`1` idempotent block vs. `4`
       square-zero minimal ideals). -/
theorem conjecture_00000007625_resolution :
    -- (1) Positive split commutative semisimple regime F_3^(m+1) & Cl_{1,0}(F_3)
    (∀ m : Nat,
      ExactCard (IsMinimalTwoSidedIdeal (F3PowRing (m + 1))) (m + 1) ∧
      ExactCard (IsMinimalLeftIdeal (F3PowRing (m + 1))) (m + 1) ∧
      (∀ (r : Nat) (e : Fin r → F3Pow (m + 1)),
        IsPrimOrthDecomp (F3PowRing (m + 1)) r e → r = m + 1) ∧
      ExactCard (IsUnordPrimOrthDecomp (F3PowRing (m + 1))) 1) ∧
    Nonempty (RingIso Cl10F3Ring (F3PowRing 2)) ∧
    -- (2) Noncommutative matrix / split Clifford M_2(F_3) ≅ Cl_{1,1}(F_3)
    Nonempty (RingIso Cl11F3Ring Mat2F3Ring) ∧
    ExactCard (IsMinimalTwoSidedIdeal Mat2F3Ring) 1 ∧
    ExactCard (IsCentralPrimitiveIdempotent Mat2F3Ring) 1 ∧
    (∀ (r : Nat) (e : Fin r → Mat2 F3), IsPrimOrthDecomp Mat2F3Ring r e → r = 2) ∧
    ExactCard (IsMinimalLeftIdeal Mat2F3Ring) 4 ∧
    ExactCard (IsUnordPrimOrthDecomp Mat2F3Ring) 6 ∧
    ExactCard (IsPrimOrthDecomp Mat2F3Ring 2) 12 ∧
    ExactCard (IsIdempotent Mat2F3Ring) 14 ∧
    -- (3) Infinite primitive decompositions in M_2(ℤ)
    (∀ k : Nat, ¬ ExactCard (IsUnordPrimOrthDecomp Mat2IntRing) k) ∧
    -- (4) Division-algebra obstructions Cl_{0,1}(F_3) and H(ℤ) = Cl_{0,2}(ℤ)
    (∀ n : Nat, ¬ Nonempty (RingIso Cl01F3Ring (MatNRing (n + 1) F3Ring))) ∧
    (∀ n : Nat, ¬ Nonempty (RingIso QuatIntRing (MatNRing (n + 1) IntRing))) ∧
    -- (5) Degenerate / non-semisimple obstructions F_3[ε]/(ε^2) and F_3[x,y]/(x^2,xy,y^2)
    IsSquareZeroIdeal DualF3Ring dualRad ∧
    (∀ n : Nat, ¬ Nonempty (RingIso DualF3Ring (MatNRing (n + 1) F3Ring))) ∧
    (ExactCard (IsUnordPrimOrthDecomp LocalF3Ring) 1 ∧
     ExactCard (IsMinimalTwoSidedIdeal LocalF3Ring) 4) := by
  have hm := mat2_f3_master_refutation
  have hd := dualF3_obstruction_theorem
  have hl := localF3_commutative_counterexample
  refine ⟨?_, ⟨cl10_f3_iso_f3Pow2⟩, ⟨cl11_f3_iso_mat2_f3⟩,
          hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.1,
          mat2_int_infinite_unord_prim_decomps,
          cl01_f3_not_iso_any_matN_f3,
          quatInt_not_iso_any_matN_int,
          hd.2.2.1, hd.2.2.2.2,
          ⟨hl.2.2.2.2.1, hl.2.2.2.2.2.1⟩⟩
  intro m
  have hp := f3Pow_positive_theorem m
  exact ⟨hp.1, hp.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

end Conjecture00000007625
