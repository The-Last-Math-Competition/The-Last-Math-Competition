/-
  Conjecture 00000004763 — Master Formal Disproof in Core Lean 4.19.0

  Source Conjecture (English & Chinese):
    Free cumulants `κ_n` and classical cumulants `c_n` are the noncommutative and
    commutative combinatorial systems of moment functionals. Conjecture:
    (1) Their conversion is always a low-order rational combination
    (2) with coefficients given by weighted crossing pair counts;
    (3) the first two nontrivial conversion coefficients are `1` and `-1`;
    (4) the conversion matrix is invertible over the field of rational functions,
        with finite bandwidth of the inverse (finite bandwidth of the Stirling-type triangle).

  Verdict: FALSE. All four constituent claims fail; only the order-4 opposite-direction
  identities `κ_4 = c_4 + 1 * c_2^2` and `c_4 = κ_4 + (-1) * κ_2^2` hold.
-/

import Conjecture00000004763.Basic
import Conjecture00000004763.LowOrderAndCrossing
import Conjecture00000004763.UnboundedDegree
import Conjecture00000004763.InverseBandwidth

namespace Conjecture00000004763

/-- **Positive Foundation & Non-Vacuity Theorem**:
    1. Exact mutual inversion between `classicalToFree` and `freeToClassical` at all orders `n ≥ 1`.
    2. Universal low-order identities `κ_1 = c_1`, `κ_2 = c_2`, `κ_3 = c_3`, `κ_4 = c_4 + c_2^2`,
       and `c_4 = κ_4 - κ_2^2` explaining the `+1` and `-1` coefficients of opposite directions at `n = 4`.
    3. Non-vacuity of `HasFiniteLowerBandwidth` (satisfied by `matId` and `bidiagDiff`). -/
theorem conjecture_00000004763_positive_foundations :
    (∀ c n, 1 ≤ n → freeToClassical (classicalToFree c) n = c n) ∧
    (∀ κ n, 1 ≤ n → classicalToFree (freeToClassical κ) n = κ n) ∧
    (∀ c, classicalToFree c 1 = c 1 ∧ classicalToFree c 2 = c 2 ∧
          classicalToFree c 3 = c 3 ∧ classicalToFree c 4 = c 4 + c 2 * c 2) ∧
    (∀ κ, freeToClassical κ 1 = κ 1 ∧ freeToClassical κ 2 = κ 2 ∧
          freeToClassical κ 3 = κ 3 ∧ freeToClassical κ 4 = κ 4 - κ 2 * κ 2) ∧
    HasFiniteLowerBandwidth matId ∧
    HasFiniteLowerBandwidth bidiagDiff :=
  ⟨freeToClassical_classicalToFree,
   classicalToFree_freeToClassical,
   fun c => ⟨classicalToFree_one c, classicalToFree_two c,
             classicalToFree_three c, classicalToFree_four c⟩,
   fun κ => ⟨freeToClassical_one κ, freeToClassical_two κ,
             freeToClassical_three κ, freeToClassical_four κ⟩,
   bandwidth_nonvacuity.1,
   bandwidth_nonvacuity.2.1⟩

/-- **Master Refutation Theorem for Conjecture 00000004763**:
    Simultaneously refutes all four constituent claims of Conjecture 00000004763:
    1. **Not a low-order rational combination**: For EVERY degree bound `D : Nat`, both
       `classicalToFree` (along `gaussRay`) and `freeToClassical` (along `wignerRay`) exceed
       rational degree `(D, D)`.
    2. **Not determined by crossing pair counts**: On set partitions of `{1..8}`, no function
       `W(blockLengths, crossingPairCount)` can reproduce either the forward connected-crossing
       weights or (even among connected partitions) the inverse Tutte-activity weights.
    3. **First two nontrivial coefficients are NOT `1` and `-1`**: In `c ↦ κ` they are `(1, 5)`,
       and in `κ ↦ c` they are `(-1, -5)`.
    4. **Unbounded inverse bandwidth across all Stirling/Narayana/Bell/recurrence triangles**:
       `matInv stirling2`, `matInv narayana`, `matInv T_clToFr` (`= S⁻¹ N`), `matInv T_frToCl`
       (`= N⁻¹ S`), and the canonical moment-recurrence conversion matrices `T_rec_clToFr` and
       `matInv ∘ T_rec_clToFr` ALL fail to have finite lower bandwidth. -/
theorem conjecture_00000004763_disproof :
    -- (1) Refutation of low-order rational combination in both directions:
    (∀ D : Nat,
      (∃ n : Nat, 2 * D < n ∧
        ∀ P Q : Nat → Int, (∃ k, k ≤ D ∧ Q k ≠ 0) →
          ∃ t : Int, 1 ≤ t ∧ evalPolyZ D Q t ≠ 0 ∧
            classicalToFree (gaussRay t) n * evalPolyZ D Q t ≠ evalPolyZ D P t) ∧
      (∃ n : Nat, 2 * D < n ∧
        ∀ P Q : Nat → Int, (∃ k, k ≤ D ∧ Q k ≠ 0) →
          ∃ t : Int, 1 ≤ t ∧ evalPolyZ D Q t ≠ 0 ∧
            freeToClassical (wignerRay t) n * evalPolyZ D Q t ≠ evalPolyZ D P t)) ∧
    -- (2) Refutation of crossing-pair-count weight parameterization:
    ((¬ ∃ W : List Nat → Nat → Int,
        ∀ p, isSetPartitionBool 8 p = true →
          forwardPartitionWeight p = W (blockLengths p) (crossingPairCount p)) ∧
     (¬ ∃ W : List Nat → Nat → Int,
        ∀ p, isSetPartitionBool 8 p = true → isCrossingConnected p = true →
          inversePartitionWeight p = W (blockLengths p) (crossingPairCount p))) ∧
    -- (3) Refutation of first two nontrivial coefficients being `1` and `-1`:
    ((classicalToFree probe23 4 - probe23 4, classicalToFree probe23 5 - probe23 5) = (1, 5) ∧
     (1, (5 : Int)) ≠ (1, -1) ∧
     (freeToClassical probe23 4 - probe23 4, freeToClassical probe23 5 - probe23 5) = (-1, -5) ∧
     ((-1 : Int), (-5 : Int)) ≠ (1, -1)) ∧
    -- (4) Refutation of finite inverse bandwidth across all Stirling/Narayana/Bell/recurrence matrices:
    (¬ HasFiniteLowerBandwidth (matInv stirling2) ∧
     ¬ HasFiniteLowerBandwidth (matInv narayana) ∧
     ¬ HasFiniteLowerBandwidth (matInv T_clToFr) ∧
     ¬ HasFiniteLowerBandwidth (matInv T_frToCl) ∧
     ¬ HasUniformFiniteBandwidth T_rec_clToFr ∧
     ¬ HasUniformFiniteBandwidth (fun m => matInv (T_rec_clToFr m))) :=
  ⟨not_low_order_rational_combination,
   no_weight_function_of_crossing_pair_count,
   first_two_nontrivial_coeffs_not_one_and_neg_one,
   ⟨stirling2_and_inv_unbounded_bandwidth.2,
    not_finite_bandwidth_inv_narayana,
    not_finite_bandwidth_inv_T_clToFr,
    not_finite_bandwidth_inv_T_frToCl,
    not_uniform_finite_bandwidth_T_rec.1,
    not_uniform_finite_bandwidth_T_rec.2⟩⟩

end Conjecture00000004763
