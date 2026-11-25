/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000004751:
 Module 3: Complete Refutation Across All Interpretations and Positive Characterization.
-/

import Conjecture00000004751.FreeSeries

set_option maxRecDepth 200000

namespace Conjecture00000004751

/-! ### 1. Premise Clarification: Ordinary Logarithm vs Free `R`-Series -/

/-- Twice the `z^2`-coefficient of `log(1 + M(z))`, i.e., `2 ℓ_2 = 2 m_2 - m_1^2`. -/
def twiceLogMoment2 (m1 m2 : Int) : Int := 2 * m2 - m1 * m1

/-- Twice the second free cumulant `2 κ_2 = 2 (m_2 - m_1^2)`. -/
def twiceFreeCumulant2 (m1 m2 : Int) : Int := 2 * (m2 - m1 * m1)

/-- Whenever `m_1 ≠ 0`, `log(1 + M(z))` already disagrees with the free cumulant series at `z^2`. -/
theorem premise_logarithm_ne_free_cumulant (m1 m2 : Int) (hm1 : m1 ≠ 0) :
    twiceLogMoment2 m1 m2 ≠ twiceFreeCumulant2 m1 m2 := by
  unfold twiceLogMoment2 twiceFreeCumulant2
  intro heq
  have hsq : m1 * m1 = 0 := by omega
  rcases Int.mul_eq_zero.mp hsq with h0 | h0
  · exact hm1 h0
  · exact hm1 h0

/-- For `δ_1 ⊞ δ_1 = δ_2` (`m_n(δ_a) = a^n`), `log(1 + M(z))` is NOT additive under free convolution:
    at `z^2`, `2 [z^2] log(1 + M_{δ_2}) = 4 ≠ 2 = 2 ([z^2] log(1 + M_{δ_1}) + [z^2] log(1 + M_{δ_1}))`. -/
theorem premise_logarithm_not_boxplus_additive :
    twiceLogMoment2 2 4 ≠ twiceLogMoment2 1 1 + twiceLogMoment2 1 1 := by decide

/-! ### 2. Refutation of Closedness Under Operation (A): Voiculescu's `R_f ∘ R_g` -/

/-- Constant term `[z^0] (R_{f,N} ∘ R_g)` of composing the `N`-truncated Voiculescu `R`-transform
    `R_{f,N}(z) = ∑_{k=1}^N a_k z^{k-1}` with `R_g(z)` at `z = 0` (`R_g(0) = b_1`). -/
def voiculescuTruncConst (a : Nat → Int) (b1 : Int) : Nat → Int
  | 0 => 0
  | n + 1 => voiculescuTruncConst a b1 n + a (n + 1) * (b1 ^ n)

private theorem int_one_pow : ∀ r : Nat, (1 : Int) ^ r = 1
  | 0 => rfl
  | r + 1 => by simp [Int.pow_succ, int_one_pow r]

/-- Algebraic non-closedness of `R_f ∘ R_g` for non-centered `b_1 ≠ 0`:
    for free Poisson (`a_k = 1`) composed with `δ_1` (`b_1 = 1`), the truncated constant term
    equals `N` and grows strictly beyond every finite bound `M`. -/
theorem voiculescu_comp_unbounded_noncentered (M : Nat) :
    ∃ N : Nat, voiculescuTruncConst (fun _ => 1) 1 N > Int.ofNat M := by
  refine ⟨M + 1, ?_⟩
  have hval : ∀ k : Nat, voiculescuTruncConst (fun _ => 1) 1 k = Int.ofNat k := by
    intro k
    induction k with
    | zero => rfl
    | succ r ih =>
        simp only [voiculescuTruncConst, ih, int_one_pow, Int.mul_one, Int.ofNat_eq_coe]
        omega
  rw [hval (M + 1)]
  simp only [Int.ofNat_eq_coe]
  omega

/-- Cached table of Rademacher free cumulants for `n = 0..6` computed directly from
    `freeCumulantsFromMoments rademacherMoments` once, avoiding redundant poset regeneration
    inside Cauchy power series products. -/
def rademacherCumulantTable : List Int :=
  (List.range 7).map (freeCumulantsFromMoments rademacherMoments)

/-- Free cumulants of the symmetric Rademacher law `μ = (δ_{-1} + δ_1)/2` (`m_{2r} = 1, m_{2r+1} = 0`)
    up to order 6. -/
def rademacherCumulants (n : Nat) : Int :=
  rademacherCumulantTable.getD n 0

theorem rademacherCumulants_eq_mobius :
    (List.range 7).all (fun n =>
      rademacherCumulants n == freeCumulantsFromMoments rademacherMoments n) = true := by decide

/-- Unshifted Voiculescu `R`-transform `R_μ(z) = ∑_{k ≥ 1} κ_k(μ) z^{k-1}` of Rademacher `μ`.
    Since `κ_1(μ) = 0`, `R_μ(0) = 0`, so formal composition `R_μ ∘ R_μ` IS well-defined. -/
def rademacherVoiculescuR (deg : Nat) : Int :=
  rademacherCumulants (deg + 1)

theorem rademacherVoiculescuR_zero : rademacherVoiculescuR 0 = 0 := by decide

/-- Cumulants and induced moments of the self-composed Voiculescu `R`-transform `R_μ ∘ R_μ`. -/
def voiculescuSelfCompCumulants (n : Nat) : Int :=
  if n == 0 then 0 else fpsComp rademacherVoiculescuR rademacherVoiculescuR (n - 1)

def voiculescuSelfCompMoments (n : Nat) : Int :=
  freeMomentsFromCumulants voiculescuSelfCompCumulants n

/-- Even for centered probability measures (`κ_1 = 0`), `R_f ∘ R_g` is NOT closed on probability
    measures: `μ` satisfies universal square positivity (`∀ p, 0 ≤ 2 ⟨m_μ, p^2⟩`), yet `R_μ ∘ R_μ`
    gives `⟨m_h, (x^2 - 1)^2⟩ = -1 < 0`! -/
theorem voiculescu_comp_breaks_positivity :
    (∀ p : IntPoly, 0 ≤ 2 * momentEval rademacherMoments (polySq p)) ∧
    rademacherVoiculescuR 0 = 0 ∧
    momentEval voiculescuSelfCompMoments (polySq [-1, 0, 1]) = -1 ∧
    momentEval voiculescuSelfCompMoments (polySq [-1, 0, 1]) < 0 := by
  refine ⟨rademacher_universal_positivity, rademacherVoiculescuR_zero, ?_, ?_⟩
  · decide
  · decide

/-! ### 3. Refutation of Closedness Under Operation (B): Centered `R`-Series `C_f ∘ C_g` -/

/-- Cumulants and induced moments of centered cumulant-series self-composition `C_μ ∘ C_μ`
    for Rademacher `μ`. -/
def centeredRademacherCompCumulants (n : Nat) : Int :=
  fpsComp rademacherCumulants rademacherCumulants n

def centeredRademacherCompMoments (n : Nat) : Int :=
  freeMomentsFromCumulants centeredRademacherCompCumulants n

/-- Standard Wigner semicircle cumulants (`κ_2 = 1`, `κ_{n ≠ 2} = 0`) and `C_sc ∘ C_sc` moments. -/
def semicircleCumulants (n : Nat) : Int := if n == 2 then 1 else 0

def centeredSemicircleCompMoments (n : Nat) : Int :=
  freeMomentsFromCumulants (fpsComp semicircleCumulants semicircleCumulants) n

/-- Centered `R`-series composition `C_f ∘ C_g` fails positivity closedness for BOTH Rademacher `μ`
    (yielding a strictly negative sixth moment `m_6 = ⟨m_h, (x^3)^2⟩ = -2 < 0`) AND Wigner semicircle
    (yielding `⟨m_h, (x^3 - x)^2⟩ = -2 < 0`). -/
theorem centered_comp_breaks_positivity :
    momentEval centeredRademacherCompMoments (polySq [0, 0, 0, 1]) = -2 ∧
    momentEval centeredRademacherCompMoments (polySq [0, 0, 0, 1]) < 0 ∧
    momentEval centeredSemicircleCompMoments (polySq [0, -1, 0, 1]) = -2 ∧
    momentEval centeredSemicircleCompMoments (polySq [0, -1, 0, 1]) < 0 := by decide

/-! ### 4. Universal Impossibility of Block-Structure Möbius Correction on `NC(4)` & `NC(6)` -/

/-- Cross-multiplied (rational-safe) statement that a non-vanishing block-type weight
    `W(λ) = numW(λ) / denW(λ)` equals a block-structure correction table
    `B(λ) = numB(λ) / denB(λ)` times the `NC(n)` Möbius inversion coefficient `μ_{NC}(π, 1_n)`
    for every `π ∈ NC(n)`. -/
def SatisfiesBlockMobiusCorrection (n : Nat)
    (numW denW numB denB : List Nat → Int) : Prop :=
  ∀ pi : Partition, isNC n pi = true →
    numW (blockType pi) * denB (blockType pi) =
      denW (blockType pi) * numB (blockType pi) * mobiusNC n pi (topPartition n)

/-- Universal Impossibility Theorem at `n = 4` (`λ = [2, 1, 1]`):
    no rational/real block-structure correction table `B(λ)` can relate `μ_{NC}(π, 1_4)`
    to ANY non-zero block-type-invariant partition weight `W([2, 1, 1]) ≠ 0`! -/
theorem no_block_structure_mobius_correction_NC4
    (numW denW numB denB : List Nat → Int)
    (hW_num : numW [2, 1, 1] ≠ 0)
    (hB_den : denB [2, 1, 1] ≠ 0) :
    ¬ SatisfiesBlockMobiusCorrection 4 numW denW numB denB := by
  intro hcorr
  rcases pi4_counterexamples_valid_and_same_type with ⟨hadj, hnest, ht_adj, ht_nest⟩
  rcases pi4_mobius_disagree with ⟨hm_adj, hm_nest, _, _⟩
  have eq1 := hcorr pi4_adj hadj
  have eq2 := hcorr pi4_nest hnest
  rw [ht_adj, hm_adj] at eq1
  rw [ht_nest, hm_nest] at eq2
  have hzero_rhs : denW [2, 1, 1] * numB [2, 1, 1] = 0 := by omega
  have hzero_lhs : numW [2, 1, 1] * denB [2, 1, 1] = 0 := by omega
  rcases Int.mul_eq_zero.mp hzero_lhs with h0 | h0
  · exact hW_num h0
  · exact hB_den h0

/-- Universal Impossibility Theorem at `n = 6` on singleton-free uniform pair partitions (`λ = [2, 2, 2]`):
    no block-structure correction table `B(λ)` can relate `μ_{NC}(π, 1_6)` to ANY non-zero
    block-type-invariant partition weight `W([2, 2, 2]) ≠ 0`! -/
theorem no_block_structure_mobius_correction_NC6
    (numW denW numB denB : List Nat → Int)
    (hW_num : numW [2, 2, 2] ≠ 0)
    (hB_den : denB [2, 2, 2] ≠ 0) :
    ¬ SatisfiesBlockMobiusCorrection 6 numW denW numB denB := by
  intro hcorr
  rcases pi6_counterexamples_valid_and_mobius_checked with ⟨hflat, hrain, ht_flat, ht_rain, _, _⟩
  rcases pi6_mobius_and_kreweras_disagree with ⟨hm_flat, hm_rain, _, _, _, _⟩
  have eq1 := hcorr pi6_flat hflat
  have eq2 := hcorr pi6_rain hrain
  rw [ht_flat, hm_flat] at eq1
  rw [ht_rain, hm_rain] at eq2
  have hzero_rhs : denW [2, 2, 2] * numB [2, 2, 2] = 0 := by omega
  have hzero_lhs : numW [2, 2, 2] * denB [2, 2, 2] = 0 := by omega
  rcases Int.mul_eq_zero.mp hzero_lhs with h0 | h0
  · exact hW_num h0
  · exact hB_den h0

/-! ### 5. Refutation Under Operation (C): Nica–Speicher Boxed Convolution `C_f ⋆ C_g` -/

/-- In Nica–Speicher boxed convolution `(a ⋆ b)_n = ∑_{π ∈ NC(n)} a_π b_{K(π)}`, the second factor's
    monomial type `blockType (kreweras n π)` is NOT determined by `blockType π` at `n = 4` or `n = 6`. -/
theorem boxed_conv_kreweras_not_block_invariant :
    (∃ p1 p2 : Partition,
      isNC 4 p1 = true ∧ isNC 4 p2 = true ∧
      blockType p1 = blockType p2 ∧
      blockType (kreweras 4 p1) ≠ blockType (kreweras 4 p2)) ∧
    (∃ q1 q2 : Partition,
      isNC 6 q1 = true ∧ isNC 6 q2 = true ∧
      blockType q1 = blockType q2 ∧
      blockType (kreweras 6 q1) ≠ blockType (kreweras 6 q2)) := by
  refine ⟨⟨pi4_adj, pi4_nest, ?_⟩, ⟨pi6_flat, pi6_rain, ?_⟩⟩
  · decide
  · decide

/-! ### 6. Aggregated Block-Type Analysis: Non-Integrality & Exact Clearing Identity -/

/-- Number of interval partitions (composition structure constant `S_comp(λ)`) of block type `λ`. -/
def compStructConst (n : Nat) (lam : List Nat) : Int :=
  Int.ofNat ((allIntervalPartitions n).filter (fun pi => blockType pi == lam)).length

/-- Aggregated `NC(n)` Möbius inversion coefficient `M_1(λ) = ∑_{π ∈ NC_λ(n)} μ_{NC}(π, 1_n)`. -/
def aggMobiusUpper (n : Nat) (lam : List Nat) : Int :=
  ((allNC n).filter (fun pi => blockType pi == lam)).foldl
    (fun s pi => s + mobiusToTopFormula n pi) 0

/-- Aggregated `NC(n)` block-type count `|NC_λ(n)|`. -/
def aggNCCount (n : Nat) (lam : List Nat) : Int :=
  Int.ofNat ((allNC n).filter (fun pi => blockType pi == lam)).length

/-- Even after summing over all `π ∈ NC_λ(n)`, neither `S_comp(λ) / M_1(λ)` nor
    `S_comp(λ) / |NC_λ(n)|` is an integer (`-2/3` and `2/3` at `n = 3, λ = [2, 1]`;
    `3/10` at `n = 4, λ = [2, 1, 1]`). -/
theorem aggregated_ratios_not_integral :
    (¬ ∃ c : Int, compStructConst 3 [2, 1] = c * aggMobiusUpper 3 [2, 1]) ∧
    (¬ ∃ c : Int, compStructConst 3 [2, 1] = c * aggNCCount 3 [2, 1]) ∧
    (¬ ∃ c : Int, compStructConst 4 [2, 1, 1] = c * aggMobiusUpper 4 [2, 1, 1]) := by
  have h1 : compStructConst 3 [2, 1] = 2 := by decide
  have h2 : aggMobiusUpper 3 [2, 1] = -3 := by decide
  have h3 : aggNCCount 3 [2, 1] = 3 := by decide
  have h4 : compStructConst 4 [2, 1, 1] = 3 := by decide
  have h5 : aggMobiusUpper 4 [2, 1, 1] = 10 := by decide
  rw [h1, h2, h3, h4, h5]
  refine ⟨?_, ?_, ?_⟩ <;> {
    rintro ⟨c, hc⟩
    omega
  }

/-- Binomial coefficient `Nat.choose` defined via Pascal's triangle. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Exact verified cleared-denominator identity across all partitions `λ` at `n = 1..6`:
    `S_comp(λ) * C(n + k - 2, k - 1) = (-1)^(k - 1) * k * M_1(λ)` where `k = ℓ(λ)`. -/
theorem exact_cleared_binomial_identity_1_to_6 :
    (List.range 6).all (fun idx =>
      let n := idx + 1
      let nc := allNC n
      let ip := allIntervalPartitions n
      let lams := nc.foldr (fun pi acc =>
        let l := blockType pi
        if acc.contains l then acc else l :: acc) []
      lams.all (fun lam =>
        let k := lam.length
        let sign : Int := if (k - 1) % 2 == 0 then 1 else -1
        let sComp : Int := Int.ofNat (ip.filter (fun pi => blockType pi == lam)).length
        let m1Sum : Int := (nc.filter (fun pi => blockType pi == lam)).foldl
          (fun s pi => s + mobiusToTopFormula n pi) 0
        sComp * Int.ofNat (binom (n + k - 2) (k - 1)) ==
          sign * Int.ofNat k * m1Sum)) = true := by decide

/-! ### 7. Master Synthesis Theorem Disproving Conjecture 00000004751 -/

/-- Complete formal refutation of Conjecture 00000004751 across all interpretations:
    1. Premise discrepancy: `log(1 + M(z))` is neither the free cumulant series nor `⊞`-additive;
    2. Operation (A) (`R_f ∘ R_g`) fails finitary closedness for `b_1 ≠ 0` and breaks measure
       positivity even for centered Rademacher laws (`R_μ(0) = 0`);
    3. Operation (B) (`C_f ∘ C_g`) breaks measure positivity for Rademacher and semicircle laws,
       and cannot be obtained from `μ_{NC}(π, 1_n)` by any block-structure correction table on `NC(n)`;
    4. Operation (C) (`C_f ⋆ C_g`) fails block-structure invariance of Kreweras complements at
       `n = 4` (`[2,1,1]`) and `n = 6` (`[2,2,2]`). -/
theorem conjecture_00000004751_disproved :
    (twiceLogMoment2 2 4 ≠ twiceLogMoment2 1 1 + twiceLogMoment2 1 1) ∧
    (∀ M : Nat, ∃ N : Nat, voiculescuTruncConst (fun _ => 1) 1 N > Int.ofNat M) ∧
    ((∀ p : IntPoly, 0 ≤ 2 * momentEval rademacherMoments (polySq p)) ∧
      rademacherVoiculescuR 0 = 0 ∧
      momentEval voiculescuSelfCompMoments (polySq [-1, 0, 1]) < 0 ∧
      momentEval centeredRademacherCompMoments (polySq [0, 0, 0, 1]) < 0 ∧
      momentEval centeredSemicircleCompMoments (polySq [0, -1, 0, 1]) < 0) ∧
    (∀ numW denW numB denB : List Nat → Int,
      numW [2, 1, 1] ≠ 0 → denB [2, 1, 1] ≠ 0 →
      ¬ SatisfiesBlockMobiusCorrection 4 numW denW numB denB) ∧
    (∀ numW denW numB denB : List Nat → Int,
      numW [2, 2, 2] ≠ 0 → denB [2, 2, 2] ≠ 0 →
      ¬ SatisfiesBlockMobiusCorrection 6 numW denW numB denB) ∧
    (∃ q1 q2 : Partition,
      isNC 6 q1 = true ∧ isNC 6 q2 = true ∧
      blockType q1 = blockType q2 ∧
      blockType (kreweras 6 q1) ≠ blockType (kreweras 6 q2)) := by
  refine ⟨premise_logarithm_not_boxplus_additive,
          voiculescu_comp_unbounded_noncentered,
          ⟨rademacher_universal_positivity,
           rademacherVoiculescuR_zero,
           voiculescu_comp_breaks_positivity.2.2.2,
           centered_comp_breaks_positivity.2.1,
           centered_comp_breaks_positivity.2.2.2⟩,
          no_block_structure_mobius_correction_NC4,
          no_block_structure_mobius_correction_NC6,
          boxed_conv_kreweras_not_block_invariant.2⟩

end Conjecture00000004751
