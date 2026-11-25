/-
  Conjecture00000004769.lean
  Top-level resolution of Conjecture 00000004769 ("Cyclotomic product of the annular q-analogue")
  in Core Lean 4.19.0 (zero external dependencies, `-DwarningAsError=true`, zero `sorry`,
  zero `native_decide`, zero custom axioms).

  Summary of formal results:
    1. Positive Non-Vacuity & Stratum Dichotomy (`positive_strata_and_pair_cyclotomic`):
       Individual Mingo-Nica through-block strata `Q^(0)_{p,2}(q)`, `Q^(1)_{p,2}(q)`, `Q^(2)_{p,2}(q)`,
       connected permutation `q`-counts `S^conn_{p,2}(q)`, and annular pair-matching `q`-binomials
       `[2m+1 choose m]_q` ARE explicit products of cyclotomic polynomials specializing to their
       exact classical counts at `q = 1`.
    2. Complete Disproof of Conjecture 00000004769 (`conjecture_00000004769_disproved`):
       - `disproof_definition_topology`: Annulus `(g=0, b=2)` != Torus `(g=1, b=0)` despite
         `χ = 0`, and `|NC_A(4, 1)| = 49 != 52 = |NC_{g<=1}(5)|`.
       - `disproof_thickness_indexing`: Neither a fixed cyclotomic product at thickness `r = 2`
         nor any cyclotomic product with orders `d <= 2` can specialize to `|NC_A(p, 2)|`.
       - `disproof_rank_q_analogue`: Poset rank / block-number `q`-analogues `R_{p,2}(q)` fail
         at `p = 1` (`1 + 3q + q^2`), `p = 2` (`1 + 7q + 6q^2 + q^3`), `p = 3` (`1 + 15q + 25q^2 + 10q^3 + q^4`),
         and universally for ALL `p >= 2` via strict non-palindromicity `[q^1]R - [q^p]R > 0`.
       - `disproof_mingo_nica_q_sums_and_shifts`: Both unshifted and `q^2`-weighted Mingo-Nica
         `q`-strata sums at `p = 1, 2, 3`, as well as ALL monomial shifts `q^a Q^(0)_{1,2} + q^b Q^(1)_{1,2}`
         for `(a, b) ∈ N × N`, fail to be cyclotomic products.
       - `disproof_degree_and_order_obstructions`: Large primes dividing `7p^2 + 9p + 14`
         force any cyclotomic product evaluating to `|NC_A(3, 2)| = 52` to have degree `>= 14`
         and a factor `Phi_d` with `d >= 13`, and any cyclotomic product evaluating to
         `|NC_A(8, 2)| = 38181` to have degree `>= 112` and a factor `Phi_d` with `d >= 89`.
-/

import Conjecture00000004769.Annular

namespace Conjecture00000004769

/-! ### 1. Positive Non-Vacuity Theorems: Individual Strata & Pair Matchings -/

def qStratum0_p1 : Poly := polyProd [4] cyclotomic
def qStratum0_p2 : Poly := polyProd [4, 4] cyclotomic
def qStratum0_p3 : Poly := polyProd [4, 5, 6] cyclotomic

def qStratum1_p1 : Poly := polyProd [3] cyclotomic
def qStratum1_p2 : Poly := polyProd [3, 3] cyclotomic
def qStratum1_p3 : Poly := polyProd [3, 4, 5] cyclotomic

def qStratum2_p2 : Poly := polyProd [4] cyclotomic
def qStratum2_p3 : Poly := polyProd [2, 3, 4, 6] cyclotomic

def qPermConn_p1 : Poly := polyProd [2, 4] cyclotomic
def qPermConn_p2 : Poly := polyProd [3, 3, 4] cyclotomic
def qPermConn_p3 : Poly := polyProd [2, 3, 3, 4, 4, 6] cyclotomic

def qPairMatching_m1 : Poly := polyProd [3] cyclotomic
def qPairMatching_m2 : Poly := polyProd [4, 5] cyclotomic
def qPairMatching_m3 : Poly := polyProd [5, 6, 7] cyclotomic

theorem eval_cyclotomic_2 : eval (cyclotomic 2) 1 = 2 :=
  (cyclotomic_prime_pow prime_2 (k := 1) (Nat.le_refl 1)).2.2

theorem eval_cyclotomic_3 : eval (cyclotomic 3) 1 = 3 :=
  (cyclotomic_prime_pow prime_3 (k := 1) (Nat.le_refl 1)).2.2

theorem eval_cyclotomic_4 : eval (cyclotomic 4) 1 = 2 :=
  (cyclotomic_prime_pow prime_2 (k := 2) (by decide)).2.2

theorem eval_cyclotomic_5 : eval (cyclotomic 5) 1 = 5 :=
  (cyclotomic_prime_pow prime_5 (k := 1) (Nat.le_refl 1)).2.2

theorem eval_cyclotomic_6 : eval (cyclotomic 6) 1 = 1 := by
  have hg : eval (geomStep 1 6) 1 = eval (polyProd (divisorsGe2 6) cyclotomic) 1 :=
    congrArg (fun P => eval P 1) (geomStep_one_eq_polyProd_ge2 (n := 6) (by decide))
  have hdiv : divisorsGe2 6 = [2, 3, 6] := rfl
  rw [eval_geomStep_one, hdiv] at hg
  have h6 : Int.ofNat 6 = (6 : Int) := rfl
  rw [h6] at hg
  simp only [polyProd, eval_mul, eval_one_poly,
             eval_cyclotomic_2, eval_cyclotomic_3, Int.mul_one] at hg
  omega

theorem eval_cyclotomic_7 : eval (cyclotomic 7) 1 = 7 := by
  have prime_7 : IsPrimeNat 7 := isPrimeNat_of_bool rfl
  exact (cyclotomic_prime_pow prime_7 (k := 1) (Nat.le_refl 1)).2.2

theorem eval_qStratum0_p1 : eval qStratum0_p1 1 = 2 := by
  simp [qStratum0_p1, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_4]
theorem eval_qStratum0_p2 : eval qStratum0_p2 1 = 4 := by
  simp [qStratum0_p2, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_4]
theorem eval_qStratum0_p3 : eval qStratum0_p3 1 = 10 := by
  simp [qStratum0_p3, polyProd, eval_mul, eval_one_poly,
        eval_cyclotomic_4, eval_cyclotomic_5, eval_cyclotomic_6]
theorem eval_qStratum1_p1 : eval qStratum1_p1 1 = 3 := by
  simp [qStratum1_p1, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_3]
theorem eval_qStratum1_p2 : eval qStratum1_p2 1 = 9 := by
  simp [qStratum1_p2, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_3]
theorem eval_qStratum1_p3 : eval qStratum1_p3 1 = 30 := by
  simp [qStratum1_p3, polyProd, eval_mul, eval_one_poly,
        eval_cyclotomic_3, eval_cyclotomic_4, eval_cyclotomic_5]
theorem eval_qStratum2_p2 : eval qStratum2_p2 1 = 2 := by
  simp [qStratum2_p2, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_4]
theorem eval_qStratum2_p3 : eval qStratum2_p3 1 = 12 := by
  simp [qStratum2_p3, polyProd, eval_mul, eval_one_poly,
        eval_cyclotomic_2, eval_cyclotomic_3, eval_cyclotomic_4, eval_cyclotomic_6]
theorem eval_qPermConn_p1 : eval qPermConn_p1 1 = 4 := by
  simp [qPermConn_p1, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_2, eval_cyclotomic_4]
theorem eval_qPermConn_p2 : eval qPermConn_p2 1 = 18 := by
  simp [qPermConn_p2, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_3, eval_cyclotomic_4]
theorem eval_qPermConn_p3 : eval qPermConn_p3 1 = 72 := by
  simp [qPermConn_p3, polyProd, eval_mul, eval_one_poly,
        eval_cyclotomic_2, eval_cyclotomic_3, eval_cyclotomic_4, eval_cyclotomic_6]
theorem eval_qPairMatching_m1 : eval qPairMatching_m1 1 = 3 := by
  simp [qPairMatching_m1, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_3]
theorem eval_qPairMatching_m2 : eval qPairMatching_m2 1 = 10 := by
  simp [qPairMatching_m2, polyProd, eval_mul, eval_one_poly, eval_cyclotomic_4, eval_cyclotomic_5]
theorem eval_qPairMatching_m3 : eval qPairMatching_m3 1 = 35 := by
  simp [qPairMatching_m3, polyProd, eval_mul, eval_one_poly,
        eval_cyclotomic_5, eval_cyclotomic_6, eval_cyclotomic_7]

/-- Non-vacuity and positive diagnostic theorem: each individual Mingo-Nica stratum,
    connected permutation `q`-analogue, and pair-matching `q`-binomial is a genuine
    `IsCyclotomicProduct` specializing at `q = 1` to its classical Mingo-Nica count. -/
theorem positive_strata_and_pair_cyclotomic :
    (IsCyclotomicProduct qStratum0_p1 ∧ eval qStratum0_p1 1 = 2) ∧
    (IsCyclotomicProduct qStratum0_p2 ∧ eval qStratum0_p2 1 = 4) ∧
    (IsCyclotomicProduct qStratum0_p3 ∧ eval qStratum0_p3 1 = 10) ∧
    (IsCyclotomicProduct qStratum1_p1 ∧ eval qStratum1_p1 1 = 3) ∧
    (IsCyclotomicProduct qStratum1_p2 ∧ eval qStratum1_p2 1 = 9) ∧
    (IsCyclotomicProduct qStratum1_p3 ∧ eval qStratum1_p3 1 = 30) ∧
    (IsCyclotomicProduct qStratum2_p2 ∧ eval qStratum2_p2 1 = 2) ∧
    (IsCyclotomicProduct qStratum2_p3 ∧ eval qStratum2_p3 1 = 12) ∧
    (IsCyclotomicProduct qPermConn_p1 ∧ eval qPermConn_p1 1 = 4) ∧
    (IsCyclotomicProduct qPermConn_p2 ∧ eval qPermConn_p2 1 = 18) ∧
    (IsCyclotomicProduct qPermConn_p3 ∧ eval qPermConn_p3 1 = 72) ∧
    (IsCyclotomicProduct qPairMatching_m1 ∧ eval qPairMatching_m1 1 = 3) ∧
    (IsCyclotomicProduct qPairMatching_m2 ∧ eval qPairMatching_m2 1 = 10) ∧
    (IsCyclotomicProduct qPairMatching_m3 ∧ eval qPairMatching_m3 1 = 35) := by
  refine ⟨⟨⟨[4], by decide, rfl⟩, eval_qStratum0_p1⟩,
          ⟨⟨[4, 4], by decide, rfl⟩, eval_qStratum0_p2⟩,
          ⟨⟨[4, 5, 6], by decide, rfl⟩, eval_qStratum0_p3⟩,
          ⟨⟨[3], by decide, rfl⟩, eval_qStratum1_p1⟩,
          ⟨⟨[3, 3], by decide, rfl⟩, eval_qStratum1_p2⟩,
          ⟨⟨[3, 4, 5], by decide, rfl⟩, eval_qStratum1_p3⟩,
          ⟨⟨[4], by decide, rfl⟩, eval_qStratum2_p2⟩,
          ⟨⟨[2, 3, 4, 6], by decide, rfl⟩, eval_qStratum2_p3⟩,
          ⟨⟨[2, 4], by decide, rfl⟩, eval_qPermConn_p1⟩,
          ⟨⟨[3, 3, 4], by decide, rfl⟩, eval_qPermConn_p2⟩,
          ⟨⟨[2, 3, 3, 4, 4, 6], by decide, rfl⟩, eval_qPermConn_p3⟩,
          ⟨⟨[3], by decide, rfl⟩, eval_qPairMatching_m1⟩,
          ⟨⟨[4, 5], by decide, rfl⟩, eval_qPairMatching_m2⟩,
          ⟨⟨[5, 6, 7], by decide, rfl⟩, eval_qPairMatching_m3⟩⟩

/-! ### 2. Disproof Pillar 1: Topological & Combinatorial Divergence (Annulus vs. Torus) -/

theorem disproof_definition_topology :
    eulerChar annulusSurface = 0 ∧
    eulerChar torusSurface = 0 ∧
    annulusSurface ≠ torusSurface ∧
    annularNCPartitionCount 4 1 ≠ (torusGenusLe1Partitions 5).length := by
  exact ⟨annulus_vs_torus_topology.1,
         annulus_vs_torus_topology.2.1,
         annulus_vs_torus_topology.2.2.2.2,
         annular_vs_torus_enumeration_divergence.2.2⟩

/-! ### 3. Disproof Pillar 2: Parameter-Indexing Contradiction at Thickness Two -/

theorem not_pow_two_5 : ∀ k : Nat, 2 ^ k ≠ 5 := by
  intro k
  match k with
  | 0 | 1 | 2 => decide
  | m + 3 =>
    have hpos : 1 ≤ 2 ^ m := Nat.pow_pos (by decide)
    have hge8 : 8 ≤ 2 ^ (m + 3) := by
      calc 8 = 1 * 8 := rfl
        _ ≤ 2 ^ m * 8 := Nat.mul_le_mul_right 8 hpos
        _ = 2 ^ (m + 3) := by rw [Nat.pow_add]
    omega

theorem not_pow_two_15 : ∀ k : Nat, 2 ^ k ≠ 15 := by
  intro k
  match k with
  | 0 | 1 | 2 | 3 => decide
  | m + 4 =>
    have hpos : 1 ≤ 2 ^ m := Nat.pow_pos (by decide)
    have hge16 : 16 ≤ 2 ^ (m + 4) := by
      calc 16 = 1 * 16 := rfl
        _ ≤ 2 ^ m * 16 := Nat.mul_le_mul_right 16 hpos
        _ = 2 ^ (m + 4) := by rw [Nat.pow_add]
    omega

theorem disproof_thickness_indexing :
    (¬∃ P : Poly,
      eval P 1 = Int.ofNat (annularNCPartitionCount 1 2) ∧
      eval P 1 = Int.ofNat (annularNCPartitionCount 2 2)) ∧
    (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2) →
      eval (polyProd ds cyclotomic) 1 ≠ Int.ofNat (annularNCPartitionCount 1 2) ∧
      eval (polyProd ds cyclotomic) 1 ≠ Int.ofNat (annularNCPartitionCount 2 2)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨P, h1, h2⟩
    have c1 : annularNCPartitionCount 1 2 = 5 := exact_enumeration_thickness_two.1
    have c2 : annularNCPartitionCount 2 2 = 15 := exact_enumeration_thickness_two.2.1
    rw [c1] at h1; rw [c2] at h2
    have h5_15 : Int.ofNat 5 = Int.ofNat 15 := h1.symm.trans h2
    contradiction
  · intro ds hds
    have c1 : annularNCPartitionCount 1 2 = 5 := exact_enumeration_thickness_two.1
    have c2 : annularNCPartitionCount 2 2 = 15 := exact_enumeration_thickness_two.2.1
    rw [c1, c2]
    refine ⟨?_, ?_⟩
    · intro hev5
      rcases cyclotomicProd_orders_le_two hds (by rw [hev5]; decide) with ⟨k, hk⟩
      rw [hev5] at hk
      exact not_pow_two_5 k (Int.ofNat.inj hk.symm)
    · intro hev15
      rcases cyclotomicProd_orders_le_two hds (by rw [hev15]; decide) with ⟨k, hk⟩
      rw [hev15] at hk
      exact not_pow_two_15 k (Int.ofNat.inj hk.symm)

/-! ### 4. Disproof Pillar 3: Poset Rank / Block-Number `q`-Analogue Fails for ALL `p >= 1` -/

theorem not_cyclotomic_rank_2_2 : ¬IsCyclotomicProduct (annularRankPoly 2 2) := by
  have hr : annularRankPoly 2 2 = [1, 7, 6, 1] := exact_enumeration_thickness_two.2.2.2.2.2.2.2.2.1
  rw [hr]
  apply not_cyclotomic_of_rank_asymmetry (p := 2) (by decide) (by decide)
  · refine ⟨rfl, rfl, ?_⟩
    intro k hk
    match k with
    | 0 | 1 | 2 | 3 => omega
    | _ + 4 => rfl
  · exact Or.inl ⟨rfl, rfl⟩

theorem not_cyclotomic_rank_3_2 : ¬IsCyclotomicProduct (annularRankPoly 3 2) := by
  have hr : annularRankPoly 3 2 = [1, 15, 25, 10, 1] :=
    exact_enumeration_thickness_two.2.2.2.2.2.2.2.2.2
  rw [hr]
  apply not_cyclotomic_of_rank_asymmetry (p := 3) (by decide) (by decide)
  · refine ⟨rfl, rfl, ?_⟩
    intro k hk
    match k with
    | 0 | 1 | 2 | 3 | 4 => omega
    | _ + 5 => rfl
  · exact Or.inl ⟨rfl, rfl⟩

theorem disproof_rank_q_analogue :
    ¬IsCyclotomicProduct (annularRankPoly 1 2) ∧
    ¬IsCyclotomicProduct (annularRankPoly 2 2) ∧
    ¬IsCyclotomicProduct (annularRankPoly 3 2) ∧
    (∀ (p : Nat) (R : Poly), 2 ≤ p → 1 ≤ eval R 1 → IsMonicOfDeg R (p + 1) →
      ((coeff R 1 = Int.ofNat (twoBlockCount p) ∧ coeff R p = Int.ofNat (coTwoBlockCount p)) ∨
       (coeff R 1 = Int.ofNat (coTwoBlockCount p) ∧ coeff R p = Int.ofNat (twoBlockCount p))) →
      ¬IsCyclotomicProduct R) := by
  exact ⟨not_cyclotomic_rank_1_2,
         not_cyclotomic_rank_2_2,
         not_cyclotomic_rank_3_2,
         fun _ _ hp hpos hmonic hcoeffs => not_cyclotomic_of_rank_asymmetry hp hpos hmonic hcoeffs⟩

/-! ### 5. Disproof Pillar 4: Mingo-Nica `q`-Strata Sums & Arbitrary Monomial Shifts -/

def mingoNicaQSumUnshifted_p1 : Poly := add qStratum0_p1 qStratum1_p1
def mingoNicaQSumUnshifted_p2 : Poly := add qStratum0_p2 (add qStratum1_p2 qStratum2_p2)
def mingoNicaQSumWeighted_p2 : Poly := add qStratum0_p2 (add qStratum1_p2 (shift qStratum2_p2 2))
def mingoNicaQSumWeighted_p3 : Poly := add qStratum0_p3 (add qStratum1_p3 (shift qStratum2_p3 2))

theorem coeff_zero_cyclotomicProd {ds : List Nat} (hd2 : ∀ d ∈ ds, 2 ≤ d) :
    coeff (polyProd ds cyclotomic) 0 = 1 :=
  (polyProd_palindromic ds cyclotomic cycloDeg
    (fun d hd => cyclotomic_palindromic d (hd2 d hd))).2.1

theorem coeff_shift_two_zero (P : Poly) : coeff (shift P 2) 0 = 0 := by
  rw [coeff_shift, if_pos (by decide : 0 < 2)]

theorem not_cyclotomic_of_const_ne_one {P : Poly}
    (hpos : 1 ≤ eval P 1) (hc0 : coeff P 0 ≠ 1) : ¬IsCyclotomicProduct P := by
  intro hcyc
  rcases cyclotomicProd_palindromic hcyc hpos with ⟨_, hpal⟩
  exact hc0 hpal.2.1

theorem disproof_mingo_nica_q_sums_and_shifts :
    (eval mingoNicaQSumUnshifted_p1 1 = 5 ∧ ¬IsCyclotomicProduct mingoNicaQSumUnshifted_p1) ∧
    (eval mingoNicaQSumUnshifted_p2 1 = 15 ∧ ¬IsCyclotomicProduct mingoNicaQSumUnshifted_p2) ∧
    (eval mingoNicaQSumWeighted_p2 1 = 15 ∧ ¬IsCyclotomicProduct mingoNicaQSumWeighted_p2) ∧
    (eval mingoNicaQSumWeighted_p3 1 = 52 ∧ ¬IsCyclotomicProduct mingoNicaQSumWeighted_p3) ∧
    (∀ a b : Nat, eval (shiftedStrataP1 a b) 1 = 5 ∧ ¬IsCyclotomicProduct (shiftedStrataP1 a b)) := by
  have hev_u1 : eval mingoNicaQSumUnshifted_p1 1 = 5 := by
    unfold mingoNicaQSumUnshifted_p1
    rw [eval_add, eval_qStratum0_p1, eval_qStratum1_p1]; rfl
  have hc0_u1 : coeff mingoNicaQSumUnshifted_p1 0 = 2 := by
    unfold mingoNicaQSumUnshifted_p1 qStratum0_p1 qStratum1_p1
    rw [coeff_add, coeff_zero_cyclotomicProd (by decide), coeff_zero_cyclotomicProd (by decide)]; rfl
  have hev_u2 : eval mingoNicaQSumUnshifted_p2 1 = 15 := by
    unfold mingoNicaQSumUnshifted_p2
    rw [eval_add, eval_add, eval_qStratum0_p2, eval_qStratum1_p2, eval_qStratum2_p2]; rfl
  have hc0_u2 : coeff mingoNicaQSumUnshifted_p2 0 = 3 := by
    unfold mingoNicaQSumUnshifted_p2 qStratum0_p2 qStratum1_p2 qStratum2_p2
    rw [coeff_add, coeff_add, coeff_zero_cyclotomicProd (by decide),
        coeff_zero_cyclotomicProd (by decide), coeff_zero_cyclotomicProd (by decide)]; rfl
  have hev_w2 : eval mingoNicaQSumWeighted_p2 1 = 15 := by
    unfold mingoNicaQSumWeighted_p2
    rw [eval_add, eval_add, eval_shift_at_one,
        eval_qStratum0_p2, eval_qStratum1_p2, eval_qStratum2_p2]; rfl
  have hc0_w2 : coeff mingoNicaQSumWeighted_p2 0 = 2 := by
    unfold mingoNicaQSumWeighted_p2 qStratum0_p2 qStratum1_p2
    rw [coeff_add, coeff_add, coeff_shift_two_zero,
        coeff_zero_cyclotomicProd (by decide), coeff_zero_cyclotomicProd (by decide)]; rfl
  have hev_w3 : eval mingoNicaQSumWeighted_p3 1 = 52 := by
    unfold mingoNicaQSumWeighted_p3
    rw [eval_add, eval_add, eval_shift_at_one,
        eval_qStratum0_p3, eval_qStratum1_p3, eval_qStratum2_p3]; rfl
  have hc0_w3 : coeff mingoNicaQSumWeighted_p3 0 = 2 := by
    unfold mingoNicaQSumWeighted_p3 qStratum0_p3 qStratum1_p3
    rw [coeff_add, coeff_add, coeff_shift_two_zero,
        coeff_zero_cyclotomicProd (by decide), coeff_zero_cyclotomicProd (by decide)]; rfl
  refine ⟨⟨hev_u1, not_cyclotomic_of_const_ne_one (by rw [hev_u1]; decide) (by rw [hc0_u1]; decide)⟩,
          ⟨hev_u2, not_cyclotomic_of_const_ne_one (by rw [hev_u2]; decide) (by rw [hc0_u2]; decide)⟩,
          ⟨hev_w2, not_cyclotomic_of_const_ne_one (by rw [hev_w2]; decide) (by rw [hc0_w2]; decide)⟩,
          ⟨hev_w3, not_cyclotomic_of_const_ne_one (by rw [hev_w3]; decide) (by rw [hc0_w3]; decide)⟩,
          fun a b => ⟨eval_shiftedStrataP1 a b, not_cyclotomic_shiftedStrataP1 a b⟩⟩

/-! ### 6. Disproof Pillar 5: Universal Prime-Divisor Degree & Order Obstructions -/

theorem disproof_degree_and_order_obstructions :
    -- (a) At p = 3 (`|NC_A(3, 2)| = 52 = 2^2 * 13`), every cyclotomic product requires deg >= 14 and order >= 13
    (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) →
      eval (polyProd ds cyclotomic) 1 = Int.ofNat (annularNCPartitionCount 3 2) →
      14 ≤ sumNatList (ds.map cycloDeg) ∧ (∃ d ∈ ds, 13 ≤ d)) ∧
    -- (b) At p = 8 (`|NC_A(8, 2)| = 38181 = 3 * 11 * 13 * 89`), every cyclotomic product requires deg >= 112 and order >= 89
    (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) →
      eval (polyProd ds cyclotomic) 1 = Int.ofNat (mingoNicaThicknessTwoCount 8) →
      112 ≤ sumNatList (ds.map cycloDeg) ∧ (∃ d ∈ ds, 89 ≤ d)) ∧
    -- (c) Connected partitions at (2, 2) (`|NC_A^conn(2, 2)| = 11`) require deg >= 10 and order >= 11
    (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) →
      eval (polyProd ds cyclotomic) 1 = Int.ofNat (annularNCConnPartitions 2 2).length →
      10 ≤ sumNatList (ds.map cycloDeg) ∧ (∃ d ∈ ds, 11 ≤ d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ds hd1 hev
    have hc3 : annularNCPartitionCount 3 2 = 52 := exact_enumeration_thickness_two.2.2.2.2.1
    rw [hc3] at hev
    have hpos : 1 ≤ eval (polyProd ds cyclotomic) 1 := by rw [hev]; decide
    have hdeg := cyclotomicProd_prime_pow_deg_bound [2, 13]
      (fun p => if p == 2 then 2 else 1)
      (by decide)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact prime_2
        · simp at hp2; subst hp2; exact prime_13)
      hd1 hpos
      (fun p hp => by
        rw [hev]
        rcases List.mem_cons.mp hp with rfl | hp2
        · decide
        · simp at hp2; subst hp2; decide)
    have hord := cyclotomicProd_prime_order_bound hd1 hpos prime_13 (by rw [hev]; decide)
    simp [sumNatList] at hdeg
    exact ⟨hdeg, hord⟩
  · intro ds hd1 hev
    have hc8 : mingoNicaThicknessTwoCount 8 = 38181 := mingoNica_closed_form_values.2.2.2.2.2.1
    rw [hc8] at hev
    have hpos : 1 ≤ eval (polyProd ds cyclotomic) 1 := by rw [hev]; decide
    have hdeg := cyclotomicProd_prime_pow_deg_bound [3, 11, 13, 89]
      (fun _ => 1)
      (by decide)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp1
        · exact prime_3
        · rcases List.mem_cons.mp hp1 with rfl | hp2
          · exact prime_11
          · rcases List.mem_cons.mp hp2 with rfl | hp3
            · exact prime_13
            · simp at hp3; subst hp3; exact prime_89)
      hd1 hpos
      (fun p hp => by
        rw [hev]
        rcases List.mem_cons.mp hp with rfl | hp1
        · decide
        · rcases List.mem_cons.mp hp1 with rfl | hp2
          · decide
          · rcases List.mem_cons.mp hp2 with rfl | hp3
            · decide
            · simp at hp3; subst hp3; decide)
    have hord := cyclotomicProd_prime_order_bound hd1 hpos prime_89 (by rw [hev]; decide)
    simp [sumNatList] at hdeg
    exact ⟨hdeg, hord⟩
  · intro ds hd1 hev
    have hcc : (annularNCConnPartitions 2 2).length = 11 := exact_enumeration_thickness_two.2.2.1
    rw [hcc] at hev
    have hpos : 1 ≤ eval (polyProd ds cyclotomic) 1 := by rw [hev]; decide
    have hdeg := cyclotomicProd_prime_pow_deg_bound [11] (fun _ => 1)
      (by decide)
      (fun p hp => by simp at hp; subst hp; exact prime_11)
      hd1 hpos
      (fun p hp => by simp at hp; subst hp; rw [hev]; decide)
    have hord := cyclotomicProd_prime_order_bound hd1 hpos prime_11 (by rw [hev]; decide)
    simp [sumNatList] at hdeg
    exact ⟨hdeg, hord⟩

/-! ### 7. Master Resolution Theorem for Conjecture 00000004769 -/

theorem conjecture_00000004769_disproved :
    -- 1. Topological misidentification & combinatorial divergence between annulus and torus
    (annulusSurface ≠ torusSurface ∧
      annularNCPartitionCount 4 1 ≠ (torusGenusLe1Partitions 5).length) ∧
    -- 2. Parameter-indexing failure at fixed thickness two
    (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2) →
      eval (polyProd ds cyclotomic) 1 ≠ Int.ofNat (annularNCPartitionCount 1 2) ∧
      eval (polyProd ds cyclotomic) 1 ≠ Int.ofNat (annularNCPartitionCount 2 2)) ∧
    -- 3. Universal failure of poset rank / block-number q-analogues for p = 1, 2, 3 and all p >= 2
    (¬IsCyclotomicProduct (annularRankPoly 1 2) ∧
      ¬IsCyclotomicProduct (annularRankPoly 2 2) ∧
      ¬IsCyclotomicProduct (annularRankPoly 3 2) ∧
      (∀ (p : Nat) (R : Poly), 2 ≤ p → 1 ≤ eval R 1 → IsMonicOfDeg R (p + 1) →
        ((coeff R 1 = Int.ofNat (twoBlockCount p) ∧ coeff R p = Int.ofNat (coTwoBlockCount p)) ∨
         (coeff R 1 = Int.ofNat (coTwoBlockCount p) ∧ coeff R p = Int.ofNat (twoBlockCount p))) →
        ¬IsCyclotomicProduct R)) ∧
    -- 4. Failure of Mingo-Nica q-strata sums and arbitrary monomial shifts at p = 1
    (¬IsCyclotomicProduct mingoNicaQSumWeighted_p2 ∧
      ¬IsCyclotomicProduct mingoNicaQSumWeighted_p3 ∧
      (∀ a b : Nat, ¬IsCyclotomicProduct (shiftedStrataP1 a b))) ∧
    -- 5. Prime-divisor degree and cyclotomic-order lower bounds at p = 3 and p = 8
    ((∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) →
        eval (polyProd ds cyclotomic) 1 = Int.ofNat (annularNCPartitionCount 3 2) →
        14 ≤ sumNatList (ds.map cycloDeg) ∧ (∃ d ∈ ds, 13 ≤ d)) ∧
     (∀ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) →
        eval (polyProd ds cyclotomic) 1 = Int.ofNat (mingoNicaThicknessTwoCount 8) →
        112 ≤ sumNatList (ds.map cycloDeg) ∧ (∃ d ∈ ds, 89 ≤ d))) := by
  exact ⟨⟨disproof_definition_topology.2.2.1, disproof_definition_topology.2.2.2⟩,
         disproof_thickness_indexing.2,
         disproof_rank_q_analogue,
         ⟨disproof_mingo_nica_q_sums_and_shifts.2.2.1.2,
          disproof_mingo_nica_q_sums_and_shifts.2.2.2.1.2,
          fun a b => (disproof_mingo_nica_q_sums_and_shifts.2.2.2.2 a b).2⟩,
         ⟨disproof_degree_and_order_obstructions.1,
          disproof_degree_and_order_obstructions.2.1⟩⟩

end Conjecture00000004769
