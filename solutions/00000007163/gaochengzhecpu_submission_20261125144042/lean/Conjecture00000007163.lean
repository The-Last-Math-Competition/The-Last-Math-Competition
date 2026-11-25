/-
  Conjecture 00000007163 — Core Lean 4.19.0 Formalization
  File: Conjecture00000007163.lean

  Top-level exported theorems resolving Conjecture 00000007163 (FALSE / Disproved),
  combining:
  - Positive non-vacuity and sharp boundary theorems (`positive_markov_doeblin_bound`,
    `positive_strict_floor_separation`, `positive_two_by_two_sharp_bound`);
  - Complete refutations of Clause 1 (almost-irreducible primitivity requirement)
    and Clause 2 (positivity-modulus upper/lower/sharp spectral-gap bounds across
    entrywise minimum `m(A)`, Doeblin column-minimum sum `δ(A)`, and scale-invariant
    entry/Birkhoff ratios);
  - Master theorem `conjecture_00000007163_disproved`.
-/

import Conjecture00000007163.PFMatrix
import Conjecture00000007163.PositiveBounds
import Conjecture00000007163.Counterexamples

namespace Conjecture00000007163

/-! ## 1. Positive Non-Vacuity & Sharp Boundary Theorems -/

/-- Positive Regime 1 (Markov–Doeblin Lower Bound): For every nonnegative `(m+2) × (m+2)`
    matrix `A` with constant row sum `R`, every non-Perron complex eigenvalue `lam ≠ R`
    satisfies `|lam|² ≤ (R - doeblinModulus A)² ≤ (R - (m+2) · posModulusMin A)²`. -/
theorem positive_markov_doeblin_bound {m : Nat} (A : IMat (m + 2)) (R : Int)
    (hnn : IsNonneg A) (hrow : HasConstantRowSum A R)
    (lam : GaussInt) (v : CVec (m + 2))
    (heig : IsComplexEigenpair A lam v) (hne : lam ≠ GaussInt.ofInt R) :
    0 ≤ R - doeblinModulus A ∧
      GaussInt.normSq lam ≤ (R - doeblinModulus A) * (R - doeblinModulus A) ∧
      ((m + 2 : Nat) : Int) * posModulusMin A ≤ doeblinModulus A := by
  rcases constantRowSum_gap_ge_doeblin A R hnn hrow lam v heig hne with ⟨h0, hb⟩
  exact ⟨h0, hb, doeblinModulus_ge_dim_mul_posModulusMin A⟩

/-- Positive Regime 2 (Universal Strict Floor Separation for `A > 0`, `n ≥ 2`):
    Every strictly positive `(m+2) × (m+2)` matrix `A` with positive right Perron
    eigenpair `(A, ρ, u)` has `posModulusMin A < ρ` and strict modulus separation
    `normSq lam < (ρ - posModulusMin A)²` for every eigenvalue `lam ≠ ρ`. -/
theorem positive_strict_floor_separation {m : Nat} (A : IMat (m + 2))
    (hposA : IsStrictlyPositive A)
    (rho : Int) (u : IVec (m + 2))
    (hrho : 0 < rho) (hu : ∀ i, 0 < u i)
    (hPerron : matVec A u = fun i => rho * u i)
    (lam : GaussInt) (x : CVec (m + 2))
    (heig : IsComplexEigenpair A lam x) (hne : lam ≠ GaussInt.ofInt rho) :
    posModulusMin A < rho ∧
      GaussInt.normSq lam < (rho - posModulusMin A) * (rho - posModulusMin A) :=
  strictlyPositive_gap_gt_posModulus A hposA rho u hrho hu hPerron lam x heig hne

/-- Positive Regime 3 (Sharp `2 × 2` Positivity-Modulus Bound `2 m`):
    Every `2 × 2` matrix with entries `≥ m > 0` has modulus spectral gap `≥ 2 m`
    (strictly separated from `m`), attained with equality on both symmetric families. -/
theorem positive_two_by_two_sharp_bound (a b c d m lam₁ lam₂ : Int)
    (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) (hc : m ≤ c) (hd : m ≤ d)
    (hord : lam₂ ≤ lam₁) (htr : lam₁ + lam₂ = a + d)
    (hdisc : (lam₁ - lam₂) * (lam₁ - lam₂) = (a - d) * (a - d) + 4 * (b * c)) :
    let absLam₂ : Int := if 0 ≤ lam₂ then lam₂ else -lam₂
    m < lam₁ - absLam₂ ∧ 2 * m ≤ lam₁ - absLam₂ := by
  intro absLam₂
  have h2m := twoByTwo_gap_ge_two_posModulus a b c d m lam₁ lam₂ hm ha hb hc hd hord htr hdisc
  exact ⟨by omega, h2m⟩

/-! ## 2. Clause-by-Clause Disproof Theorems -/

/-- **Disproof of Clause 1:** Existence of nonnegative matrices (`n = 2` and `n = 3`)
    with simple Perron root and strict modulus & real spectral gap `γ = 2 > 0` that
    are neither irreducible, nor primitive, nor single-essential-class (almost irreducible),
    nor block-supported primitive — plus an irreducible non-primitive matrix with strict
    real spectral gap `γ_re = 4 > 0`. -/
theorem disproof_clause1_almost_irreducible_primitivity :
    (∃ A : IMat 2,
      IsNonneg A ∧
      (∀ x : Int, charPolyEval A x = (x - 3) * (x - 1)) ∧
      ¬ IsIrreducible A ∧ ¬ IsPrimitive A ∧
      ¬ HasSingleEssentialClass A ∧ ¬ IsBlockSupportedPrimitive A) ∧
    (∃ B : IMat 3,
      IsNonneg B ∧
      (∀ x : Int, charPolyEval B x = (x - 3) * ((x - 1) * (x + 1))) ∧
      ¬ IsIrreducible B ∧ ¬ IsPrimitive B ∧
      ¬ HasSingleEssentialClass B ∧ ¬ IsBlockSupportedPrimitive B) ∧
    (∃ C : IMat 2,
      IsNonneg C ∧ IsIrreducible C ∧ ¬ IsPrimitive C ∧
      (∀ x : Int, charPolyEval C x = (x - 2) * (x + 2))) := by
  rcases diag31_disproves_clause1 with ⟨hd1, hd2, _, _, _, hd5, hd6, hd7, hd8⟩
  rcases periodicBlock3_disproves_clause1 with ⟨hp1, hp2, _, _, _, hp6, hp7, hp8, hp9⟩
  rcases cycle2_irreducible_not_primitive with ⟨hc1, hc2, hc3, hc4, _, _⟩
  exact ⟨⟨diag31, hd1, hd2, hd5, hd6, hd7, hd8⟩,
         ⟨periodicBlock3, hp1, hp2, hp6, hp7, hp8, hp9⟩,
         ⟨cycle2, hc1, hc2, hc3, hc4⟩⟩

/-- **Disproof of Clause 2 across all positivity-modulus conventions:**
    1. Primitive nonnegative matrix with `m(A) = 0` yet strict gap `2 > 0`;
    2. Unbounded spectral gap (`> M` for every `M`) at fixed `m(A) = 1` and fixed
       Doeblin modulus `δ(A) = 2` (even among symmetric strictly positive matrices);
    3. Failure of Doeblin / `n · m(A)` as a lower bound on symmetric strictly
       positive `3 × 3` and `4 × 4` matrices (`γ < δ(A) = n · m(A)`);
    4. Failure of `δ(P)` and `m(P)` as upper bounds even on doubly stochastic
       strictly positive matrices (`m(P) < δ(P) < γ(P)`);
    5. Arbitrarily small scale-invariant entry-ratio and Birkhoff–Hopf moduli
       while the relative spectral gap `(λ₁ - λ₂) / λ₁` approaches `1`. -/
theorem conjecture_00000007163_disproved :
    -- (1) Clause 1 refuted: strict gap without irreducibility, primitivity, or almost-irreducibility
    (∃ A : IMat 2,
      IsNonneg A ∧ (∀ x : Int, charPolyEval A x = (x - 3) * (x - 1)) ∧
      ¬ IsIrreducible A ∧ ¬ IsPrimitive A ∧
      ¬ HasSingleEssentialClass A ∧ ¬ IsBlockSupportedPrimitive A) ∧
    -- (2) Primitive matrix with zero entrywise modulus (`m = 0`) and strict gap `3 - |-1| = 2`
    (∃ A : IMat 2,
      IsNonneg A ∧ IsPrimitive A ∧ posModulusMin A = 0 ∧
      (∀ x : Int, charPolyEval A x = (x - 3) * (x + 1))) ∧
    -- (3) Unbounded gap at unit positivity floor `m = 1` and constant Doeblin modulus `δ = 2`
    (∀ M : Int, ∃ A : IMat 2, ∃ B : IMat 2, ∃ rhoA rhoB : Int,
      IsSymmetric A ∧ IsStrictlyPositive A ∧ posModulusMin A = 1 ∧
      (∀ x : Int, charPolyEval A x = x * (x - rhoA)) ∧ M < rhoA ∧
      IsStrictlyPositive B ∧ posModulusMin B = 1 ∧ doeblinModulus B = 2 ∧
      (∀ x : Int, charPolyEval B x = x * (x - rhoB)) ∧ M < rhoB) ∧
    -- (4) Doeblin / `n · m` lower bound fails on strictly positive symmetric matrices (`n = 3, 4`)
    (∃ A : IMat 3,
      IsSymmetric A ∧ IsStrictlyPositive A ∧
      (∀ x : Int, charPolyEval A x = (x - 10) * ((x - 5) * (x - 1))) ∧
      posModulusMin A < 10 - 5 ∧ 10 - 5 < doeblinModulus A) ∧
    (∃ A : IMat 4,
      IsSymmetric A ∧ IsStrictlyPositive A ∧ posModulusMin A = 1 ∧
      (∀ x : Int, charPolyEval A x = x * ((x - 6) * ((x - 3) * (x - 1)))) ∧
      6 - 3 < doeblinModulus A) ∧
    -- (5) Upper bound fails even on constant-row-sum (doubly stochastic) positive matrices
    (∃ P : IMat 4,
      IsSymmetric P ∧ IsStrictlyPositive P ∧ HasConstantRowSum P 10 ∧
      (∀ x : Int, charPolyEval P x = (x - 10) * ((x - 2) * ((x - 2) * (x + 2)))) ∧
      posModulusMin P < doeblinModulus P ∧ doeblinModulus P < 10 - 2) ∧
    -- (6) Scale-invariant / Birkhoff–Hopf moduli diverge from relative spectral gap
    (∀ N : Int, 1 ≤ N → ∃ A : IMat 2, ∃ lam₁ lam₂ : Int,
      IsSymmetric A ∧ IsStrictlyPositive A ∧ 0 < lam₂ ∧ lam₂ < lam₁ ∧
      (∀ x : Int, charPolyEval A x = (x - lam₁) * (x - lam₂)) ∧
      N * posModulusMin A < entryMax A ∧
      (N - 1) * lam₁ < N * (lam₁ - lam₂)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases diag31_disproves_clause1 with ⟨h1, h2, _, _, _, h5, h6, h7, h8⟩
    exact ⟨diag31, h1, h2, h5, h6, h7, h8⟩
  · rcases primZeroMod_properties with ⟨h1, h2, h3, _, h5, _, _⟩
    exact ⟨primZeroMod, h1, h2, h3, h5⟩
  · intro M
    rcases unbounded_gap_fixed_modulus_families M with
      ⟨K, _, hsA, hpA, hmA, hcA, _, _, hMA, hpB, hmB, hdB, hcB, _, _, hMB⟩
    exact ⟨symRank1Family K, constDeltaFamily K, K * K + 1, K + 1,
           hsA, hpA, hmA, hcA, by omega, hpB, hmB, hdB, hcB, by omega⟩
  · rcases doeblinFail3_properties with ⟨h1, h2, _, _, h5, _, _, _, h9, h10⟩
    exact ⟨doeblinFail3, h1, h2, h5, h9, h10⟩
  · rcases doeblinFail4_properties with ⟨h1, h2, h3, _, h5, _, _, _, _, _, h11⟩
    exact ⟨doeblinFail4, h1, h2, h3, h5, h11⟩
  · rcases stochasticScaled4_properties with ⟨h1, h2, h3, h4, h5, _, _, _, _, h10, h11⟩
    refine ⟨stochasticScaled4, h1, h2, h3, h10, ?_, h11⟩
    rw [h4, h5]; decide
  · intro N hN
    rcases ratioGapFamily_arbitrage N hN with ⟨p, hp3, hmin_max, _, hrel⟩
    have hp2 : 2 ≤ p := by omega
    rcases ratioGapFamily_properties p hp2 with ⟨hsym, hpos, _, _, hchar, _, _⟩
    have hpp : 9 ≤ p * p := Int.mul_le_mul hp3 hp3 (by omega) (by omega)
    have hp1 : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by
      rw [Int.add_mul, Int.mul_add]; omega
    exact ⟨ratioGapFamily p, (p + 1) * (p + 1), 2 * p - 3,
           hsym, hpos, by omega, by omega, hchar, hmin_max, hrel⟩

end Conjecture00000007163
