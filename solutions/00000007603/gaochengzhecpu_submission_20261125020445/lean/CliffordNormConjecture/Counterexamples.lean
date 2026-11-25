/-
Copyright (c) 2026. All rights reserved.
Sharp counterexamples refuting Conjecture 00000007603 across all standard
Clifford-algebra norm conventions, dimensions, signatures, and unit-group readings.
-/
import CliffordNormConjecture.Positive

namespace CliffordNormConjecture
namespace Cl

section DimensionLifting

variable {R : Type} [CommRing R]

/-- Isometric algebra embedding `Cl_{1,0} ↪ Cl_{m+1,0}` for all `m ∈ ℕ`. -/
def liftEuc1 : (m : Nat) → Cl R (eucSig R 1) → Cl R (eucSig R (m + 1))
  | 0, x => x
  | m + 1, x => embedLeft (liftEuc1 m x)

/-- Isometric algebra embedding `Cl_{0,1} ↪ Cl_{0,m+1}` for all `m ∈ ℕ`. -/
def liftSpin1 : (m : Nat) → Cl R (spinSig R 1) → Cl R (spinSig R (m + 1))
  | 0, x => x
  | m + 1, x => embedLeft (liftSpin1 m x)

/-- Isometric algebra embedding `Cl_{0,3} ↪ Cl_{0,m+3}` for all `m ∈ ℕ`. -/
def liftSpin3 : (m : Nat) → Cl R (spinSig R 3) → Cl R (spinSig R (m + 3))
  | 0, x => x
  | m + 1, x => embedLeft (liftSpin3 m x)

/-- Isometric algebra embedding `Cl_{4,0} ↪ Cl_{m+4,0}` for all `m ∈ ℕ`. -/
def liftEuc4 : (m : Nat) → Cl R (eucSig R 4) → Cl R (eucSig R (m + 4))
  | 0, x => x
  | m + 1, x => embedLeft (liftEuc4 m x)

theorem liftEuc1_mul (m : Nat) (x y : Cl R (eucSig R 1)) :
    liftEuc1 m (mul x y) = mul (liftEuc1 m x) (liftEuc1 m y) := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc1, ih, embedLeft_mul]

theorem liftEuc1_l2NormSq (m : Nat) (x : Cl R (eucSig R 1)) :
    l2NormSq (liftEuc1 m x) = l2NormSq x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc1, embedLeft_l2NormSq, ih]

theorem liftEuc1_revNorm (m : Nat) (x : Cl R (eucSig R 1)) :
    revNorm (liftEuc1 m x) = revNorm x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc1, embedLeft_revNorm, ih]

theorem liftEuc1_eq_zero_iff (m : Nat) (x : Cl R (eucSig R 1)) :
    liftEuc1 m x = zero ↔ x = zero := by
  induction m with
  | zero => exact Iff.rfl
  | succ k ih => exact Iff.trans (embedLeft_eq_zero_iff _) ih

theorem liftSpin1_mul (m : Nat) (x y : Cl R (spinSig R 1)) :
    liftSpin1 m (mul x y) = mul (liftSpin1 m x) (liftSpin1 m y) := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftSpin1, ih, embedLeft_mul]

theorem liftSpin1_revNorm (m : Nat) (x : Cl R (spinSig R 1)) :
    revNorm (liftSpin1 m x) = revNorm x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftSpin1, embedLeft_revNorm, ih]

theorem liftSpin3_mul (m : Nat) (x y : Cl R (spinSig R 3)) :
    liftSpin3 m (mul x y) = mul (liftSpin3 m x) (liftSpin3 m y) := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftSpin3, ih, embedLeft_mul]

theorem liftSpin3_l2NormSq (m : Nat) (x : Cl R (spinSig R 3)) :
    l2NormSq (liftSpin3 m x) = l2NormSq x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftSpin3, embedLeft_l2NormSq, ih]

theorem liftSpin3_conjNorm (m : Nat) (x : Cl R (spinSig R 3)) :
    conjNorm (liftSpin3 m x) = conjNorm x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftSpin3, embedLeft_conjNorm, ih]

theorem liftSpin3_eq_zero_iff (m : Nat) (x : Cl R (spinSig R 3)) :
    liftSpin3 m x = zero ↔ x = zero := by
  induction m with
  | zero => exact Iff.rfl
  | succ k ih => exact Iff.trans (embedLeft_eq_zero_iff _) ih

theorem liftEuc4_mul (m : Nat) (x y : Cl R (eucSig R 4)) :
    liftEuc4 m (mul x y) = mul (liftEuc4 m x) (liftEuc4 m y) := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc4, ih, embedLeft_mul]

theorem liftEuc4_involute (m : Nat) (x : Cl R (eucSig R 4)) :
    involute (liftEuc4 m x) = liftEuc4 m (involute x) := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc4, embedLeft_involute, ih]

theorem liftEuc4_l2NormSq (m : Nat) (x : Cl R (eucSig R 4)) :
    l2NormSq (liftEuc4 m x) = l2NormSq x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc4, embedLeft_l2NormSq, ih]

theorem liftEuc4_revNorm (m : Nat) (x : Cl R (eucSig R 4)) :
    revNorm (liftEuc4 m x) = revNorm x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc4, embedLeft_revNorm, ih]

theorem liftEuc4_conjNorm (m : Nat) (x : Cl R (eucSig R 4)) :
    conjNorm (liftEuc4 m x) = conjNorm x := by
  induction m with
  | zero => rfl
  | succ k ih => simp only [liftEuc4, embedLeft_conjNorm, ih]

theorem liftEuc4_eq_zero_iff (m : Nat) (x : Cl R (eucSig R 4)) :
    liftEuc4 m x = zero ↔ x = zero := by
  induction m with
  | zero => exact Iff.rfl
  | succ k ih => exact Iff.trans (embedLeft_eq_zero_iff _) ih

end DimensionLifting

section OrderedRingRefutations

variable {R : Type} [OrderedCommRing R]

/-- Base counterexample in `Cl_{1,0}`: `X_+ = 1 + e₁` and `X_- = 1 - e₁`. -/
def xPlus10 : Cl R (eucSig R 1) := ((1 : R), (1 : R))
def xMinus10 : Cl R (eucSig R 1) := ((1 : R), -(1 : R))

theorem xPlus10_l2 : l2NormSq (xPlus10 (R := R)) = two R := by
  change (1 : R) * 1 + 1 * 1 = (1 : R) + 1
  rw [CommRing.one_mul]

theorem xMinus10_l2 : l2NormSq (xMinus10 (R := R)) = two R := by
  change (1 : R) * 1 + (-(1 : R)) * (-(1 : R)) = (1 : R) + 1
  rw [neg_mul_neg, CommRing.one_mul]

theorem xPlus10_sq_l2 : l2NormSq (mul (xPlus10 (R := R)) xPlus10) = eight R := by
  have hm : mul (xPlus10 (R := R)) xPlus10 = (two R, two R) := by
    refine Prod.ext ?_ ?_
    · change (1 : R) * 1 + 1 * (1 * 1) = (1 : R) + 1
      rw [CommRing.one_mul, CommRing.one_mul]
    · change (1 : R) * 1 + 1 * 1 = (1 : R) + 1
      rw [CommRing.one_mul]
  rw [hm]
  change two R * two R + two R * two R = two R * (two R * two R)
  unfold two
  rw [CommRing.right_distrib (1 : R) 1 ((1 + 1) * (1 + 1)), CommRing.one_mul]

theorem xPlus10_mul_xMinus10 : mul (xPlus10 (R := R)) xMinus10 = zero := by
  refine Prod.ext ?_ ?_
  · change (1 : R) * 1 + 1 * (1 * -(1 : R)) = 0
    rw [CommRing.one_mul, CommRing.one_mul, CommRing.one_mul, add_neg_cancel]
  · change (1 : R) * -(1 : R) + 1 * 1 = 0
    rw [CommRing.one_mul, CommRing.one_mul, CommRing.neg_add_cancel]

/-- Refutation Theorem 1A (Euclidean `Cl_{n,0}` for ALL `n = m + 1 ≥ 1`, over any `OrderedCommRing R`):
    There exist nonzero multivectors `X_+, X_- ∈ Cl_{m+1,0}(R)` such that:
    - `‖X_+‖₂² = N_rev(X_+) = 2` and `‖X_-‖₂² = N_rev(X_-) = 2` (so product bound = 4),
    - `‖X_+²‖₂² = N_rev(X_+²) = 8 > 4 = ‖X_+‖₂² · ‖X_+‖₂²` (violating BOTH equality and C = 1 bound,
      and strictly exceeding the ratio `1` achieved by all grade-1 vector pairs),
    - `X_+ X_- = 0`, so `‖X_+ X_-‖₂² = 0 < 4` (zero-divisor collapse). -/
theorem refutation_euc_all_pos_dim (m : Nat) :
    ∃ xPlus xMinus : Cl R (eucSig R (m + 1)),
      l2NormSq xPlus = two R ∧
      revNorm xPlus = two R ∧
      l2NormSq xMinus = two R ∧
      revNorm xMinus = two R ∧
      l2NormSq (mul xPlus xPlus) = eight R ∧
      revNorm (mul xPlus xPlus) = eight R ∧
      l2NormSq xPlus * l2NormSq xPlus < l2NormSq (mul xPlus xPlus) ∧
      mul xPlus xMinus = zero ∧
      l2NormSq (mul xPlus xMinus) = 0 := by
  refine ⟨liftEuc1 m xPlus10, liftEuc1 m xMinus10, ?_⟩
  have hl2p : l2NormSq (liftEuc1 m (xPlus10 (R := R))) = two R := by
    rw [liftEuc1_l2NormSq, xPlus10_l2]
  have hl2m : l2NormSq (liftEuc1 m (xMinus10 (R := R))) = two R := by
    rw [liftEuc1_l2NormSq, xMinus10_l2]
  have hl2sq : l2NormSq (mul (liftEuc1 m (xPlus10 (R := R))) (liftEuc1 m xPlus10)) = eight R := by
    rw [← liftEuc1_mul, liftEuc1_l2NormSq, xPlus10_sq_l2]
  have hzd : mul (liftEuc1 m (xPlus10 (R := R))) (liftEuc1 m xMinus10) = zero := by
    rw [← liftEuc1_mul, xPlus10_mul_xMinus10]
    exact (liftEuc1_eq_zero_iff m zero).2 rfl
  refine ⟨hl2p, ?_, hl2m, ?_, hl2sq, ?_, ?_, hzd, ?_⟩
  · rw [euc_revNorm_eq_l2NormSq, hl2p]
  · rw [euc_revNorm_eq_l2NormSq, hl2m]
  · rw [euc_revNorm_eq_l2NormSq, hl2sq]
  · rw [hl2p, hl2sq]; exact four_lt_eight
  · rw [hzd, l2NormSq_zero]

/-- Base counterexample in `Cl_{0,3}`: `X_± = 1 ± e₁e₂e₃`. -/
def xPlus03 : Cl R (spinSig R 3) :=
  ((((1 : R), 0), (0, 0)), ((0, 0), (0, (1 : R))))

def xMinus03 : Cl R (spinSig R 3) :=
  ((((1 : R), 0), (0, 0)), ((0, 0), (0, -(1 : R))))

theorem xPlus03_l2 : l2NormSq (xPlus03 (R := R)) = two R := by
  simp only [xPlus03, l2NormSq, zero_mul, CommRing.one_mul, CommRing.add_zero, CommRing.zero_add]
  rfl

theorem xMinus03_l2 : l2NormSq (xMinus03 (R := R)) = two R := by
  simp only [xMinus03, l2NormSq, zero_mul, neg_mul_neg, CommRing.one_mul,
    CommRing.add_zero, CommRing.zero_add]
  rfl

theorem xPlus03_sq_l2 : l2NormSq (mul (xPlus03 (R := R)) xPlus03) = eight R := by
  have hm : mul (xPlus03 (R := R)) xPlus03 =
      ((((two R, 0), (0, 0)), ((0, 0), (0, two R))) : Cl R (spinSig R 3)) := by
    simp only [xPlus03, spinSig, repSig, mul, add, smul, involute, neg,
      zero_mul, mul_zero, CommRing.one_mul, CommRing.mul_one,
      CommRing.add_zero, CommRing.zero_add, neg_zero_eq, neg_involutive,
      neg_mul, mul_neg, neg_mul_neg]
    rfl
  rw [hm]
  simp only [l2NormSq, zero_mul, CommRing.add_zero, CommRing.zero_add]
  unfold eight four two
  rw [CommRing.right_distrib (1 : R) 1 (((1 + 1) * (1 + 1))), CommRing.one_mul]

theorem xPlus03_mul_xMinus03 : mul (xPlus03 (R := R)) xMinus03 = zero := by
  simp only [xPlus03, xMinus03, spinSig, repSig, mul, add, smul, involute, neg, zero,
    zero_mul, mul_zero, CommRing.one_mul, CommRing.mul_one,
    CommRing.add_zero, CommRing.zero_add, neg_zero_eq, neg_involutive,
    neg_mul, mul_neg, neg_mul_neg, add_neg_cancel, CommRing.neg_add_cancel]

/-- Refutation Theorem 1B (Spin-Euclidean `Cl_{0,n}` for ALL `n = m + 3 ≥ 3`, over any `OrderedCommRing R`):
    In `Cl_{0,m+3}(R)` (where Hurwitz multiplicativity held for `n ≤ 2`!), `X_± = 1 ± e₁e₂e₃` satisfy:
    - `‖X_±‖₂² = N_conj(X_±) = 2`,
    - `‖X_+²‖₂² = N_conj(X_+²) = 8 > 4 = ‖X_+‖₂² · ‖X_+‖₂²`,
    - `X_+ X_- = 0`, so `‖X_+ X_-‖₂² = N_conj(X_+ X_-) = 0 < 4`. -/
theorem refutation_spin_all_ge_three (m : Nat) :
    ∃ xPlus xMinus : Cl R (spinSig R (m + 3)),
      l2NormSq xPlus = two R ∧
      conjNorm xPlus = two R ∧
      l2NormSq xMinus = two R ∧
      conjNorm xMinus = two R ∧
      l2NormSq (mul xPlus xPlus) = eight R ∧
      conjNorm (mul xPlus xPlus) = eight R ∧
      l2NormSq xPlus * l2NormSq xPlus < l2NormSq (mul xPlus xPlus) ∧
      mul xPlus xMinus = zero ∧
      l2NormSq (mul xPlus xMinus) = 0 := by
  refine ⟨liftSpin3 m xPlus03, liftSpin3 m xMinus03, ?_⟩
  have hl2p : l2NormSq (liftSpin3 m (xPlus03 (R := R))) = two R := by
    rw [liftSpin3_l2NormSq, xPlus03_l2]
  have hl2m : l2NormSq (liftSpin3 m (xMinus03 (R := R))) = two R := by
    rw [liftSpin3_l2NormSq, xMinus03_l2]
  have hl2sq : l2NormSq (mul (liftSpin3 m (xPlus03 (R := R))) (liftSpin3 m xPlus03)) = eight R := by
    rw [← liftSpin3_mul, liftSpin3_l2NormSq, xPlus03_sq_l2]
  have hzd : mul (liftSpin3 m (xPlus03 (R := R))) (liftSpin3 m xMinus03) = zero := by
    rw [← liftSpin3_mul, xPlus03_mul_xMinus03]
    exact (liftSpin3_eq_zero_iff m zero).2 rfl
  refine ⟨hl2p, ?_, hl2m, ?_, hl2sq, ?_, ?_, hzd, ?_⟩
  · rw [spin_conjNorm_eq_l2NormSq, hl2p]
  · rw [spin_conjNorm_eq_l2NormSq, hl2m]
  · rw [spin_conjNorm_eq_l2NormSq, hl2sq]
  · rw [hl2p, hl2sq]; exact four_lt_eight
  · rw [hzd, l2NormSq_zero]

/-- Also in `Cl_{0,m+1}` (`n ≥ 1`), the reversal scalar form `N_rev` fails multiplicativity:
    `W = 1 + e₁` satisfies `N_rev(W) = 0`, yet `N_rev(W²) = -4 ≠ 0`. -/
theorem refutation_spin_revNorm_all_pos_dim (m : Nat) :
    ∃ w : Cl R (spinSig R (m + 1)),
      revNorm w = 0 ∧ revNorm (mul w w) = -(four R) ∧ revNorm (mul w w) ≠ revNorm w * revNorm w := by
  let w0 : Cl R (spinSig R 1) := ((1 : R), (1 : R))
  refine ⟨liftSpin1 m w0, ?_⟩
  have hw0 : revNorm w0 = 0 := by
    change (1 : R) * 1 + (-(1 : R)) * (1 * 1) = 0
    rw [CommRing.one_mul, neg_mul, CommRing.one_mul, add_neg_cancel]
  have hw0sq : revNorm (mul w0 w0) = -(four R) := by
    have hm : mul w0 w0 = ((0 : R), two R) := by
      refine Prod.ext ?_ ?_
      · change (1 : R) * 1 + (-(1 : R)) * (1 * 1) = 0
        rw [CommRing.one_mul, neg_mul, CommRing.one_mul, add_neg_cancel]
      · change (1 : R) * 1 + 1 * 1 = two R
        rw [CommRing.one_mul]; rfl
    rw [hm]
    change (0 : R) * 0 + (-(1 : R)) * (two R * two R) = -(four R)
    rw [zero_mul, CommRing.zero_add, neg_mul, CommRing.one_mul]
    rfl
  rw [liftSpin1_revNorm, hw0, ← liftSpin1_mul, liftSpin1_revNorm, hw0sq, zero_mul]
  refine ⟨rfl, rfl, ?_⟩
  intro hcontra
  have hpos : (0 : R) < four R := zero_lt_four
  have heq : four R = 0 := by
    have h1 : -(four R) + four R = 0 + four R := congrArg (fun t => t + four R) hcontra
    rw [CommRing.neg_add_cancel, CommRing.zero_add] at h1
    exact h1.symm
  exact ne_of_lt hpos heq.symm

/-- Recursive pseudoscalar blade `e₁ ⋯ e_n` in `Cl R sig`. -/
def omegaBlade {R : Type} [CommRing R] : {sig : List R} → Cl R sig
  | [] => (1 : R)
  | _ :: _ => (zero, omegaBlade)

theorem omegaBlade_l2 {sig : List R} : l2NormSq (omegaBlade (sig := sig)) = 1 := by
  induction sig with
  | nil => exact CommRing.one_mul 1
  | cons _ _ ih => simp only [omegaBlade, l2NormSq, l2NormSq_zero, CommRing.zero_add, ih]

theorem omegaBlade_involute_1 :
    involute (omegaBlade : Cl R (eucSig R 1)) = neg omegaBlade :=
  Prod.ext (by change (0 : R) = -(0 : R); exact neg_zero_eq.symm) rfl

theorem omegaBlade_involute_2 :
    involute (omegaBlade : Cl R (eucSig R 2)) = omegaBlade :=
  Prod.ext involute_zero
    (by change neg (involute (omegaBlade : Cl R (eucSig R 1))) = omegaBlade
        rw [omegaBlade_involute_1, neg_involutive_cl])

theorem omegaBlade_involute_3 :
    involute (omegaBlade : Cl R (eucSig R 3)) = neg omegaBlade :=
  Prod.ext (by change involute zero = neg zero; rw [involute_zero, neg_zero_cl])
    (by change neg (involute (omegaBlade : Cl R (eucSig R 2))) = neg omegaBlade
        rw [omegaBlade_involute_2])

theorem omegaBlade_rev_3 :
    rev (omegaBlade : Cl R (eucSig R 3)) = neg omegaBlade := by
  have hr1 : rev (omegaBlade : Cl R (eucSig R 1)) = omegaBlade := Prod.ext rfl rfl
  have hr2 : rev (omegaBlade : Cl R (eucSig R 2)) = neg omegaBlade :=
    Prod.ext (by change rev zero = neg zero; rw [rev_zero, neg_zero_cl])
      (by change involute (rev (omegaBlade : Cl R (eucSig R 1))) = neg omegaBlade
          rw [hr1, omegaBlade_involute_1])
  exact Prod.ext (by change rev zero = neg zero; rw [rev_zero, neg_zero_cl])
    (by change involute (rev (omegaBlade : Cl R (eucSig R 2))) = neg omegaBlade
        rw [hr2, involute_neg, omegaBlade_involute_2])

theorem omegaBlade_sq_3 :
    mul (omegaBlade : Cl R (eucSig R 3)) omegaBlade = neg one := by
  have h1 : mul (omegaBlade : Cl R (eucSig R 1)) omegaBlade = one := by
    refine Prod.ext ?_ ?_
    · change (0 : R) * 0 + 1 * (1 * 1) = 1
      rw [zero_mul, CommRing.zero_add, CommRing.one_mul, CommRing.one_mul]
    · change (0 : R) * 1 + 1 * 0 = 0
      rw [zero_mul, mul_zero, CommRing.add_zero]
  have h2 : mul (omegaBlade : Cl R (eucSig R 2)) omegaBlade = neg one := by
    refine Prod.ext ?_ ?_
    · change add (mul zero zero) (smul 1 (mul (omegaBlade : Cl R (eucSig R 1)) (involute omegaBlade))) =
        neg (one : Cl R (eucSig R 1))
      rw [zero_mul_cl, zero_add_cl, one_smul_cl, omegaBlade_involute_1, mul_neg_cl, h1]
    · change add (mul zero _) (mul _ (involute zero)) = neg zero
      rw [zero_mul_cl, involute_zero, mul_zero_cl, add_zero_cl, neg_zero_cl]
  refine Prod.ext ?_ ?_
  · change add (mul zero zero) (smul 1 (mul (omegaBlade : Cl R (eucSig R 2)) (involute omegaBlade))) =
      neg (one : Cl R (eucSig R 2))
    rw [zero_mul_cl, zero_add_cl, one_smul_cl, omegaBlade_involute_2, h2]
  · change add (mul zero _) (mul _ (involute zero)) = neg zero
    rw [zero_mul_cl, involute_zero, mul_zero_cl, add_zero_cl, neg_zero_cl]

/-- Base even counterexample in Euclidean `Cl_{4,0}`: `X_± = 1 ± e₁e₂e₃e₄ = (one, ±ω₃) ∈ Cl_{4,0}^+`. -/
def xPlus40 : Cl R (eucSig R 4) := (one, omegaBlade)
def xMinus40 : Cl R (eucSig R 4) := (one, neg omegaBlade)

/-- Refutation Theorem 1C (Simultaneous Triple-Norm Failure on Even Multivectors in `Cl_{n,0}`, ALL `n = m + 4 ≥ 4`):
    In positive-definite Euclidean `Cl_{m+4,0}(R)`, the even multivectors `X_± = 1 ± e₁e₂e₃e₄`
    (`involute X_± = X_±`) simultaneously defeat `‖·‖₂²`, `N_rev`, AND `N_conj`:
    all three assign `2` to `X_+` and `X_-`, `8 > 4` to `X_+²`, and `0 < 4` to `X_+ X_-`. -/
theorem refutation_euc_even_triple_norm_ge_four (m : Nat) :
    ∃ xPlus xMinus : Cl R (eucSig R (m + 4)),
      involute xPlus = xPlus ∧
      involute xMinus = xMinus ∧
      l2NormSq xPlus = two R ∧ revNorm xPlus = two R ∧ conjNorm xPlus = two R ∧
      l2NormSq xMinus = two R ∧ revNorm xMinus = two R ∧ conjNorm xMinus = two R ∧
      l2NormSq (mul xPlus xPlus) = eight R ∧
      revNorm (mul xPlus xPlus) = eight R ∧
      conjNorm (mul xPlus xPlus) = eight R ∧
      mul xPlus xMinus = zero := by
  refine ⟨liftEuc4 m xPlus40, liftEuc4 m xMinus40, ?_⟩
  have hinvP : involute (xPlus40 (R := R)) = xPlus40 := by
    change (involute one, neg (involute (omegaBlade : Cl R (eucSig R 3)))) = (one, omegaBlade)
    rw [involute_one, omegaBlade_involute_3, neg_involutive_cl]
  have hinvM : involute (xMinus40 (R := R)) = xMinus40 := by
    change (involute one, neg (involute (neg (omegaBlade : Cl R (eucSig R 3))))) = (one, neg omegaBlade)
    rw [involute_one, involute_neg, omegaBlade_involute_3, neg_involutive_cl]
  have hrevP : rev (xPlus40 (R := R)) = xPlus40 := by
    change (rev one, involute (rev (omegaBlade : Cl R (eucSig R 3)))) = (one, omegaBlade)
    rw [rev_one, omegaBlade_rev_3, involute_neg, omegaBlade_involute_3, neg_involutive_cl]
  have hrevM : rev (xMinus40 (R := R)) = xMinus40 := by
    change (rev one, involute (rev (neg (omegaBlade : Cl R (eucSig R 3))))) = (one, neg omegaBlade)
    rw [rev_one, rev_neg, omegaBlade_rev_3, neg_involutive_cl, omegaBlade_involute_3]
  have hconjP : conj (xPlus40 (R := R)) = xPlus40 := by
    rw [conj_eq_rev_involute, hinvP, hrevP]
  have hconjM : conj (xMinus40 (R := R)) = xMinus40 := by
    rw [conj_eq_rev_involute, hinvM, hrevM]
  have hl2P : l2NormSq (xPlus40 (R := R)) = two R := by
    change l2NormSq (one : Cl R (eucSig R 3)) + l2NormSq (omegaBlade : Cl R (eucSig R 3)) = two R
    rw [l2NormSq_one, omegaBlade_l2]; rfl
  have hl2M : l2NormSq (xMinus40 (R := R)) = two R := by
    change l2NormSq (one : Cl R (eucSig R 3)) + l2NormSq (neg (omegaBlade : Cl R (eucSig R 3))) = two R
    rw [l2NormSq_one, l2NormSq_neg, omegaBlade_l2]; rfl
  have hsq : mul (xPlus40 (R := R)) xPlus40 = smul (two R) xPlus40 := by
    refine Prod.ext ?_ ?_
    · change add (mul one one) (smul 1 (mul (omegaBlade : Cl R (eucSig R 3)) (involute omegaBlade))) =
        smul (two R) one
      rw [one_mul_cl, one_smul_cl, omegaBlade_involute_3, mul_neg_cl, omegaBlade_sq_3,
          neg_involutive_cl]
      unfold two
      rw [add_smul_cl, one_smul_cl]
    · change add (mul one omegaBlade) (mul omegaBlade (involute one)) = smul (two R) omegaBlade
      rw [one_mul_cl, involute_one, mul_one_cl]
      unfold two
      rw [add_smul_cl, one_smul_cl]
  have hl2Sq : l2NormSq (mul (xPlus40 (R := R)) xPlus40) = eight R := by
    rw [hsq, l2NormSq_smul, hl2P]
    unfold eight four
    rw [CommRing.mul_comm (two R * two R) (two R)]
  have hcEqR_P : conj (xPlus40 (R := R)) = rev (xPlus40 (R := R)) :=
    Eq.trans hconjP hrevP.symm
  have hcEqR_M : conj (xMinus40 (R := R)) = rev (xMinus40 (R := R)) :=
    Eq.trans hconjM hrevM.symm
  have hconjNP : conjNorm (xPlus40 (R := R)) = two R := by
    unfold conjNorm
    rw [hcEqR_P]
    exact Eq.trans (euc_revNorm_eq_l2NormSq 4 xPlus40) hl2P
  have hconjNM : conjNorm (xMinus40 (R := R)) = two R := by
    unfold conjNorm
    rw [hcEqR_M]
    exact Eq.trans (euc_revNorm_eq_l2NormSq 4 xMinus40) hl2M
  have hconjNSq : conjNorm (mul (xPlus40 (R := R)) xPlus40) = eight R := by
    have hcEqR_Sq : conj (mul (xPlus40 (R := R)) xPlus40) = rev (mul (xPlus40 (R := R)) xPlus40) := by
      rw [conj_mul, hcEqR_P, ← rev_mul]
    unfold conjNorm
    rw [hcEqR_Sq]
    exact Eq.trans (euc_revNorm_eq_l2NormSq 4 (mul xPlus40 xPlus40)) hl2Sq
  have hzd : mul (xPlus40 (R := R)) xMinus40 = zero := by
    refine Prod.ext ?_ ?_
    · change add (mul one one) (smul 1 (mul (omegaBlade : Cl R (eucSig R 3)) (involute (neg omegaBlade)))) = zero
      rw [one_mul_cl, one_smul_cl, involute_neg, omegaBlade_involute_3, neg_involutive_cl,
          omegaBlade_sq_3, add_neg_cancel_cl]
    · change add (mul one (neg omegaBlade)) (mul omegaBlade (involute one)) = zero
      rw [one_mul_cl, involute_one, mul_one_cl, neg_add_cancel_cl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [liftEuc4_involute, hinvP]
  · rw [liftEuc4_involute, hinvM]
  · rw [liftEuc4_l2NormSq, hl2P]
  · rw [euc_revNorm_eq_l2NormSq, liftEuc4_l2NormSq, hl2P]
  · rw [liftEuc4_conjNorm, hconjP |> fun _ => hconjNP]
  · rw [liftEuc4_l2NormSq, hl2M]
  · rw [euc_revNorm_eq_l2NormSq, liftEuc4_l2NormSq, hl2M]
  · rw [liftEuc4_conjNorm, hconjNM]
  · rw [← liftEuc4_mul, liftEuc4_l2NormSq, hl2Sq]
  · rw [euc_revNorm_eq_l2NormSq, ← liftEuc4_mul, liftEuc4_l2NormSq, hl2Sq]
  · rw [← liftEuc4_mul, liftEuc4_conjNorm, hconjNSq]
  · rw [← liftEuc4_mul, hzd]; exact (liftEuc4_eq_zero_iff m zero).2 rfl

/-- Refutation Theorem 1D (Indefinite Metric `Cl_{1,1}` Even on Grade-1 Vector Pairs!):
    Isotropic grade-1 vectors `u = e₁ + e₂` and `v = e₁ - e₂` satisfy `Q(u) = Q(v) = 0`
    (so `Q(u) Q(v) = 0`), YET `u v ≠ 0` with `‖u v‖₂² = 8 > 4 = ‖u‖₂² ‖v‖₂²`,
    `u² = 0`, and `N_rev(u v) = 0` despite `u v ≠ 0` (showing `N_rev` is degenerate). -/
theorem refutation_indefinite_vector_pairs :
    ∃ u v : Vec R [(1 : R), -(1 : R)],
      quadForm u = 0 ∧
      quadForm v = 0 ∧
      mul (ofVec u) (ofVec v) ≠ zero ∧
      l2NormSq (ofVec u) = two R ∧
      l2NormSq (ofVec v) = two R ∧
      l2NormSq (mul (ofVec u) (ofVec v)) = eight R ∧
      l2NormSq (mul (ofVec u) (ofVec u)) = 0 ∧
      revNorm (mul (ofVec u) (ofVec v)) = 0 := by
  let u : Vec R [(1 : R), -(1 : R)] := ((PUnit.unit, (1 : R)), (1 : R))
  let v : Vec R [(1 : R), -(1 : R)] := ((PUnit.unit, -(1 : R)), (1 : R))
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((0 : R) + (-(1 : R)) * (1 * 1)) + 1 * (1 * 1) = 0
    rw [CommRing.zero_add, CommRing.one_mul, neg_mul, CommRing.one_mul, CommRing.neg_add_cancel]
  · change ((0 : R) + (-(1 : R)) * ((-(1 : R)) * (-(1 : R)))) + 1 * (1 * 1) = 0
    rw [CommRing.zero_add, neg_mul_neg, CommRing.one_mul, neg_mul, CommRing.one_mul,
        CommRing.neg_add_cancel]
  · have huv : mul (ofVec u) (ofVec v) = ((two R, 0), (0, two R)) := by
      simp only [u, v, ofVec, mul, add, smul, involute, neg, one, zero,
        zero_mul, mul_zero, CommRing.one_mul, CommRing.mul_one,
        CommRing.add_zero, CommRing.zero_add, neg_zero_eq, neg_involutive,
        neg_mul, mul_neg, neg_mul_neg, neg_add_rev]
      rfl
    rw [huv]
    intro hz
    have h0 : two R = 0 := congrArg (fun z => z.1.1) hz
    exact ne_of_lt (zero_lt_two (R := R)) h0.symm
  · rw [l2NormSq_ofVec]
    change ((0 : R) + 1 * 1) + 1 * 1 = two R
    rw [CommRing.zero_add, CommRing.one_mul]; rfl
  · rw [l2NormSq_ofVec]
    change ((0 : R) + (-(1 : R)) * (-(1 : R))) + 1 * 1 = two R
    rw [CommRing.zero_add, neg_mul_neg, CommRing.one_mul]; rfl
  · have huv : mul (ofVec u) (ofVec v) = ((two R, 0), (0, two R)) := by
      simp only [u, v, ofVec, mul, add, smul, involute, neg, one, zero,
        zero_mul, mul_zero, CommRing.one_mul, CommRing.mul_one,
        CommRing.add_zero, CommRing.zero_add, neg_zero_eq, neg_involutive,
        neg_mul, mul_neg, neg_mul_neg, neg_add_rev]
      rfl
    rw [huv]
    simp only [l2NormSq, zero_mul, CommRing.add_zero, CommRing.zero_add]
    unfold eight four two
    rw [CommRing.right_distrib (1 : R) 1 (((1 + 1) * (1 + 1))), CommRing.one_mul]
  · have huq : quadForm u = 0 := by
      change ((0 : R) + (-(1 : R)) * (1 * 1)) + 1 * (1 * 1) = 0
      rw [CommRing.zero_add, CommRing.one_mul, neg_mul, CommRing.one_mul, CommRing.neg_add_cancel]
    rw [ofVec_sq_eq_quadForm, huq, zero_smul_cl, l2NormSq_zero]
  · rw [vec_pair_revNorm]
    have huq : quadForm u = 0 := by
      change ((0 : R) + (-(1 : R)) * (1 * 1)) + 1 * (1 * 1) = 0
      rw [CommRing.zero_add, CommRing.one_mul, neg_mul, CommRing.one_mul, CommRing.neg_add_cancel]
    rw [huq, zero_mul]

/-- Twisted adjoint action `ρ(u)(x) = û x u⁻¹` (where `u⁻¹` is given). -/
def twistedAdjoint {sig : List R} (u x uInv : Cl R sig) : Cl R sig :=
  mul (mul (involute u) x) uInv

/-- Refutation Theorem 2A (Universal Double-Cover Non-Injectivity on ALL `Cl_R(sig)`):
    `1` and `-1` are distinct unit-norm elements (`1 ≠ -1`, `ũ u = 1`, `ū u = 1`, `‖u‖₂² = 1`)
    that induce the IDENTICAL trivial twisted adjoint action on all of `Cl_R(sig)`. -/
theorem refutation_double_cover_kernel (sig : List R) :
    let uPos : Cl R sig := one
    let uNeg : Cl R sig := neg one
    uPos ≠ uNeg ∧
    mul (rev uPos) uPos = one ∧
    mul (rev uNeg) uNeg = one ∧
    mul (conj uPos) uPos = one ∧
    mul (conj uNeg) uNeg = one ∧
    l2NormSq uPos = 1 ∧
    l2NormSq uNeg = 1 ∧
    (∀ x : Cl R sig, twistedAdjoint uPos x uPos = x ∧ twistedAdjoint uNeg x uNeg = x) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, l2NormSq_one, ?_, ?_⟩
  · intro h
    have hs : scalarPart (one : Cl R sig) = scalarPart (neg (one : Cl R sig)) :=
      congrArg scalarPart h
    have hneg1 : scalarPart (neg (one : Cl R sig)) = -(1 : R) := by
      have hsm : neg (one : Cl R sig) = smul (-(1 : R)) one := by
        rw [neg_smul_cl, one_smul_cl]
      rw [hsm, scalarPart_smul, scalarPart_one, CommRing.mul_one]
    rw [scalarPart_one, hneg1] at hs
    exact one_ne_neg_one hs
  · rw [rev_one, one_mul_cl]
  · rw [rev_neg, rev_one, neg_mul_cl, mul_neg_cl, neg_involutive_cl, one_mul_cl]
  · rw [conj_one, one_mul_cl]
  · rw [conj_eq_rev_involute, involute_neg, involute_one, rev_neg, rev_one,
        neg_mul_cl, mul_neg_cl, neg_involutive_cl, one_mul_cl]
  · rw [l2NormSq_neg, l2NormSq_one]
  · intro x
    refine ⟨?_, ?_⟩
    · unfold twistedAdjoint
      rw [involute_one, one_mul_cl, mul_one_cl]
    · unfold twistedAdjoint
      rw [involute_neg, involute_one, neg_mul_cl, one_mul_cl, mul_neg_cl,
          mul_one_cl, neg_involutive_cl]

end OrderedRingRefutations

section ConcreteIntegerAndUnitGroupRefutations

/-- Every 1D linear isometry `f : Int → Int` (`f(x) = c * x` preserving `Q(x) = x²`)
    belongs to `{id, -id}` (so `|O(1)| = 2`), whereas `Cl_{0,1}(ℤ) ≅ ℤ[i]` already has
    4 distinct unit-norm elements `{±1, ±e₁}` (`Pin(0,1) ≅ ℤ/4ℤ`), and `Cl_{0,1}(ℚ) ⊂ ℂ`
    has infinitely many rational Pythagorean units `((k² - 1)/(k² + 1), 2k/(k² + 1))`. -/
theorem refutation_cl01_isometry_mismatch :
    -- (1) Every 1D linear isometry `x ↦ c * x` has `c = 1` or `c = -1` (at most 2 maps):
    (∀ c : Int, (∀ x : Int, (c * x) * (c * x) = x * x) → c = 1 ∨ c = -1) ∧
    -- (2) `Cl_{0,1}(ℤ)` already contains 4 pairwise-distinct unit-norm elements (`X̄ X = 1`, `‖X‖₂² = 1`):
    (∃ u0 u1 u2 u3 : Cl Int (spinSig Int 1),
      u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      mul (conj u0) u0 = one ∧ l2NormSq u0 = 1 ∧
      mul (conj u1) u1 = one ∧ l2NormSq u1 = 1 ∧
      mul (conj u2) u2 = one ∧ l2NormSq u2 = 1 ∧
      mul (conj u3) u3 = one ∧ l2NormSq u3 = 1) ∧
    -- (3) Infinite Pythagorean family on the unit circle of `Cl_{0,1}`:
    -- for every `k ≥ 1`, `X_k = (k² - 1) + (2k) e₁` satisfies `‖X_k‖₂² = (k² + 1)² > 0`
    -- and distinct `1 ≤ k₁ < k₂` define distinct rays `(k₁² - 1)(k₂² + 1) ≠ (k₂² - 1)(k₁² + 1)`:
    (∀ k : Int, 1 ≤ k →
      l2NormSq (sig := spinSig Int 1) (k * k - 1, 2 * k) = (k * k + 1) * (k * k + 1) ∧
      0 < (k * k + 1) * (k * k + 1)) ∧
    (∀ k1 k2 : Int, 1 ≤ k1 → k1 < k2 →
      (k1 * k1 - 1) * (k2 * k2 + 1) ≠ (k2 * k2 - 1) * (k1 * k1 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    have h1 : (c * 1) * (c * 1) = 1 * 1 := hc 1
    rw [Int.mul_one, Int.one_mul] at h1
    by_cases hge : 2 ≤ c
    · exfalso
      have hgt : 4 ≤ c * c := by
        have := Int.mul_le_mul hge hge (by omega) (by omega)
        omega
      omega
    · by_cases hle : c ≤ -2
      · exfalso
        have hnc : 2 ≤ -c := by omega
        have hgt : 4 ≤ (-c) * (-c) := Int.mul_le_mul hnc hnc (by omega) (by omega)
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at hgt
        omega
      · have hcases : c = -1 ∨ c = 0 ∨ c = 1 := by omega
        rcases hcases with rfl | rfl | rfl
        · exact Or.inr rfl
        · exfalso; revert h1; decide
        · exact Or.inl rfl
  · refine ⟨(1, 0), (-1, 0), (0, 1), (0, -1), ?_⟩
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro k hk
    refine ⟨?_, ?_⟩
    · change (k * k - 1) * (k * k - 1) + (2 * k) * (2 * k) = (k * k + 1) * (k * k + 1)
      have hsq : k * k ≥ 1 := Int.mul_le_mul hk hk (by omega) (by omega)
      -- Pure polynomial identity `(t - 1)² + 4 t = (t + 1)²` for `t = k * k`:
      have hid : ∀ t : Int, (t - 1) * (t - 1) + 4 * t = (t + 1) * (t + 1) := fun t => by
        rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
            Int.add_mul, Int.mul_add, Int.mul_add]
        omega
      have h2k : (2 * k) * (2 * k) = 4 * (k * k) := by
        rw [Int.mul_assoc 2 k (2 * k), ← Int.mul_assoc k 2 k,
            Int.mul_comm k 2, Int.mul_assoc 2 k k, ← Int.mul_assoc 2 2 (k * k)]
        rfl
      rw [h2k]
      exact hid (k * k)
    · have hk2 : 0 < k * k + 1 := by
        have := Int.mul_nonneg (by omega : 0 ≤ k) (by omega : 0 ≤ k)
        omega
      exact Int.mul_pos hk2 hk2
  · intro k1 k2 hk1 hlt heq
    -- `(k1² - 1)(k2² + 1) - (k2² - 1)(k1² + 1) = 2 (k1² - k2²) < 0`!
    have hsqlt : k1 * k1 < k2 * k2 := by
      have h1 : k1 * k1 ≤ k1 * k2 := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have h2 : k1 * k2 < k2 * k2 := Int.mul_lt_mul_of_pos_right hlt (by omega)
      omega
    have hid : ∀ a b : Int, (a - 1) * (b + 1) - (b - 1) * (a + 1) = 2 * (a - b) := fun a b => by
      rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.add_mul, Int.mul_add, Int.mul_add]
      have hab : b * a = a * b := Int.mul_comm b a
      omega
    have hdiff := hid (k1 * k1) (k2 * k2)
    omega

/-- Non-versor rational/homogeneous unit element `X = 3 + 4 e₁e₂e₃ ∈ Cl_{3,0}`:
    - `X̃ X = 25 · 1` and `‖X‖₂² = 25` (so `U = X / 5` has `Ũ U = 1` and `‖U‖₂² = 1`),
    - `X` is non-scalar (`∀ s, X ≠ s · 1`), yet untwisted conjugation fixes EVERY vector `v ∈ V`
      (`X v X̃ = 25 v`),
    - Twisted conjugation sends the basis grade-1 vector `e₁ ∈ V` to `-7 e₁ - 24 e₂e₃ ∉ V`! -/
def xUnit30 : Cl Int (eucSig Int 3) :=
  (((3, 0), (0, 0)), ((0, 0), (0, 4)))

def e1Vec30 : Vec Int (eucSig Int 3) :=
  (((PUnit.unit, 0), 0), 1)

theorem refutation_cl30_algebraic_unit_not_pin :
    mul (rev xUnit30) xUnit30 = smul 25 one ∧
    l2NormSq xUnit30 = 25 ∧
    (∀ s : Int, xUnit30 ≠ smul s one) ∧
    (∀ v : Vec Int (eucSig Int 3),
      mul (mul xUnit30 (ofVec v)) (rev xUnit30) = smul 25 (ofVec v)) ∧
    isGradeOne (ofVec e1Vec30) ∧
    ¬ isGradeOne (mul (mul (involute xUnit30) (ofVec e1Vec30)) (rev xUnit30)) := by
  refine ⟨rfl, rfl, ?_, ?_, ofVec_isGradeOne e1Vec30, ?_⟩
  · intro s hs
    have h4 : (4 : Int) = s * 0 := congrArg (fun z => z.2.2.2) hs
    omega
  · intro v
    rcases v with ⟨⟨⟨_, v3⟩, v2⟩, v1⟩
    let b1 : Cl Int (eucSig Int 3) := (((0, 0), (0, 0)), ((1, 0), (0, 0)))
    let b2 : Cl Int (eucSig Int 3) := (((0, 0), (1, 0)), ((0, 0), (0, 0)))
    let b3 : Cl Int (eucSig Int 3) := (((0, 1), (0, 0)), ((0, 0), (0, 0)))
    have hdecomp : ofVec (sig := eucSig Int 3) (((PUnit.unit, v3), v2), v1) =
        add (add (smul v1 b1) (smul v2 b2)) (smul v3 b3) := by
      refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
                      (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)) <;>
        simp [ofVec, add, smul, one, zero, b1, b2, b3,
          Int.mul_zero, Int.mul_one, Int.add_zero, Int.zero_add]
    have hb1 : mul (mul xUnit30 b1) (rev xUnit30) = smul 25 b1 := rfl
    have hb2 : mul (mul xUnit30 b2) (rev xUnit30) = smul 25 b2 := rfl
    have hb3 : mul (mul xUnit30 b3) (rev xUnit30) = smul 25 b3 := rfl
    rw [hdecomp]
    simp only [left_distrib_cl, right_distrib_cl, mul_smul_cl, smul_mul_cl,
      hb1, hb2, hb3, smul_add_cl, ← smul_smul_cl, Int.mul_comm _ (25 : Int)]
  · intro hgrade
    have hval : mul (mul (involute xUnit30) (ofVec e1Vec30)) (rev xUnit30) =
        ((((0, 0), (0, -24)), ((-7, 0), (0, 0))) : Cl Int (eucSig Int 3)) := rfl
    rw [hval] at hgrade
    rcases hgrade.1.2 with ⟨r, hr⟩
    have h24 : (-24 : Int) = r * 0 := congrArg Prod.snd hr
    omega

end ConcreteIntegerAndUnitGroupRefutations

end Cl
end CliffordNormConjecture
