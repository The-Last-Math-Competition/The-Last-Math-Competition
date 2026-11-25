/-
Copyright (c) 2026. All rights reserved.
Formalization of Conjecture 00000007166 in Core Lean 4.19.0 (zero external dependencies).

Module: Conjecture00000007166.Kantorovich
Purpose:
  Complete proof from first principles over any `LinearOrderedField F` of Clause 1:
    1. Exact condition-ratio and AM/HM representations of the Kantorovich constant
       `K(κ) = (κ + 1)^2 / (4κ)` and `K(M/m) = (M + m)^2 / (4Mm) = AM(M,m) / HM(M,m)`.
    2. Exact lower-bound master identity and inequality `1 ≤ Q_A(x)` with equality
       characterization.
    3. Exact upper-bound master identity and Kantorovich inequality
       `Q_A(x) ≤ (M + m)^2 / (4Mm) = K(M/m)` with equality characterization.
    4. Exact tightness / optimality for every dimension `n ≥ 2` and condition ratio
       `κ = M / m ≥ 1`, both for diagonal SPD matrices and for general orthogonally
       diagonalizable SPD matrices `A = Q diag(λ) Q^T`.
-/

import Conjecture00000007166.OrderedField

namespace Conjecture00000007166

section FiniteSums

variable {F : Type u} [LinearOrderedField F]

/-- Finite sum `∑_{i=0}^{n-1} f(i)` over `Fin n` in any `LinearOrderedField`. -/
def finSum : (n : Nat) → (Fin n → F) → F
  | 0, _ => 0
  | n + 1, f =>
    finSum n (fun i => f ⟨i.val, by omega⟩) + f ⟨n, by omega⟩

theorem finSum_congr {n : Nat} {f g : Fin n → F} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold finSum
    rw [ih (fun i => h ⟨i.val, by omega⟩), h ⟨n, by omega⟩]

theorem finSum_eq_zero (n : Nat) {f : Fin n → F} (hf : ∀ i, f i = 0) :
    finSum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold finSum
    rw [ih (fun i => hf ⟨i.val, by omega⟩), hf ⟨n, by omega⟩, lofAddZero]

theorem finSum_add (n : Nat) (f g : Fin n → F) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero =>
    unfold finSum
    rw [lofAddZero]
  | succ n ih =>
    unfold finSum
    rw [ih]
    calc
      (finSum n (fun i => f ⟨i.val, by omega⟩) + finSum n (fun i => g ⟨i.val, by omega⟩)) +
          (f ⟨n, by omega⟩ + g ⟨n, by omega⟩)
        = finSum n (fun i => f ⟨i.val, by omega⟩) +
          (finSum n (fun i => g ⟨i.val, by omega⟩) + (f ⟨n, by omega⟩ + g ⟨n, by omega⟩)) :=
            lofAddAssoc _ _ _
      _ = finSum n (fun i => f ⟨i.val, by omega⟩) +
          (f ⟨n, by omega⟩ + (finSum n (fun i => g ⟨i.val, by omega⟩) + g ⟨n, by omega⟩)) := by
            congr 1
            rw [← lofAddAssoc, lofAddComm (finSum n _) (f ⟨n, by omega⟩), lofAddAssoc]
      _ = (finSum n (fun i => f ⟨i.val, by omega⟩) + f ⟨n, by omega⟩) +
          (finSum n (fun i => g ⟨i.val, by omega⟩) + g ⟨n, by omega⟩) := by
            rw [← lofAddAssoc]

theorem finSum_neg (n : Nat) (f : Fin n → F) :
    finSum n (fun i => -f i) = -finSum n f := by
  induction n with
  | zero =>
    unfold finSum
    exact neg_zero.symm
  | succ n ih =>
    unfold finSum
    rw [ih, neg_add_rev]

theorem finSum_sub (n : Nat) (f g : Fin n → F) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  have h : finSum n (fun i => f i - g i) = finSum n (fun i => f i + -g i) :=
    finSum_congr (fun i => lofSubEqAddNeg (f i) (g i))
  rw [h, finSum_add, finSum_neg, ← lofSubEqAddNeg]

theorem finSum_mul_left (n : Nat) (c : F) (f : Fin n → F) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero =>
    unfold finSum
    exact (mul_zero c).symm
  | succ n ih =>
    unfold finSum
    rw [ih, lofLeftDistrib]

theorem finSum_mul_right (n : Nat) (f : Fin n → F) (c : F) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero =>
    unfold finSum
    exact (zero_mul c).symm
  | succ n ih =>
    unfold finSum
    rw [ih, lofRightDistrib]

theorem finSum_div_const (n : Nat) (f : Fin n → F) (c : F) :
    finSum n (fun i => f i / c) = finSum n f / c := by
  have h : finSum n (fun i => f i / c) = finSum n (fun i => f i * c⁻¹) :=
    finSum_congr (fun i => lofDivEqMulInv (f i) c)
  rw [h, finSum_mul_right, ← lofDivEqMulInv]

theorem finSum_nonneg (n : Nat) {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  induction n with
  | zero =>
    unfold finSum
    exact LinearOrderedField.le_refl 0
  | succ n ih =>
    unfold finSum
    have h0 := add_le_add (ih (fun i => hf ⟨i.val, by omega⟩)) (hf ⟨n, by omega⟩)
    rw [lofAddZero] at h0
    exact h0

theorem finSum_le_finSum (n : Nat) {f g : Fin n → F} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  rw [← sub_nonneg, ← finSum_sub]
  exact finSum_nonneg n (fun i => sub_nonneg.mpr (h i))

theorem finSum_eq_zero_iff_of_nonneg (n : Nat) {f : Fin n → F} (hf : ∀ i, 0 ≤ f i) :
    finSum n f = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · induction n with
    | zero =>
      intro _ i
      exact Fin.elim0 i
    | succ n ih =>
      unfold finSum
      intro hsum
      have h1 : 0 ≤ finSum n (fun i => f ⟨i.val, by omega⟩) :=
        finSum_nonneg n (fun i => hf ⟨i.val, by omega⟩)
      have h2 : 0 ≤ f ⟨n, by omega⟩ := hf ⟨n, by omega⟩
      have hlast : f ⟨n, by omega⟩ = 0 := by
        rcases lt_trichotomy 0 (f ⟨n, by omega⟩) with hpos | heq | hneg
        · have hgt := add_lt_add_of_le_of_lt h1 hpos
          rw [lofAddZero, hsum] at hgt
          exact False.elim (lt_irrefl 0 hgt)
        · exact heq.symm
        · exact False.elim (not_le_of_lt hneg h2)
      have hinit : finSum n (fun i => f ⟨i.val, by omega⟩) = 0 := by
        rw [hlast, lofAddZero] at hsum
        exact hsum
      have hall := ih (fun i => hf ⟨i.val, by omega⟩) hinit
      intro i
      by_cases hi : i.val = n
      · have hieq : i = ⟨n, by omega⟩ := Fin.ext hi
        rw [hieq]
        exact hlast
      · have hilt : i.val < n := by have := i.isLt; omega
        have hieq : i = ⟨i.val, by omega⟩ := Fin.ext rfl
        rw [hieq]
        exact hall ⟨i.val, hilt⟩
  · exact finSum_eq_zero n

theorem finSum_single : ∀ (n : Nat) (k : Fin n) (c : F),
    finSum n (fun i => if i = k then c else 0) = c
  | 0, k, _ => Fin.elim0 k
  | n + 1, k, c => by
    unfold finSum
    dsimp only
    by_cases hk : k.val = n
    · have hkeq : (⟨n, by omega⟩ : Fin (n + 1)) = k := Fin.ext hk.symm
      rw [if_pos hkeq]
      have hzero : finSum n (fun i : Fin n =>
          if (⟨i.val, by omega⟩ : Fin (n + 1)) = k then c else 0) = 0 := by
        apply finSum_eq_zero
        intro i
        rw [if_neg]
        intro heq
        have hval : i.val = k.val := congrArg Fin.val heq
        have hi := i.isLt
        omega
      rw [hzero, lofZeroAdd]
    · have hklt : k.val < n := by have := k.isLt; omega
      have hkne : (⟨n, by omega⟩ : Fin (n + 1)) ≠ k := by
        intro heq
        exact hk (congrArg Fin.val heq).symm
      rw [if_neg hkne, lofAddZero]
      have hcong : finSum n (fun i : Fin n =>
          if (⟨i.val, by omega⟩ : Fin (n + 1)) = k then c else 0) =
          finSum n (fun i : Fin n => if i = ⟨k.val, hklt⟩ then c else 0) := by
        apply finSum_congr
        intro i
        by_cases hi : i.val = k.val
        · have h1 : (⟨i.val, by omega⟩ : Fin (n + 1)) = k := Fin.ext hi
          have h2 : i = ⟨k.val, hklt⟩ := Fin.ext hi
          rw [if_pos h1, if_pos h2]
        · have h1 : (⟨i.val, by omega⟩ : Fin (n + 1)) ≠ k :=
            fun h => hi (congrArg Fin.val h)
          have h2 : i ≠ ⟨k.val, hklt⟩ :=
            fun h => hi (congrArg Fin.val h)
          rw [if_neg h1, if_neg h2]
      rw [hcong, finSum_single n ⟨k.val, hklt⟩ c]

theorem finSum_comm (m n : Nat) (h : Fin m → Fin n → F) :
    finSum m (fun i => finSum n (fun j => h i j)) =
    finSum n (fun j => finSum m (fun i => h i j)) := by
  induction m with
  | zero =>
    change (0 : F) = finSum n (fun _ => (0 : F))
    exact (finSum_eq_zero n (fun _ => rfl)).symm
  | succ m ih =>
    change finSum m (fun i => finSum n (fun j => h ⟨i.val, by omega⟩ j)) +
        finSum n (fun j => h ⟨m, by omega⟩ j) =
      finSum n (fun j => finSum m (fun i => h ⟨i.val, by omega⟩ j) + h ⟨m, by omega⟩ j)
    rw [ih, ← finSum_add]

end FiniteSums

/-!
### Classical Means, Kantorovich Constant, and Quadratic Forms
-/

section Definitions

variable {F : Type u} [LinearOrderedField F]

/-- Arithmetic mean `AM(M, m) = (M + m) / 2`. -/
def arithmeticMean (M m : F) : F := (M + m) / twoF

/-- Harmonic mean `HM(M, m) = 2 M m / (M + m)`. -/
def harmonicMean (M m : F) : F := (twoF * M * m) / (M + m)

/-- The Kantorovich multiplicative bound as an explicit function of condition ratio `κ`:
    `K(κ) = (κ + 1)^2 / (4κ)`. -/
def kantorovichConst (κ : F) : F := ((κ + 1) * (κ + 1)) / (fourF * κ)

/-- The reciprocal (Wielandt-Kantorovich) constant `R(κ) = 4κ / (κ + 1)^2`. -/
def reciprocalKantorovichConst (κ : F) : F := (fourF * κ) / ((κ + 1) * (κ + 1))

/-- Euclidean squared norm `‖x‖^2 = ∑_i x_i^2`. -/
def normSq (n : Nat) (x : Fin n → F) : F :=
  finSum n (fun i => x i * x i)

/-- Diagonal quadratic form `⟨diag(λ) x, x⟩ = ∑_i λ_i x_i^2`. -/
def quadFormDiag (n : Nat) (lam x : Fin n → F) : F :=
  finSum n (fun i => lam i * (x i * x i))

/-- Kantorovich quotient for `A = diag(λ)`:
    `Q_A(x) = (⟨Ax, x⟩ ⟨A⁻¹x, x⟩) / ‖x‖^4`. -/
def kantorovichQuotient (n : Nat) (lam x : Fin n → F) : F :=
  (quadFormDiag n lam x * quadFormDiag n (fun i => (lam i)⁻¹) x) /
    (normSq n x * normSq n x)

/-- Standard basis vector `e_k`. -/
def basisVec (n : Nat) (k : Fin n) : Fin n → F :=
  fun i => if i = k then 1 else 0

/-- Equal-amplitude superposition `e_j + e_k` on two coordinates. -/
def pairVec (n : Nat) (j k : Fin n) : Fin n → F :=
  fun i => (if i = j then (1 : F) else 0) + (if i = k then (1 : F) else 0)

/-- General matrix quadratic form `⟨Ax, x⟩ = ∑_r ∑_s A_{r,s} x_s x_r`. -/
def matQuadForm (n : Nat) (A : Fin n → Fin n → F) (x : Fin n → F) : F :=
  finSum n (fun r => finSum n (fun s => A r s * x s * x r))

/-- General matrix Kantorovich quotient `(⟨Ax, x⟩ ⟨A⁻¹x, x⟩) / ‖x‖^4`. -/
def matrixKantorovichQuotient (n : Nat) (A A_inv : Fin n → Fin n → F) (x : Fin n → F) : F :=
  (matQuadForm n A x * matQuadForm n A_inv x) / (normSq n x * normSq n x)

/-- Orthogonality of `Q ∈ F^{n×n}`: `Q^T Q = I_n` and `Q Q^T = I_n`. -/
structure IsOrthogonal (n : Nat) (Qmat : Fin n → Fin n → F) : Prop where
  col_ortho : ∀ i j : Fin n,
    finSum n (fun r => Qmat r i * Qmat r j) = if i = j then 1 else 0
  row_ortho : ∀ r s : Fin n,
    finSum n (fun i => Qmat r i * Qmat s i) = if r = s then 1 else 0

/-- Symmetric matrix `A = Q diag(λ) Q^T` constructed from eigenbasis `Q` and spectrum `λ`. -/
def orthoSPDMat (n : Nat) (Qmat : Fin n → Fin n → F) (lam : Fin n → F) :
    Fin n → Fin n → F :=
  fun r s => finSum n (fun i => Qmat r i * lam i * Qmat s i)

/-- Matrix product `(A B)_{r,t} = ∑_s A_{r,s} B_{s,t}`. -/
def matMul (n : Nat) (A B : Fin n → Fin n → F) : Fin n → Fin n → F :=
  fun r t => finSum n (fun s => A r s * B s t)

end Definitions

/-!
### Clause 1 — Explicit Condition-Ratio Identities & Master Kantorovich Proof
-/

section Clause1Proofs

variable {F : Type u} [LinearOrderedField F]

/-- `K(M/m) = (M + m)^2 / (4 M m)` for `m ≠ 0`. -/
theorem kantorovichConst_ratio {M m : F} (hm : m ≠ 0) :
    kantorovichConst (M / m) = ((M + m) * (M + m)) / (fourF * M * m) := by
  unfold kantorovichConst
  have h1 : M / m + 1 = (M + m) / m := by
    rw [add_div, div_self hm]
  rw [h1]
  have hnum : ((M + m) / m) * ((M + m) / m) = ((M + m) * (M + m)) / (m * m) :=
    div_mul_div (M + m) m (M + m) m hm hm
  have hden : fourF * (M / m) = (fourF * M) / m :=
    mul_div_assoc fourF M m
  rw [hnum, hden]
  by_cases hM : M = 0
  · rw [hM, lofZeroAdd, mul_zero, zero_mul, zero_div]
    rw [lofDivEqMulInv ((m * m) / (m * m)) 0,
        lofDivEqMulInv (m * m) 0,
        LinearOrderedField.inv_zero, mul_zero, mul_zero]
  · have h4M : fourF * M ≠ 0 := mul_ne_zero fourF_ne_zero hM
    have hmm : m * m ≠ 0 := mul_ne_zero hm hm
    rw [div_div_div_eq ((M + m) * (M + m)) (m * m) (fourF * M) m hmm h4M hm]
    apply (div_eq_div_iff (mul_ne_zero hmm h4M) (mul_ne_zero h4M hm)).mpr
    calc
      ((M + m) * (M + m) * m) * (fourF * M * m)
        = ((M + m) * (M + m)) * (m * (fourF * M * m)) := lofMulAssoc _ m _
      _ = ((M + m) * (M + m)) * ((m * m) * (fourF * M)) := by
          congr 1
          rw [lofMulComm (fourF * M) m, ← lofMulAssoc m m (fourF * M)]

/-- `K(M/m) = AM(M, m) / HM(M, m)` for `0 < m` and `0 < M`. -/
theorem kantorovichConst_eq_am_div_hm {M m : F} (hm : 0 < m) (hM : 0 < M) :
    kantorovichConst (M / m) = arithmeticMean M m / harmonicMean M m := by
  rw [kantorovichConst_ratio (ne_of_gt hm)]
  unfold arithmeticMean harmonicMean
  have hMm_pos : 0 < M + m := by
    have h := add_lt_add hM hm
    rw [lofAddZero] at h
    exact h
  have hMm_ne : M + m ≠ 0 := ne_of_gt hMm_pos
  have h2Mm_ne : twoF * M * m ≠ 0 :=
    mul_ne_zero (mul_ne_zero twoF_ne_zero (ne_of_gt hM)) (ne_of_gt hm)
  rw [div_div_div_eq (M + m) twoF (twoF * M * m) (M + m) twoF_ne_zero h2Mm_ne hMm_ne]
  congr 1
  rw [fourF_eq_two_mul_two]
  calc
    (twoF * twoF) * M * m = twoF * (twoF * M) * m := lofMulAssoc twoF twoF M ▸ rfl
    _ = twoF * (twoF * M * m) := lofMulAssoc twoF (twoF * M) m

/-- Lower-bound pointwise algebraic identity:
    `w * (λ - S)^2 / λ = w * λ - 2 * S * w + S^2 * (w / λ)`. -/
theorem lower_summand_identity (w lam S : F) (hlam : lam ≠ 0) :
    (w * ((lam - S) * (lam - S))) / lam =
    w * lam - twoF * S * w + (S * S) * (w / lam) := by
  apply (div_eq_iff hlam).mpr
  calc
    w * ((lam - S) * (lam - S))
      = w * (lam * lam - twoF * S * lam + S * S) := by
        congr 1
        calc
          (lam - S) * (lam - S)
            = lam * (lam - S) - S * (lam - S) := sub_mul lam S (lam - S)
          _ = (lam * lam - lam * S) - (S * lam - S * S) := by
              rw [mul_sub, mul_sub]
          _ = (lam * lam - S * lam) + S * S - S * lam := by
              rw [lofMulComm lam S, sub_sub_eq_add_sub]
          _ = lam * lam - S * lam - S * lam + S * S := by
              rw [lofSubEqAddNeg (lam * lam - S * lam + S * S) (S * lam),
                  lofAddAssoc (lam * lam - S * lam) (S * S) (-(S * lam)),
                  lofAddComm (S * S) (-(S * lam)),
                  ← lofAddAssoc, ← lofSubEqAddNeg]
          _ = lam * lam - (S * lam + S * lam) + S * S := by
              rw [sub_sub]
          _ = lam * lam - twoF * S * lam + S * S := by
              rw [lofMulAssoc twoF S lam, twoF_mul (S * lam)]
    _ = w * (lam * lam) - w * (twoF * S * lam) + w * (S * S) := by
        rw [lofLeftDistrib, mul_sub]
    _ = (w * lam) * lam - (twoF * S * w) * lam + ((S * S) * (w / lam)) * lam := by
        congr 1
        · congr 1
          · rw [lofMulAssoc]
          · rw [lofMulComm w (twoF * S * lam), lofMulAssoc (twoF * S) lam w,
                lofMulComm lam w, ← lofMulAssoc (twoF * S) w lam]
        · calc
            w * (S * S) = (S * S) * w := lofMulComm w (S * S)
            _ = (S * S) * ((w / lam) * lam) := by rw [div_mul_cancel w hlam]
            _ = ((S * S) * (w / lam)) * lam := (lofMulAssoc (S * S) (w / lam) lam).symm
    _ = (w * lam - twoF * S * w + (S * S) * (w / lam)) * lam := by
        rw [lofRightDistrib, sub_mul]

/-- **Lower-Bound Master Identity**:
    For weights `∑ w_i = 1` and `λ_i ≠ 0`, setting `S = ∑ w_i λ_i` and `T = ∑ w_i / λ_i`,
    `S * (S * T - 1) = ∑ w_i (λ_i - S)^2 / λ_i`. -/
theorem kantorovich_lower_master_identity (n : Nat) (w lam : Fin n → F)
    (hw_sum : finSum n w = 1) (hlam_ne : ∀ i, lam i ≠ 0) :
    let S := finSum n (fun i => w i * lam i)
    let T := finSum n (fun i => w i / lam i)
    S * (S * T - 1) =
      finSum n (fun i => (w i * ((lam i - S) * (lam i - S))) / lam i) := by
  intro S T
  have hcong :
      finSum n (fun i => (w i * ((lam i - S) * (lam i - S))) / lam i) =
      finSum n (fun i => w i * lam i - twoF * S * w i + (S * S) * (w i / lam i)) :=
    finSum_congr (fun i => lower_summand_identity (w i) (lam i) S (hlam_ne i))
  rw [hcong, finSum_add, finSum_sub, finSum_mul_left, finSum_mul_left, hw_sum, lofMulOne]
  change S * (S * T - 1) = S - twoF * S + (S * S) * T
  calc
    S * (S * T - 1) = S * (S * T) - S * 1 := mul_sub S (S * T) 1
    _ = (S * S) * T - S := by rw [← lofMulAssoc S S T, lofMulOne]
    _ = -(S) + (S * S) * T := by rw [lofSubEqAddNeg, lofAddComm]
    _ = (S - (S + S)) + (S * S) * T := by
        congr 1
        calc
          -S = 0 + -S := (lofZeroAdd (-S)).symm
          _ = (S - S) + -S := by rw [sub_self]
          _ = S - S - S := (lofSubEqAddNeg (S - S) S).symm
          _ = S - (S + S) := sub_sub S S S
    _ = S - twoF * S + (S * S) * T := by rw [twoF_mul]

/-- Weighted mean `S = ∑ w_i λ_i` satisfies `m ≤ S` whenever `w_i ≥ 0`, `∑ w_i = 1`, `m ≤ λ_i`. -/
theorem weighted_sum_ge_min (n : Nat) (w lam : Fin n → F) {m : F}
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : finSum n w = 1) (hm_le : ∀ i, m ≤ lam i) :
    m ≤ finSum n (fun i => w i * lam i) := by
  calc
    m = 1 * m := (lofOneMul m).symm
    _ = finSum n w * m := by rw [hw_sum]
    _ = finSum n (fun i => w i * m) := (finSum_mul_right n w m).symm
    _ ≤ finSum n (fun i => w i * lam i) :=
        finSum_le_finSum n (fun i => mul_le_mul_of_nonneg_left (hm_le i) (hw_nonneg i))

/-- Weighted Kantorovich lower bound `1 ≤ (∑ w_i λ_i)(∑ w_i / λ_i)` and equality condition. -/
theorem weighted_kantorovich_lower (n : Nat) (w lam : Fin n → F) {m : F}
    (hm_pos : 0 < m) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : finSum n w = 1)
    (hm_le : ∀ i, m ≤ lam i) :
    1 ≤ finSum n (fun i => w i * lam i) * finSum n (fun i => w i / lam i) := by
  let S := finSum n (fun i => w i * lam i)
  let T := finSum n (fun i => w i / lam i)
  have hS_pos : 0 < S := lt_of_lt_of_le hm_pos (weighted_sum_ge_min n w lam hw_nonneg hw_sum hm_le)
  have hlam_pos : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le hm_pos (hm_le i)
  have hid := kantorovich_lower_master_identity n w lam hw_sum (fun i => ne_of_gt (hlam_pos i))
  have hrhs : 0 ≤ finSum n (fun i => (w i * ((lam i - S) * (lam i - S))) / lam i) := by
    apply finSum_nonneg
    intro i
    exact div_nonneg (mul_nonneg (hw_nonneg i) (sq_nonneg (lam i - S))) (le_of_lt (hlam_pos i))
  rw [← hid] at hrhs
  have h0 : S * 0 ≤ S * (S * T - 1) := by
    rw [mul_zero]
    exact hrhs
  have hsub : 0 ≤ S * T - 1 := le_of_mul_le_mul_left hS_pos h0
  exact sub_nonneg.mp hsub

/-- Exact equality characterization for the lower bound `S * T = 1`. -/
theorem weighted_kantorovich_lower_eq_iff (n : Nat) (w lam : Fin n → F) {m : F}
    (hm_pos : 0 < m) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : finSum n w = 1)
    (hm_le : ∀ i, m ≤ lam i) :
    let S := finSum n (fun i => w i * lam i)
    let T := finSum n (fun i => w i / lam i)
    S * T = 1 ↔ ∀ i, 0 < w i → lam i = S := by
  intro S T
  have hS_pos : 0 < S := lt_of_lt_of_le hm_pos (weighted_sum_ge_min n w lam hw_nonneg hw_sum hm_le)
  have hlam_pos : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le hm_pos (hm_le i)
  have hid := kantorovich_lower_master_identity n w lam hw_sum (fun i => ne_of_gt (hlam_pos i))
  have hterm_nonneg : ∀ i, 0 ≤ (w i * ((lam i - S) * (lam i - S))) / lam i :=
    fun i => div_nonneg (mul_nonneg (hw_nonneg i) (sq_nonneg (lam i - S))) (le_of_lt (hlam_pos i))
  constructor
  · intro heq
    have hzero : finSum n (fun i => (w i * ((lam i - S) * (lam i - S))) / lam i) = 0 := by
      rw [← hid]
      change S * (S * T - 1) = 0
      rw [heq, sub_self, mul_zero]
    have hall := (finSum_eq_zero_iff_of_nonneg n hterm_nonneg).mp hzero
    intro i hwi
    have hi := hall i
    have hnum : w i * ((lam i - S) * (lam i - S)) = 0 := by
      have hm := (div_eq_iff (ne_of_gt (hlam_pos i))).mp hi
      rw [zero_mul] at hm
      exact hm
    rcases mul_eq_zero.mp hnum with hwz | hsq
    · exact False.elim (ne_of_gt hwi hwz)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hall
    have hzero : finSum n (fun i => (w i * ((lam i - S) * (lam i - S))) / lam i) = 0 := by
      apply finSum_eq_zero
      intro i
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul, zero_div]
      · have hwpos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
        rw [hall i hwpos, sub_self, zero_mul, mul_zero, zero_div]
    change S * (S * T - 1) = _ at hid
    rw [hzero] at hid
    rcases mul_eq_zero.mp hid with hSz | hsub
    · exact False.elim (ne_of_gt hS_pos hSz)
    · exact sub_eq_zero.mp hsub

/-- Upper-bound pointwise algebraic identity:
    `w * (M - λ)(λ - m) / (M m λ) = (w * (M + m) - w * λ) / (M m) - w / λ`. -/
theorem upper_summand_identity (w lam M m : F)
    (hM : M ≠ 0) (hm : m ≠ 0) (hlam : lam ≠ 0) :
    (w * ((M - lam) * (lam - m))) / (M * m * lam) =
    (w * (M + m) - w * lam) / (M * m) - w / lam := by
  have hMm : M * m ≠ 0 := mul_ne_zero hM hm
  have hMml : M * m * lam ≠ 0 := mul_ne_zero hMm hlam
  apply (div_eq_iff hMml).mpr
  calc
    w * ((M - lam) * (lam - m))
      = w * ((M + m - lam) * lam - M * m) := by
        congr 1
        calc
          (M - lam) * (lam - m)
            = M * (lam - m) - lam * (lam - m) := sub_mul M lam (lam - m)
          _ = (M * lam - M * m) - (lam * lam - lam * m) := by
              rw [mul_sub, mul_sub]
          _ = M * lam - M * m + lam * m - lam * lam := by
              rw [sub_sub_eq_add_sub]
          _ = M * lam + m * lam - lam * lam - M * m := by
              rw [lofMulComm lam m,
                  lofSubEqAddNeg (M * lam) (M * m),
                  lofAddAssoc (M * lam) (-(M * m)) (m * lam),
                  lofAddComm (-(M * m)) (m * lam),
                  ← lofAddAssoc (M * lam) (m * lam) (-(M * m)),
                  lofSubEqAddNeg (M * lam + m * lam + -(M * m)) (lam * lam),
                  lofAddAssoc (M * lam + m * lam) (-(M * m)) (-(lam * lam)),
                  lofAddComm (-(M * m)) (-(lam * lam)),
                  ← lofAddAssoc, ← lofSubEqAddNeg, ← lofSubEqAddNeg]
          _ = (M + m - lam) * lam - M * m := by
              rw [sub_mul, lofRightDistrib]
    _ = (w * ((M + m) - lam)) * lam - w * (M * m) := by
        rw [mul_sub, ← lofMulAssoc]
    _ = (w * (M + m) - w * lam) * lam - w * (M * m) := by
        rw [mul_sub]
    _ = (((w * (M + m) - w * lam) / (M * m)) * (M * m)) * lam -
        ((w / lam) * lam) * (M * m) := by
        rw [div_mul_cancel _ hMm, div_mul_cancel w hlam]
    _ = ((w * (M + m) - w * lam) / (M * m)) * (M * m * lam) -
        (w / lam) * (M * m * lam) := by
        congr 1
        · exact lofMulAssoc _ (M * m) lam
        · rw [lofMulAssoc (w / lam) lam (M * m), lofMulComm lam (M * m)]
    _ = ((w * (M + m) - w * lam) / (M * m) - w / lam) * (M * m * lam) := by
        rw [sub_mul]

/-- Completing-the-square polynomial identity at the heart of Kantorovich's inequality:
    `(M + m)^2 - 4 M m S T = (2S - (M + m))^2 + 4 S ((M + m - S) - M m T)`. -/
private theorem kantorovich_square_poly (M m S T : F) :
    (M + m) * (M + m) - fourF * M * m * (S * T) =
    (twoF * S - (M + m)) * (twoF * S - (M + m)) +
      fourF * S * (M + m - S) - fourF * M * m * (S * T) := by
  congr 1
  let A := M + m
  change A * A = (twoF * S - A) * (twoF * S - A) + fourF * S * (A - S)
  have h1 : (twoF * S - A) * (twoF * S - A) =
      (twoF * S) * (twoF * S) - fourF * S * A + A * A := by
    calc
      (twoF * S - A) * (twoF * S - A)
        = (twoF * S) * (twoF * S - A) - A * (twoF * S - A) := sub_mul _ _ _
      _ = ((twoF * S) * (twoF * S) - (twoF * S) * A) - (A * (twoF * S) - A * A) := by
          rw [mul_sub, mul_sub]
      _ = (twoF * S) * (twoF * S) - (twoF * S) * A + A * A - (twoF * S) * A := by
          rw [lofMulComm A (twoF * S), sub_sub_eq_add_sub]
      _ = (twoF * S) * (twoF * S) - (twoF * S) * A - (twoF * S) * A + A * A := by
          rw [lofSubEqAddNeg (_ + A * A) _,
              lofAddAssoc _ (A * A) _, lofAddComm (A * A) _,
              ← lofAddAssoc, ← lofSubEqAddNeg]
      _ = (twoF * S) * (twoF * S) - ((twoF * S) * A + (twoF * S) * A) + A * A := by
          rw [sub_sub]
      _ = (twoF * S) * (twoF * S) - fourF * S * A + A * A := by
          congr 2
          rw [← twoF_mul ((twoF * S) * A), ← lofMulAssoc twoF (twoF * S) A,
              ← lofMulAssoc twoF twoF S, ← fourF_eq_two_mul_two]
  have h2 : fourF * S * (A - S) = fourF * S * A - (twoF * S) * (twoF * S) := by
    rw [mul_sub]
    congr 1
    calc
      fourF * S * S = (twoF * twoF) * S * S := by rw [fourF_eq_two_mul_two]
      _ = twoF * (twoF * S) * S := by rw [lofMulAssoc twoF twoF S]
      _ = (twoF * S) * twoF * S := by rw [lofMulComm twoF (twoF * S)]
      _ = (twoF * S) * (twoF * S) := lofMulAssoc (twoF * S) twoF S
  rw [h1, h2]
  calc
    A * A = 0 + A * A := (lofZeroAdd (A * A)).symm
    _ = (fourF * S * A - fourF * S * A) + A * A := by rw [sub_self]
    _ = ((twoF * S) * (twoF * S) - fourF * S * A + A * A) +
        (fourF * S * A - (twoF * S) * (twoF * S)) := by
        let X := (twoF * S) * (twoF * S)
        let Y := fourF * S * A
        let Z := A * A
        change (Y - Y) + Z = (X - Y + Z) + (Y - X)
        calc
          (Y - Y) + Z = Z := by rw [sub_self, lofZeroAdd]
          _ = Z + 0 := (lofAddZero Z).symm
          _ = Z + (0 + 0) := by rw [lofAddZero 0]
          _ = Z + ((X - X) + (Y - Y)) := by rw [sub_self X, sub_self Y]
          _ = (X - Y + Z) + (Y - X) := by
              rw [lofSubEqAddNeg, lofSubEqAddNeg, lofSubEqAddNeg, lofSubEqAddNeg]
              calc
                Z + ((X + -X) + (Y + -Y))
                  = Z + (X + (-X + (Y + -Y))) := by rw [lofAddAssoc X (-X) (Y + -Y)]
                _ = Z + (X + (-Y + (Y + -X))) := by
                    congr 2
                    rw [← lofAddAssoc (-X) Y (-Y), lofAddComm (-X) Y,
                        lofAddAssoc Y (-X) (-Y), lofAddComm (-X) (-Y),
                        ← lofAddAssoc Y (-Y) (-X), lofAddComm Y (-Y), lofAddAssoc]
                _ = (X + -Y + Z) + (Y + -X) := by
                    rw [← lofAddAssoc X (-Y) (Y + -X),
                        ← lofAddAssoc Z (X + -Y) (Y + -X),
                        lofAddComm Z (X + -Y)]

/-- **Upper-Bound Master Identity (Kantorovich Decomposition)**:
    For weights `∑ w_i = 1` and `m, M, λ_i ≠ 0`, setting `S = ∑ w_i λ_i` and `T = ∑ w_i / λ_i`:
    `(M + m)^2 / (4 M m) - S * T
      = (2 S - (M + m))^2 / (4 M m) + S * ∑ w_i (M - λ_i)(λ_i - m) / (M m λ_i)`. -/
theorem kantorovich_upper_master_identity (n : Nat) (w lam : Fin n → F) {M m : F}
    (hM : M ≠ 0) (hm : m ≠ 0) (hw_sum : finSum n w = 1) (hlam_ne : ∀ i, lam i ≠ 0) :
    let S := finSum n (fun i => w i * lam i)
    let T := finSum n (fun i => w i / lam i)
    ((M + m) * (M + m)) / (fourF * M * m) - S * T =
      ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
        S * finSum n (fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)) := by
  intro S T
  have hMm : M * m ≠ 0 := mul_ne_zero hM hm
  have h4Mm : fourF * M * m ≠ 0 := mul_ne_zero (mul_ne_zero fourF_ne_zero hM) hm
  have hsum_id :
      finSum n (fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)) =
      (M + m - S) / (M * m) - T := by
    have hc :
        finSum n (fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)) =
        finSum n (fun i => (w i * (M + m) - w i * lam i) / (M * m) - w i / lam i) :=
      finSum_congr (fun i => upper_summand_identity (w i) (lam i) M m hM hm (hlam_ne i))
    rw [hc, finSum_sub, finSum_div_const, finSum_sub, finSum_mul_right, hw_sum, lofOneMul]
  rw [hsum_id]
  change ((M + m) * (M + m)) / (fourF * M * m) - S * T =
    ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
      S * ((M + m - S) / (M * m) - T)
  have hlhs :
      ((M + m) * (M + m)) / (fourF * M * m) - S * T =
      ((M + m) * (M + m) - fourF * M * m * (S * T)) / (fourF * M * m) := by
    rw [sub_div, mul_div_cancel_left (S * T) h4Mm]
  have hrhs :
      ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
        S * ((M + m - S) / (M * m) - T) =
      ((twoF * S - (M + m)) * (twoF * S - (M + m)) +
        fourF * S * (M + m - S) - fourF * M * m * (S * T)) / (fourF * M * m) := by
    have hmid :
        S * ((M + m - S) / (M * m)) =
        (fourF * S * (M + m - S)) / (fourF * M * m) := by
      rw [mul_div_assoc S (M + m - S) (M * m)]
      apply (div_eq_div_iff hMm h4Mm).mpr
      calc
        (S * (M + m - S)) * (fourF * M * m)
          = (S * (M + m - S)) * (fourF * (M * m)) := by rw [lofMulAssoc fourF M m]
        _ = fourF * (S * (M + m - S)) * (M * m) := by
            rw [← lofMulAssoc, lofMulComm _ fourF]
        _ = (fourF * S * (M + m - S)) * (M * m) := by rw [← lofMulAssoc fourF S _]
    calc
      ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
          S * ((M + m - S) / (M * m) - T)
        = ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
          ((fourF * S * (M + m - S)) / (fourF * M * m) -
           (fourF * M * m * (S * T)) / (fourF * M * m)) := by
          rw [mul_sub S ((M + m - S) / (M * m)) T, hmid,
              mul_div_cancel_left (S * T) h4Mm]
      _ = (((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) +
           (fourF * S * (M + m - S)) / (fourF * M * m)) -
          (fourF * M * m * (S * T)) / (fourF * M * m) := by
          let P := ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m)
          let Q1 := (fourF * S * (M + m - S)) / (fourF * M * m)
          let R1 := (fourF * M * m * (S * T)) / (fourF * M * m)
          change P + (Q1 - R1) = (P + Q1) - R1
          rw [lofSubEqAddNeg Q1 R1, ← lofAddAssoc P Q1 (-R1), ← lofSubEqAddNeg (P + Q1) R1]
      _ = ((twoF * S - (M + m)) * (twoF * S - (M + m)) +
            fourF * S * (M + m - S) - fourF * M * m * (S * T)) / (fourF * M * m) := by
          rw [← add_div, ← sub_div]
  rw [hlhs, hrhs, kantorovich_square_poly M m S T]

/-- **Weighted Kantorovich Upper Bound**:
    For `0 < m ≤ λ_i ≤ M` and probability weights `w_i ≥ 0, ∑ w_i = 1`:
    `(∑ w_i λ_i)(∑ w_i / λ_i) ≤ (M + m)^2 / (4 M m) = K(M / m)`. -/
theorem weighted_kantorovich_upper (n : Nat) (w lam : Fin n → F) {M m : F}
    (hm_pos : 0 < m) (hmM : m ≤ M)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : finSum n w = 1)
    (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    finSum n (fun i => w i * lam i) * finSum n (fun i => w i / lam i) ≤
      kantorovichConst (M / m) := by
  let S := finSum n (fun i => w i * lam i)
  let T := finSum n (fun i => w i / lam i)
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hS_pos : 0 < S :=
    lt_of_lt_of_le hm_pos (weighted_sum_ge_min n w lam hw_nonneg hw_sum (fun i => (hlam_bounds i).1))
  have hlam_pos : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le hm_pos (hlam_bounds i).1
  rw [kantorovichConst_ratio (ne_of_gt hm_pos)]
  apply sub_nonneg.mp
  rw [kantorovich_upper_master_identity n w lam (ne_of_gt hM_pos) (ne_of_gt hm_pos) hw_sum
        (fun i => ne_of_gt (hlam_pos i))]
  have h4Mm_pos : 0 < fourF * M * m :=
    LinearOrderedField.mul_pos (LinearOrderedField.mul_pos fourF_pos hM_pos) hm_pos
  have hsq : 0 ≤ ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) :=
    div_nonneg (sq_nonneg _) (le_of_lt h4Mm_pos)
  have hdef : 0 ≤ finSum n (fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)) := by
    apply finSum_nonneg
    intro i
    have h1 : 0 ≤ M - lam i := sub_nonneg.mpr (hlam_bounds i).2
    have h2 : 0 ≤ lam i - m := sub_nonneg.mpr (hlam_bounds i).1
    have hnum : 0 ≤ w i * ((M - lam i) * (lam i - m)) :=
      mul_nonneg (hw_nonneg i) (mul_nonneg h1 h2)
    have hden : 0 < M * m * lam i :=
      LinearOrderedField.mul_pos (LinearOrderedField.mul_pos hM_pos hm_pos) (hlam_pos i)
    exact div_nonneg hnum (le_of_lt hden)
  have hprod : 0 ≤ S * finSum n (fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)) :=
    mul_nonneg (le_of_lt hS_pos) hdef
  have htot := add_le_add hsq hprod
  rw [lofAddZero] at htot
  exact htot

/-- **Exact Upper-Bound Equality Characterization**:
    Equality `S * T = K(M/m)` holds iff `S = AM(M, m)` and every active weight `w_i > 0`
    sits on an extreme eigenvalue `λ_i ∈ {m, M}`. -/
theorem weighted_kantorovich_upper_eq_iff (n : Nat) (w lam : Fin n → F) {M m : F}
    (hm_pos : 0 < m) (hmM : m ≤ M)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : finSum n w = 1)
    (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    let S := finSum n (fun i => w i * lam i)
    let T := finSum n (fun i => w i / lam i)
    S * T = kantorovichConst (M / m) ↔
      S = arithmeticMean M m ∧ ∀ i, 0 < w i → (lam i = m ∨ lam i = M) := by
  intro S T
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hS_pos : 0 < S :=
    lt_of_lt_of_le hm_pos (weighted_sum_ge_min n w lam hw_nonneg hw_sum (fun i => (hlam_bounds i).1))
  have hlam_pos : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le hm_pos (hlam_bounds i).1
  have h4Mm_pos : 0 < fourF * M * m :=
    LinearOrderedField.mul_pos (LinearOrderedField.mul_pos fourF_pos hM_pos) hm_pos
  let term1 := ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m)
  let summand := fun i => (w i * ((M - lam i) * (lam i - m))) / (M * m * lam i)
  let term2 := S * finSum n summand
  have hs_nonneg : ∀ i, 0 ≤ summand i := by
    intro i
    exact div_nonneg
      (mul_nonneg (hw_nonneg i)
        (mul_nonneg (sub_nonneg.mpr (hlam_bounds i).2) (sub_nonneg.mpr (hlam_bounds i).1)))
      (le_of_lt (LinearOrderedField.mul_pos (LinearOrderedField.mul_pos hM_pos hm_pos) (hlam_pos i)))
  have ht1 : 0 ≤ term1 := div_nonneg (sq_nonneg _) (le_of_lt h4Mm_pos)
  have ht2 : 0 ≤ term2 := mul_nonneg (le_of_lt hS_pos) (finSum_nonneg n hs_nonneg)
  have hid := kantorovich_upper_master_identity n w lam (ne_of_gt hM_pos) (ne_of_gt hm_pos)
    hw_sum (fun i => ne_of_gt (hlam_pos i))
  constructor
  · intro heq
    rw [kantorovichConst_ratio (ne_of_gt hm_pos)] at heq
    have hdiff : ((M + m) * (M + m)) / (fourF * M * m) - S * T = 0 := by
      rw [heq, sub_self]
    change _ = term1 + term2 at hid
    rw [hdiff] at hid
    have ht1_zero : term1 = 0 := by
      rcases lt_trichotomy 0 term1 with hp | hz | hn
      · have hg := add_lt_add_of_lt_of_le hp ht2
        rw [lofAddZero, ← hid] at hg
        exact False.elim (lt_irrefl 0 hg)
      · exact hz.symm
      · exact False.elim (not_le_of_lt hn ht1)
    have ht2_zero : term2 = 0 := by
      rw [ht1_zero, lofZeroAdd] at hid
      exact hid.symm
    have hS_eq : S = arithmeticMean M m := by
      have hnum : (twoF * S - (M + m)) * (twoF * S - (M + m)) = 0 := by
        have hm := (div_eq_iff (ne_of_gt h4Mm_pos)).mp ht1_zero
        rw [zero_mul] at hm
        exact hm
      have h2S : twoF * S = M + m := sub_eq_zero.mp (sq_eq_zero_iff.mp hnum)
      unfold arithmeticMean
      apply (eq_div_iff twoF_ne_zero).mpr
      rw [lofMulComm S twoF]
      exact h2S
    have hsum_zero : finSum n summand = 0 := by
      rcases mul_eq_zero.mp ht2_zero with hSz | hz
      · exact False.elim (ne_of_gt hS_pos hSz)
      · exact hz
    have hall := (finSum_eq_zero_iff_of_nonneg n hs_nonneg).mp hsum_zero
    refine ⟨hS_eq, ?_⟩
    intro i hwi
    have hi := hall i
    have hden_ne : M * m * lam i ≠ 0 :=
      ne_of_gt (LinearOrderedField.mul_pos (LinearOrderedField.mul_pos hM_pos hm_pos) (hlam_pos i))
    have hnum : w i * ((M - lam i) * (lam i - m)) = 0 := by
      have hm := (div_eq_iff hden_ne).mp hi
      rw [zero_mul] at hm
      exact hm
    rcases mul_eq_zero.mp hnum with hwz | hprod
    · exact False.elim (ne_of_gt hwi hwz)
    · rcases mul_eq_zero.mp hprod with hM_eq | hm_eq
      · exact Or.inr (sub_eq_zero.mp hM_eq).symm
      · exact Or.inl (sub_eq_zero.mp hm_eq)
  · rintro ⟨hS_eq, hall⟩
    rw [kantorovichConst_ratio (ne_of_gt hm_pos)]
    have ht1_zero : term1 = 0 := by
      have h2S : twoF * S = M + m := by
        unfold arithmeticMean at hS_eq
        rw [hS_eq, lofMulComm twoF _, div_mul_cancel (M + m) twoF_ne_zero]
      change ((twoF * S - (M + m)) * (twoF * S - (M + m))) / (fourF * M * m) = 0
      rw [h2S, sub_self, zero_mul, zero_div]
    have ht2_zero : term2 = 0 := by
      have hsum_zero : finSum n summand = 0 := by
        apply finSum_eq_zero
        intro i
        by_cases hwi : w i = 0
        · change (w i * _) / _ = 0
          rw [hwi, zero_mul, zero_div]
        · have hwpos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
          rcases hall i hwpos with hm_eq | hM_eq
          · change (w i * ((M - lam i) * (lam i - m))) / _ = 0
            rw [hm_eq, sub_self, mul_zero, mul_zero, zero_div]
          · change (w i * ((M - lam i) * (lam i - m))) / _ = 0
            rw [hM_eq, sub_self, zero_mul, mul_zero, zero_div]
      change S * finSum n summand = 0
      rw [hsum_zero, mul_zero]
    change _ = term1 + term2 at hid
    rw [ht1_zero, ht2_zero, lofAddZero] at hid
    exact (sub_eq_zero.mp hid).symm

/-! ### Vector Formulation, Tightness for `n ≥ 2`, and Orthogonal SPD Invariance -/

theorem normSq_nonneg (n : Nat) (x : Fin n → F) : 0 ≤ normSq n x :=
  finSum_nonneg n (fun i => sq_nonneg (x i))

theorem normSq_pos_of_ne_zero (n : Nat) {x : Fin n → F} (hx : ∃ i, x i ≠ 0) :
    0 < normSq n x := by
  rcases hx with ⟨i₀, hi₀⟩
  have hnn := normSq_nonneg n x
  apply lt_of_le_of_ne hnn
  intro hz
  have hall := (finSum_eq_zero_iff_of_nonneg n (fun i => sq_nonneg (x i))).mp hz.symm
  exact hi₀ (sq_eq_zero_iff.mp (hall i₀))

/-- Reduction of `kantorovichQuotient` to normalized coordinate weights `w_i = x_i^2 / ‖x‖^2`. -/
theorem kantorovichQuotient_eq_weighted (n : Nat) (lam x : Fin n → F)
    (hx : ∃ i, x i ≠ 0) :
    let w := fun i => (x i * x i) / normSq n x
    kantorovichQuotient n lam x =
      finSum n (fun i => w i * lam i) * finSum n (fun i => w i / lam i) := by
  intro w
  have hn_pos : 0 < normSq n x := normSq_pos_of_ne_zero n hx
  have hn_ne : normSq n x ≠ 0 := ne_of_gt hn_pos
  have hS : finSum n (fun i => w i * lam i) = quadFormDiag n lam x / normSq n x := by
    have hc : finSum n (fun i => w i * lam i) =
        finSum n (fun i => (lam i * (x i * x i)) / normSq n x) := by
      apply finSum_congr
      intro i
      change ((x i * x i) / normSq n x) * lam i = _
      rw [div_mul_eq_mul_div, lofMulComm (x i * x i) (lam i)]
    rw [hc, finSum_div_const]
    rfl
  have hT : finSum n (fun i => w i / lam i) =
      quadFormDiag n (fun i => (lam i)⁻¹) x / normSq n x := by
    have hc : finSum n (fun i => w i / lam i) =
        finSum n (fun i => ((lam i)⁻¹ * (x i * x i)) / normSq n x) := by
      apply finSum_congr
      intro i
      change ((x i * x i) / normSq n x) / lam i = _
      rw [lofDivEqMulInv ((x i * x i) / normSq n x) (lam i),
          div_mul_eq_mul_div, lofMulComm (x i * x i) (lam i)⁻¹]
    rw [hc, finSum_div_const]
    rfl
  rw [hS, hT, div_mul_div _ _ _ _ hn_ne hn_ne]
  rfl

/-- **Clause 1 (Vector Kantorovich Bounds)**:
    For every `n`, every spectrum `0 < m ≤ λ_i ≤ M`, and every nonzero vector `x`:
    `1 ≤ Q_A(x) ≤ K(M / m)`. -/
theorem kantorovich_bounds_diag (n : Nat) (lam x : Fin n → F) {M m : F}
    (hm_pos : 0 < m) (hmM : m ≤ M)
    (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M)
    (hx : ∃ i, x i ≠ 0) :
    1 ≤ kantorovichQuotient n lam x ∧
      kantorovichQuotient n lam x ≤ kantorovichConst (M / m) := by
  let w := fun i => (x i * x i) / normSq n x
  have hn_pos : 0 < normSq n x := normSq_pos_of_ne_zero n hx
  have hw_nonneg : ∀ i, 0 ≤ w i :=
    fun i => div_nonneg (sq_nonneg (x i)) (le_of_lt hn_pos)
  have hw_sum : finSum n w = 1 := by
    change finSum n (fun i => (x i * x i) / normSq n x) = 1
    rw [finSum_div_const]
    exact div_self (ne_of_gt hn_pos)
  rw [kantorovichQuotient_eq_weighted n lam x hx]
  exact ⟨weighted_kantorovich_lower n w lam hm_pos hw_nonneg hw_sum (fun i => (hlam_bounds i).1),
         weighted_kantorovich_upper n w lam hm_pos hmM hw_nonneg hw_sum hlam_bounds⟩

/-- Evaluation of `quadFormDiag` on standard basis vector `e_k`. -/
theorem quadFormDiag_basisVec (n : Nat) (g : Fin n → F) (k : Fin n) :
    quadFormDiag n g (basisVec n k) = g k := by
  unfold quadFormDiag basisVec
  have hc : finSum n (fun i => g i * ((if i = k then (1 : F) else 0) *
      (if i = k then (1 : F) else 0))) =
      finSum n (fun i => if i = k then g k else 0) := by
    apply finSum_congr
    intro i
    by_cases hik : i = k
    · rw [if_pos hik, if_pos hik, hik, lofMulOne, lofMulOne]
    · rw [if_neg hik, if_neg hik, mul_zero, mul_zero]
  rw [hc, finSum_single]

theorem normSq_basisVec (n : Nat) (k : Fin n) :
    normSq (F := F) n (basisVec n k) = 1 := by
  have h : normSq (F := F) n (basisVec n k) =
      quadFormDiag n (fun _ => (1 : F)) (basisVec n k) := by
    unfold normSq quadFormDiag
    exact finSum_congr (fun i => (lofOneMul _).symm)
  rw [h, quadFormDiag_basisVec]

/-- Standard basis vector `e_k` attains the lower bound `Q_A(e_k) = 1`. -/
theorem kantorovichQuotient_basisVec (n : Nat) (lam : Fin n → F) (k : Fin n)
    (hk : lam k ≠ 0) :
    kantorovichQuotient n lam (basisVec n k) = 1 := by
  unfold kantorovichQuotient
  rw [quadFormDiag_basisVec, quadFormDiag_basisVec, normSq_basisVec,
      lofMulInvCancel hk, lofMulOne, div_one]

/-- Evaluation of `quadFormDiag` on `pairVec n j k = e_j + e_k` for `j ≠ k`. -/
theorem quadFormDiag_pairVec (n : Nat) (g : Fin n → F) {j k : Fin n} (hjk : j ≠ k) :
    quadFormDiag n g (pairVec n j k) = g j + g k := by
  unfold quadFormDiag pairVec
  have hc : finSum n (fun i =>
      g i * (((if i = j then (1 : F) else 0) + (if i = k then (1 : F) else 0)) *
             ((if i = j then (1 : F) else 0) + (if i = k then (1 : F) else 0)))) =
      finSum n (fun i => (if i = j then g j else 0) + (if i = k then g k else 0)) := by
    apply finSum_congr
    intro i
    by_cases hij : i = j
    · rw [hij, if_pos rfl, if_neg hjk, if_pos rfl, if_neg hjk,
          lofAddZero, lofMulOne, lofMulOne, lofAddZero]
    · by_cases hik : i = k
      · have hkj : k ≠ j := Ne.symm hjk
        rw [hik, if_neg hkj, if_pos rfl, if_neg hkj, if_pos rfl,
            lofZeroAdd, lofMulOne, lofMulOne, lofZeroAdd]
      · rw [if_neg hij, if_neg hik, if_neg hij, if_neg hik,
            lofAddZero, mul_zero, mul_zero]
  rw [hc, finSum_add, finSum_single, finSum_single]

theorem normSq_pairVec (n : Nat) {j k : Fin n} (hjk : j ≠ k) :
    normSq (F := F) n (pairVec n j k) = twoF := by
  have h : normSq (F := F) n (pairVec n j k) =
      quadFormDiag n (fun _ => (1 : F)) (pairVec n j k) := by
    unfold normSq quadFormDiag
    exact finSum_congr (fun i => (lofOneMul _).symm)
  rw [h, quadFormDiag_pairVec n _ hjk]
  rfl

theorem pairVec_nonzero (n : Nat) {j k : Fin n} (hjk : j ≠ k) :
    ∃ i, pairVec (F := F) n j k i ≠ 0 := by
  refine ⟨j, ?_⟩
  unfold pairVec
  rw [if_pos rfl, if_neg hjk, lofAddZero]
  exact Ne.symm LinearOrderedField.zero_ne_one

/-- **Clause 1 (Exact Tightness & AM/HM Extremizer Structure for all `n ≥ 2`)**:
    Whenever `j ≠ k` carry eigenvalues `λ_j = m` and `λ_k = M` (`0 < m, 0 < M`),
    the rational/integer-entry witness `x* = e_j + e_k` satisfies:
      1. `‖x*‖^2 = 2` (`x* ≠ 0`),
      2. `⟨Ax*, x*⟩ / ‖x*‖^2 = AM(M, m)`,
      3. `⟨A⁻¹x*, x*⟩ / ‖x*‖^2 = HM(M, m)⁻¹`,
      4. `Q_A(x*) = K(M / m)`. -/
theorem kantorovich_tightness_pairVec (n : Nat) (lam : Fin n → F) {M m : F}
    {j k : Fin n} (hjk : j ≠ k) (hm_pos : 0 < m) (hM_pos : 0 < M)
    (hj : lam j = m) (hk : lam k = M) :
    let x := pairVec n j k
    normSq n x = twoF ∧
    quadFormDiag n lam x / normSq n x = arithmeticMean M m ∧
    quadFormDiag n (fun i => (lam i)⁻¹) x / normSq n x = (harmonicMean M m)⁻¹ ∧
    kantorovichQuotient n lam x = kantorovichConst (M / m) := by
  intro x
  have hnorm : normSq n x = twoF := normSq_pairVec n hjk
  have hqa : quadFormDiag n lam x = M + m := by
    rw [quadFormDiag_pairVec n lam hjk, hj, hk, lofAddComm m M]
  have hqinv : quadFormDiag n (fun i => (lam i)⁻¹) x = (M + m) / (M * m) := by
    rw [quadFormDiag_pairVec n (fun i => (lam i)⁻¹) hjk, hj, hk]
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hM_pos) (ne_of_gt hm_pos))).mpr
    rw [lofRightDistrib]
    have h1 : m⁻¹ * (M * m) = M := by
      rw [lofMulComm M m, ← lofMulAssoc m⁻¹ m M, inv_mul_cancel (ne_of_gt hm_pos), lofOneMul]
    have h2 : M⁻¹ * (M * m) = m := by
      rw [← lofMulAssoc M⁻¹ M m, inv_mul_cancel (ne_of_gt hM_pos), lofOneMul]
    rw [h1, h2]
  have hrayA : quadFormDiag n lam x / normSq n x = arithmeticMean M m := by
    rw [hqa, hnorm]
    rfl
  have hrayInv : quadFormDiag n (fun i => (lam i)⁻¹) x / normSq n x = (harmonicMean M m)⁻¹ := by
    rw [hqinv, hnorm]
    unfold harmonicMean
    have hMm_pos : 0 < M + m := by
      have h := add_lt_add hM_pos hm_pos
      rw [lofAddZero] at h
      exact h
    have h2Mm_ne : twoF * M * m ≠ 0 :=
      mul_ne_zero (mul_ne_zero twoF_ne_zero (ne_of_gt hM_pos)) (ne_of_gt hm_pos)
    rw [inv_div h2Mm_ne (ne_of_gt hMm_pos), lofDivEqMulInv ((M + m) / (M * m)) twoF]
    have hinv2 : (twoF : F)⁻¹ = 1 / twoF := by
      rw [lofDivEqMulInv, lofOneMul]
    rw [hinv2, div_mul_div (M + m) (M * m) 1 twoF
          (mul_ne_zero (ne_of_gt hM_pos) (ne_of_gt hm_pos)) twoF_ne_zero, lofMulOne]
    congr 1
    calc
      (M * m) * twoF = twoF * (M * m) := lofMulComm (M * m) twoF
      _ = twoF * M * m := (lofMulAssoc twoF M m).symm
  have hquot : kantorovichQuotient n lam x = kantorovichConst (M / m) := by
    unfold kantorovichQuotient
    rw [← div_mul_div _ _ _ _ (by rw [hnorm]; exact twoF_ne_zero)
          (by rw [hnorm]; exact twoF_ne_zero),
        hrayA, hrayInv, ← lofDivEqMulInv, kantorovichConst_eq_am_div_hm hm_pos hM_pos]
  exact ⟨hnorm, hrayA, hrayInv, hquot⟩

/-! ### Orthogonal Invariance for General Symmetric Positive-Definite Matrices -/

/-- Confirm that `orthoSPDMat n Q lam` and `orthoSPDMat n Q lam⁻¹` are exact matrix inverses. -/
theorem orthoSPDMat_mul_inv (n : Nat) (Qmat : Fin n → Fin n → F) (lam : Fin n → F)
    (hQ : IsOrthogonal n Qmat) (hlam : ∀ i, lam i ≠ 0) (r t : Fin n) :
    matMul n (orthoSPDMat n Qmat lam) (orthoSPDMat n Qmat (fun i => (lam i)⁻¹)) r t =
      if r = t then 1 else 0 := by
  unfold matMul orthoSPDMat
  have step1 :
      finSum n (fun s =>
        finSum n (fun i => Qmat r i * lam i * Qmat s i) *
        finSum n (fun j => Qmat s j * (lam j)⁻¹ * Qmat t j)) =
      finSum n (fun i =>
        finSum n (fun j =>
          (Qmat r i * lam i) * ((lam j)⁻¹ * Qmat t j) *
            finSum n (fun s => Qmat s i * Qmat s j))) := by
    have hc1 :
        finSum n (fun s =>
          finSum n (fun i => Qmat r i * lam i * Qmat s i) *
          finSum n (fun j => Qmat s j * (lam j)⁻¹ * Qmat t j)) =
        finSum n (fun s =>
          finSum n (fun i =>
            finSum n (fun j =>
              (Qmat r i * lam i * Qmat s i) * (Qmat s j * (lam j)⁻¹ * Qmat t j)))) := by
      apply finSum_congr
      intro s
      rw [← finSum_mul_right]
      apply finSum_congr
      intro i
      rw [← finSum_mul_left]
    rw [hc1, finSum_comm n n]
    apply finSum_congr
    intro i
    rw [finSum_comm n n]
    apply finSum_congr
    intro j
    rw [← finSum_mul_left]
    apply finSum_congr
    intro s
    calc
      (Qmat r i * lam i * Qmat s i) * (Qmat s j * (lam j)⁻¹ * Qmat t j)
        = (Qmat r i * lam i) * (Qmat s i * (Qmat s j * ((lam j)⁻¹ * Qmat t j))) := by
          rw [lofMulAssoc (Qmat s j) (lam j)⁻¹ (Qmat t j),
              lofMulAssoc (Qmat r i * lam i) (Qmat s i) _]
      _ = (Qmat r i * lam i) * ((Qmat s i * Qmat s j) * ((lam j)⁻¹ * Qmat t j)) := by
          rw [← lofMulAssoc (Qmat s i) (Qmat s j) _]
      _ = (Qmat r i * lam i) * (((lam j)⁻¹ * Qmat t j) * (Qmat s i * Qmat s j)) := by
          rw [lofMulComm (Qmat s i * Qmat s j) _]
      _ = (Qmat r i * lam i) * ((lam j)⁻¹ * Qmat t j) * (Qmat s i * Qmat s j) := by
          rw [← lofMulAssoc]
  rw [step1]
  have step2 :
      finSum n (fun i =>
        finSum n (fun j =>
          (Qmat r i * lam i) * ((lam j)⁻¹ * Qmat t j) *
            finSum n (fun s => Qmat s i * Qmat s j))) =
      finSum n (fun i => Qmat r i * Qmat t i) := by
    apply finSum_congr
    intro i
    have hc2 :
        finSum n (fun j =>
          (Qmat r i * lam i) * ((lam j)⁻¹ * Qmat t j) *
            finSum n (fun s => Qmat s i * Qmat s j)) =
        finSum n (fun j => if j = i then Qmat r i * Qmat t i else 0) := by
      apply finSum_congr
      intro j
      rw [hQ.col_ortho i j]
      by_cases hij : j = i
      · rw [if_pos hij.symm, if_pos hij, hij, lofMulOne]
        calc
          (Qmat r i * lam i) * ((lam i)⁻¹ * Qmat t i)
            = Qmat r i * (lam i * ((lam i)⁻¹ * Qmat t i)) := lofMulAssoc _ _ _
          _ = Qmat r i * ((lam i * (lam i)⁻¹) * Qmat t i) := by
              rw [← lofMulAssoc (lam i) (lam i)⁻¹ _]
          _ = Qmat r i * Qmat t i := by rw [lofMulInvCancel (hlam i), lofOneMul]
      · have hij' : i ≠ j := fun h => hij h.symm
        rw [if_neg hij', if_neg hij, mul_zero]
    rw [hc2, finSum_single]
  rw [step2, hQ.row_ortho r t]

/-- Coordinate map `y = Q^T x` preserves `normSq` and diagonalizes `orthoSPDMat`. -/
def qtVec (n : Nat) (Qmat : Fin n → Fin n → F) (x : Fin n → F) : Fin n → F :=
  fun i => finSum n (fun r => Qmat r i * x r)

theorem matQuadForm_orthoSPD (n : Nat) (Qmat : Fin n → Fin n → F) (lam x : Fin n → F) :
    matQuadForm n (orthoSPDMat n Qmat lam) x = quadFormDiag n lam (qtVec n Qmat x) := by
  unfold matQuadForm orthoSPDMat quadFormDiag qtVec
  have hc1 :
      finSum n (fun r =>
        finSum n (fun s =>
          finSum n (fun i => Qmat r i * lam i * Qmat s i) * x s * x r)) =
      finSum n (fun r =>
        finSum n (fun i =>
          finSum n (fun s => (Qmat r i * lam i * Qmat s i) * x s * x r))) := by
    apply finSum_congr
    intro r
    have hc2 :
        finSum n (fun s =>
          finSum n (fun i => Qmat r i * lam i * Qmat s i) * x s * x r) =
        finSum n (fun s =>
          finSum n (fun i => (Qmat r i * lam i * Qmat s i) * x s * x r)) := by
      apply finSum_congr
      intro s
      rw [← finSum_mul_right, ← finSum_mul_right]
    rw [hc2, finSum_comm n n]
  rw [hc1, finSum_comm n n]
  apply finSum_congr
  intro i
  rw [← finSum_mul_right, ← finSum_mul_left]
  apply finSum_congr
  intro r
  rw [← finSum_mul_left, ← finSum_mul_left]
  apply finSum_congr
  intro s
  calc
    (Qmat r i * lam i * Qmat s i) * x s * x r
      = ((Qmat r i * lam i) * (Qmat s i * x s)) * x r := by
        rw [lofMulAssoc (Qmat r i * lam i) (Qmat s i) (x s)]
    _ = (Qmat r i * lam i) * ((Qmat s i * x s) * x r) := lofMulAssoc _ _ _
    _ = (lam i * Qmat r i) * (x r * (Qmat s i * x s)) := by
        rw [lofMulComm (Qmat r i) (lam i), lofMulComm (Qmat s i * x s) (x r)]
    _ = lam i * (Qmat r i * (x r * (Qmat s i * x s))) := lofMulAssoc _ _ _
    _ = lam i * ((Qmat r i * x r) * (Qmat s i * x s)) := by
        rw [← lofMulAssoc (Qmat r i) (x r) _]

theorem normSq_qtVec (n : Nat) (Qmat : Fin n → Fin n → F) (x : Fin n → F)
    (hQ : IsOrthogonal n Qmat) :
    normSq n (qtVec n Qmat x) = normSq n x := by
  have h1 := matQuadForm_orthoSPD n Qmat (fun _ => (1 : F)) x
  have hrhs : quadFormDiag n (fun _ => (1 : F)) (qtVec n Qmat x) = normSq n (qtVec n Qmat x) := by
    unfold quadFormDiag normSq
    exact finSum_congr (fun i => lofOneMul _)
  rw [hrhs] at h1
  rw [← h1]
  unfold matQuadForm orthoSPDMat normSq
  apply finSum_congr
  intro r
  have hc :
      finSum n (fun s =>
        finSum n (fun i => Qmat r i * 1 * Qmat s i) * x s * x r) =
      finSum n (fun s => if s = r then x r * x r else 0) := by
    apply finSum_congr
    intro s
    have hrow : finSum n (fun i => Qmat r i * 1 * Qmat s i) = if r = s then 1 else 0 := by
      have hc2 : finSum n (fun i => Qmat r i * 1 * Qmat s i) =
          finSum n (fun i => Qmat r i * Qmat s i) :=
        finSum_congr (fun i => by rw [lofMulOne])
      rw [hc2, hQ.row_ortho r s]
    rw [hrow]
    by_cases hrs : s = r
    · rw [if_pos hrs.symm, if_pos hrs, hrs, lofOneMul]
    · have hrs' : r ≠ s := fun h => hrs h.symm
      rw [if_neg hrs', if_neg hrs, zero_mul, zero_mul]
  rw [hc, finSum_single]

/-- **Clause 1 for General Orthogonally Diagonalizable SPD Matrices `A = Q diag(λ) Q^T`**:
    For every orthogonal `Q`, spectrum `0 < m ≤ λ_i ≤ M`, and nonzero `x`:
    `1 ≤ (⟨Ax, x⟩ ⟨A⁻¹x, x⟩) / ‖x‖^4 ≤ K(M / m)`. -/
theorem kantorovich_bounds_orthoSPD (n : Nat) (Qmat : Fin n → Fin n → F)
    (lam x : Fin n → F) {M m : F}
    (hQ : IsOrthogonal n Qmat)
    (hm_pos : 0 < m) (hmM : m ≤ M)
    (hlam_bounds : ∀ i, m ≤ lam i ∧ lam i ≤ M)
    (hx : ∃ i, x i ≠ 0) :
    let A := orthoSPDMat n Qmat lam
    let A_inv := orthoSPDMat n Qmat (fun i => (lam i)⁻¹)
    1 ≤ matrixKantorovichQuotient n A A_inv x ∧
      matrixKantorovichQuotient n A A_inv x ≤ kantorovichConst (M / m) := by
  intro A A_inv
  have hnorm_eq : normSq n (qtVec n Qmat x) = normSq n x := normSq_qtVec n Qmat x hQ
  have hy : ∃ i, qtVec n Qmat x i ≠ 0 := by
    have hp : 0 < normSq n (qtVec n Qmat x) := by
      rw [hnorm_eq]
      exact normSq_pos_of_ne_zero n hx
    by_cases hex : ∃ i, qtVec n Qmat x i ≠ 0
    · exact hex
    · have hall : ∀ i, qtVec n Qmat x i = 0 := by
        intro i
        by_cases hi : qtVec n Qmat x i = 0
        · exact hi
        · exact False.elim (hex ⟨i, hi⟩)
      have hz : normSq n (qtVec n Qmat x) = 0 := by
        unfold normSq
        exact finSum_eq_zero n (fun i => by rw [hall i, zero_mul])
      rw [hz] at hp
      exact False.elim (lt_irrefl 0 hp)
  have hq : matrixKantorovichQuotient n A A_inv x =
      kantorovichQuotient n lam (qtVec n Qmat x) := by
    unfold matrixKantorovichQuotient kantorovichQuotient
    rw [matQuadForm_orthoSPD, matQuadForm_orthoSPD, hnorm_eq]
  rw [hq]
  exact kantorovich_bounds_diag n lam (qtVec n Qmat x) hm_pos hmM hlam_bounds hy

end Clause1Proofs

end Conjecture00000007166
