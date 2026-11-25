/-
  Conjecture 00000007178 — Matrix Rank, Minors, and Partial Matrix Completions
  Defines matrix rank factorization `HasRankAtMost`, `2 × 2` and `3 × 3` minor
  obstructions over arbitrary commutative rings, and partial matrix completion rank.
-/

import Conjecture00000007178.Algebra

namespace Conjecture00000007178

universe u

open CommRingR

/-- An `m × n` matrix over `R`. -/
abbrev Mat (R : Type u) (m n : Nat) := Fin m → Fin n → R

/-- Explicit bounded universal principles for `Fin 2`..`Fin 7` in Core Lean 4. -/
theorem fin2_cases {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i : Fin 2, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | _ + 2 => omega

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i : Fin 3, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | _ + 3 => omega

theorem fin4_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i : Fin 4, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | _ + 4 => omega

theorem fin5_cases {P : Fin 5 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) :
    ∀ i : Fin 5, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | _ + 5 => omega

theorem fin6_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ i : Fin 6, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | _ + 6 => omega

theorem fin7_cases {P : Fin 7 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) :
    ∀ i : Fin 7, P i := by
  intro ⟨val, isLt⟩
  match val with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | _ + 7 => omega

/-- Summation over `Fin r` in a commutative ring `R`. -/
def finSum {R : Type u} [CommRingR R] : {r : Nat} → (Fin r → R) → R
  | 0, _ => 0
  | r + 1, f => f ⟨0, Nat.zero_lt_succ r⟩ + finSum (fun t : Fin r => f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)

theorem finSum_zero {R : Type u} [CommRingR R] (f : Fin 0 → R) : finSum f = 0 := rfl

theorem finSum_one {R : Type u} [CommRingR R] (f : Fin 1 → R) :
    finSum f = f ⟨0, Nat.zero_lt_one⟩ := by
  unfold finSum
  exact add_zero _

theorem finSum_two {R : Type u} [CommRingR R] (f : Fin 2 → R) :
    finSum f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  simp [finSum, add_zero]

theorem finSum_three {R : Type u} [CommRingR R] (f : Fin 3 → R) :
    finSum f = f ⟨0, by decide⟩ + (f ⟨1, by decide⟩ + f ⟨2, by decide⟩) := by
  simp [finSum, add_zero]

theorem finSum_four {R : Type u} [CommRingR R] (f : Fin 4 → R) :
    finSum f = f ⟨0, by decide⟩ + (f ⟨1, by decide⟩ + (f ⟨2, by decide⟩ + f ⟨3, by decide⟩)) := by
  simp [finSum, add_zero]

/-- Matrix `M` is symmetric. -/
def IsSymmetric {R : Type u} {n : Nat} (M : Mat R n n) : Prop :=
  ∀ i j : Fin n, M i j = M j i

/-- Standard rank-factorization predicate: `M` has rank at most `r` over `R`
iff `M = U * V` for some `m × r` matrix `U` and `r × n` matrix `V`.
Over any field `F`, this is equivalent to `dim(rowSpace M) ≤ r` and `dim(colSpace M) ≤ r`. -/
def HasRankAtMost (R : Type u) [CommRingR R] {m n : Nat} (r : Nat) (M : Mat R m n) : Prop :=
  ∃ (U : Mat R m r) (V : Mat R r n),
    ∀ (i : Fin m) (j : Fin n), M i j = finSum (fun t : Fin r => U i t * V t j)

theorem hasRankAtMost_zero_iff {R : Type u} [CommRingR R] {m n : Nat} (M : Mat R m n) :
    HasRankAtMost R 0 M ↔ ∀ i j, M i j = 0 := by
  constructor
  · rintro ⟨U, V, hM⟩ i j
    rw [hM i j]
    rfl
  · intro h0
    refine ⟨fun _ t => Fin.elim0 t, fun t _ => Fin.elim0 t, ?_⟩
    intro i j
    exact h0 i j

theorem hasRankAtMost_one_iff_outer {R : Type u} [CommRingR R] {m n : Nat} (M : Mat R m n) :
    HasRankAtMost R 1 M ↔ ∃ (u : Fin m → R) (v : Fin n → R), ∀ i j, M i j = u i * v j := by
  constructor
  · rintro ⟨U, V, hM⟩
    refine ⟨fun i => U i ⟨0, Nat.zero_lt_one⟩, fun j => V ⟨0, Nat.zero_lt_one⟩ j, ?_⟩
    intro i j
    rw [hM i j, finSum_one]
  · rintro ⟨u, v, huv⟩
    refine ⟨fun i _ => u i, fun _ j => v j, ?_⟩
    intro i j
    rw [finSum_one]
    exact huv i j

theorem hasRankAtMost_succ {R : Type u} [CommRingR R] {m n r : Nat} {M : Mat R m n}
    (h : HasRankAtMost R r M) : HasRankAtMost R (r + 1) M := by
  rcases h with ⟨U, V, hM⟩
  let U' : Mat R m (r + 1) := fun i t =>
    match t with
    | ⟨0, _⟩ => 0
    | ⟨k + 1, hk⟩ => U i ⟨k, Nat.lt_of_succ_lt_succ hk⟩
  let V' : Mat R (r + 1) n := fun t j =>
    match t with
    | ⟨0, _⟩ => 0
    | ⟨k + 1, hk⟩ => V ⟨k, Nat.lt_of_succ_lt_succ hk⟩ j
  refine ⟨U', V', ?_⟩
  intro i j
  rw [hM i j]
  show finSum (fun t : Fin r => U i t * V t j) =
       (0 : R) * 0 + finSum (fun t : Fin r => U i t * V t j)
  rw [zero_mul, zero_add]

theorem HasRankAtMost.mono {R : Type u} [CommRingR R] {m n : Nat} {r₁ r₂ : Nat}
    (hle : r₁ ≤ r₂) {M : Mat R m n} (h : HasRankAtMost R r₁ M) : HasRankAtMost R r₂ M := by
  induction hle with
  | refl => exact h
  | step _ ih => exact hasRankAtMost_succ ih

theorem not_hasRankAtMost_of_lt {R : Type u} [CommRingR R] {m n r₁ r₂ : Nat}
    (hle : r₁ ≤ r₂) {M : Mat R m n} (hnot : ¬ HasRankAtMost R r₂ M) :
    ¬ HasRankAtMost R r₁ M :=
  fun h1 => hnot (HasRankAtMost.mono hle h1)

/-- Nonzero matrix cannot have rank `0`. -/
theorem not_hasRankAtMost_zero_of_entry_ne_zero {R : Type u} [CommRingR R] {m n : Nat}
    {M : Mat R m n} (i : Fin m) (j : Fin n) (hne : M i j ≠ 0) :
    ¬ HasRankAtMost R 0 M := by
  intro h0
  exact hne ((hasRankAtMost_zero_iff M).mp h0 i j)

/-- Universal `2 × 2` minor identity: if `rank(M) ≤ 1`, every `2 × 2` minor vanishes. -/
theorem minor2_eq_of_rank_le_one {R : Type u} [CommRingR R] {m n : Nat}
    {M : Mat R m n} (h : HasRankAtMost R 1 M)
    (i₀ i₁ : Fin m) (j₀ j₁ : Fin n) :
    M i₀ j₀ * M i₁ j₁ = M i₀ j₁ * M i₁ j₀ := by
  rcases (hasRankAtMost_one_iff_outer M).mp h with ⟨u, v, huv⟩
  rw [huv i₀ j₀, huv i₁ j₁, huv i₀ j₁, huv i₁ j₀]
  rw [mul_assoc (u i₀), mul_assoc (u i₀)]
  apply congrArg (fun x => u i₀ * x)
  calc
    v j₀ * (u i₁ * v j₁) = (u i₁ * v j₁) * v j₀ := mul_comm _ _
    _ = (v j₁ * u i₁) * v j₀ := by rw [mul_comm (u i₁) (v j₁)]
    _ = v j₁ * (u i₁ * v j₀) := mul_assoc _ _ _

/-- `3 × 3` determinant of a submatrix indexed by rows `(i₀, i₁, i₂)` and columns `(j₀, j₁, j₂)`. -/
def subDet3 {R : Type u} [CommRingR R] {m n : Nat} (M : Mat R m n)
    (i₀ i₁ i₂ : Fin m) (j₀ j₁ j₂ : Fin n) : R :=
  M i₀ j₀ * (M i₁ j₁ * M i₂ j₂ - M i₁ j₂ * M i₂ j₁) -
  M i₀ j₁ * (M i₁ j₀ * M i₂ j₂ - M i₁ j₂ * M i₂ j₀) +
  M i₀ j₂ * (M i₁ j₀ * M i₂ j₁ - M i₁ j₁ * M i₂ j₀)

/-- Helper lemma: in any commutative ring, a `3 × 3` matrix whose rows are linear
combinations of `2` vectors `(v₀, v₁)` has determinant `0`. -/
theorem det3_rank2_factor_zero {F : Type u} [FieldR F]
    (a₀ b₀ a₁ b₁ a₂ b₂ x₀ y₀ z₀ x₁ y₁ z₁ : F) :
    let m00 := a₀ * x₀ + b₀ * x₁
    let m01 := a₀ * y₀ + b₀ * y₁
    let m02 := a₀ * z₀ + b₀ * z₁
    let m10 := a₁ * x₀ + b₁ * x₁
    let m11 := a₁ * y₀ + b₁ * y₁
    let m12 := a₁ * z₀ + b₁ * z₁
    let m20 := a₂ * x₀ + b₂ * x₁
    let m21 := a₂ * y₀ + b₂ * y₁
    let m22 := a₂ * z₀ + b₂ * z₁
    m00 * (m11 * m22 - m12 * m21) -
    m01 * (m10 * m22 - m12 * m20) +
    m02 * (m10 * m21 - m11 * m20) = 0 := by
  dsimp only
  -- Note: `(a₁ y₀ + b₁ y₁)(a₂ z₀ + b₂ z₁) - (a₁ z₀ + b₁ z₁)(a₂ y₀ + b₂ y₁)`
  -- simplifies cleanly to `(a₁ b₂ - b₁ a₂)(y₀ z₁ - z₀ y₁)`!
  have hmin : ∀ p₁ q₁ p₂ q₂ u₀ u₁ w₀ w₁ : F,
      (p₁ * u₀ + q₁ * u₁) * (p₂ * w₀ + q₂ * w₁) -
      (p₁ * w₀ + q₁ * w₁) * (p₂ * u₀ + q₂ * u₁) =
      (p₁ * q₂ - q₁ * p₂) * (u₀ * w₁ - w₀ * u₁) := by
    intro p₁ q₁ p₂ q₂ u₀ u₁ w₀ w₁
    -- Expand and cancel the `p₁ p₂ u₀ w₀` and `q₁ q₂ u₁ w₁` terms!
    have expandL :
        (p₁ * u₀ + q₁ * u₁) * (p₂ * w₀ + q₂ * w₁) =
        ((p₁ * p₂) * (u₀ * w₀) + (q₁ * q₂) * (u₁ * w₁)) +
        ((p₁ * q₂) * (u₀ * w₁) + (q₁ * p₂) * (u₁ * w₀)) := by
      rw [right_distrib, left_distrib, left_distrib]
      have t1 : (p₁ * u₀) * (p₂ * w₀) = (p₁ * p₂) * (u₀ * w₀) := by
        rw [mul_assoc, ← mul_assoc u₀, mul_comm u₀ p₂, mul_assoc p₂, ← mul_assoc]
      have t2 : (p₁ * u₀) * (q₂ * w₁) = (p₁ * q₂) * (u₀ * w₁) := by
        rw [mul_assoc, ← mul_assoc u₀, mul_comm u₀ q₂, mul_assoc q₂, ← mul_assoc]
      have t3 : (q₁ * u₁) * (p₂ * w₀) = (q₁ * p₂) * (u₁ * w₀) := by
        rw [mul_assoc, ← mul_assoc u₁, mul_comm u₁ p₂, mul_assoc p₂, ← mul_assoc]
      have t4 : (q₁ * u₁) * (q₂ * w₁) = (q₁ * q₂) * (u₁ * w₁) := by
        rw [mul_assoc, ← mul_assoc u₁, mul_comm u₁ q₂, mul_assoc q₂, ← mul_assoc]
      rw [t1, t2, t3, t4]
      let A := (p₁ * p₂) * (u₀ * w₀)
      let B := (p₁ * q₂) * (u₀ * w₁)
      let C := (q₁ * p₂) * (u₁ * w₀)
      let D := (q₁ * q₂) * (u₁ * w₁)
      show (A + B) + (C + D) = (A + D) + (B + C)
      calc
        (A + B) + (C + D) = A + (B + (C + D)) := by rw [add_assoc]
        _ = A + ((B + C) + D) := by rw [← add_assoc B C D]
        _ = A + (D + (B + C)) := by rw [add_comm (B + C) D]
        _ = (A + D) + (B + C) := by rw [← add_assoc]
    have expandR :
        (p₁ * w₀ + q₁ * w₁) * (p₂ * u₀ + q₂ * u₁) =
        ((p₁ * p₂) * (u₀ * w₀) + (q₁ * q₂) * (u₁ * w₁)) +
        ((p₁ * q₂) * (w₀ * u₁) + (q₁ * p₂) * (w₁ * u₀)) := by
      rw [right_distrib, left_distrib, left_distrib]
      have s1 : (p₁ * w₀) * (p₂ * u₀) = (p₁ * p₂) * (u₀ * w₀) := by
        rw [mul_assoc, ← mul_assoc w₀, mul_comm w₀ p₂, mul_assoc p₂, ← mul_assoc, mul_comm w₀ u₀]
      have s2 : (p₁ * w₀) * (q₂ * u₁) = (p₁ * q₂) * (w₀ * u₁) := by
        rw [mul_assoc, ← mul_assoc w₀, mul_comm w₀ q₂, mul_assoc q₂, ← mul_assoc]
      have s3 : (q₁ * w₁) * (p₂ * u₀) = (q₁ * p₂) * (w₁ * u₀) := by
        rw [mul_assoc, ← mul_assoc w₁, mul_comm w₁ p₂, mul_assoc p₂, ← mul_assoc]
      have s4 : (q₁ * w₁) * (q₂ * u₁) = (q₁ * q₂) * (u₁ * w₁) := by
        rw [mul_assoc, ← mul_assoc w₁, mul_comm w₁ q₂, mul_assoc q₂, ← mul_assoc, mul_comm w₁ u₁]
      rw [s1, s2, s3, s4]
      let A := (p₁ * p₂) * (u₀ * w₀)
      let B := (p₁ * q₂) * (w₀ * u₁)
      let C := (q₁ * p₂) * (w₁ * u₀)
      let D := (q₁ * q₂) * (u₁ * w₁)
      show (A + B) + (C + D) = (A + D) + (B + C)
      calc
        (A + B) + (C + D) = A + (B + (C + D)) := by rw [add_assoc]
        _ = A + ((B + C) + D) := by rw [← add_assoc B C D]
        _ = A + (D + (B + C)) := by rw [add_comm (B + C) D]
        _ = (A + D) + (B + C) := by rw [← add_assoc]
    rw [expandL, expandR]
    have cancelCommon : ∀ K X Y : F, (K + X) - (K + Y) = X - Y := by
      intro K X Y
      rw [sub_eq_add_neg, neg_add, add_assoc K X (-K + -Y)]
      rw [← add_assoc X (-K) (-Y), add_comm X (-K), add_assoc (-K) X (-Y)]
      rw [← add_assoc K (-K) (X + -Y), add_neg_cancel, zero_add, ← sub_eq_add_neg]
    rw [cancelCommon]
    -- Now show `(P * U + Q * V') - (P * W + Q * Z') = (P - Q) * (U - W)` where `V' = W` and `Z' = U`
    rw [mul_comm u₁ w₀, mul_comm w₁ u₀]
    let P := p₁ * q₂
    let Q := q₁ * p₂
    let U := u₀ * w₁
    let W := w₀ * u₁
    show (P * U + Q * W) - (P * W + Q * U) = (P - Q) * (U - W)
    calc
      (P * U + Q * W) - (P * W + Q * U)
          = (P * U + Q * W) + (-(P * W) + -(Q * U)) := by rw [sub_eq_add_neg, neg_add]
      _ = P * U + (Q * W + (-(P * W) + -(Q * U))) := by rw [add_assoc]
      _ = P * U + ((Q * W + -(Q * U)) + -(P * W)) := by
        rw [add_comm (-(P * W)) (-(Q * U)), ← add_assoc (Q * W)]
      _ = P * U + (-(P * W) + (Q * W + -(Q * U))) := by rw [add_comm (Q * W + -(Q * U)) (-(P * W))]
      _ = (P * U + -(P * W)) + (Q * W + -(Q * U)) := by rw [← add_assoc]
      _ = (P * U - P * W) + (-(Q * U) + Q * W) := by rw [← sub_eq_add_neg, add_comm (Q * W)]
      _ = P * (U - W) - Q * (U - W) := by
        have hQ : -(Q * U) + Q * W = -(Q * (U - W)) := by
          rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg]
        rw [← mul_sub, hQ, ← sub_eq_add_neg]
      _ = (P - Q) * (U - W) := by rw [← sub_mul]
  rw [hmin a₁ b₁ a₂ b₂ y₀ y₁ z₀ z₁,
      hmin a₁ b₁ a₂ b₂ x₀ x₁ z₀ z₁,
      hmin a₁ b₁ a₂ b₂ x₀ x₁ y₀ y₁]
  let D := a₁ * b₂ - b₁ * a₂
  -- Factor `D` to the left and apply `hmin` / cancellation on the remaining 6 terms!
  have pullD : ∀ s m : F, s * (D * m) = D * (s * m) := by
    intro s m
    rw [← mul_assoc, mul_comm s D, mul_assoc]
  rw [pullD (a₀ * x₀ + b₀ * x₁), pullD (a₀ * y₀ + b₀ * y₁), pullD (a₀ * z₀ + b₀ * z₁)]
  rw [← mul_sub, ← left_distrib]
  -- Now show `(a₀*x₀+b₀*x₁)*(y₀*z₁-z₀*y₁) - (a₀*y₀+b₀*y₁)*(x₀*z₁-z₀*x₁) + (a₀*z₀+b₀*z₁)*(x₀*y₁-y₀*x₁) = 0`!
  have inner_a : ∀ x₀ y₀ z₀ x₁ y₁ z₁ : F,
      x₀ * (y₀ * z₁ - z₀ * y₁) - y₀ * (x₀ * z₁ - z₀ * x₁) + z₀ * (x₀ * y₁ - y₀ * x₁) = 0 := by
    intro x₀ y₀ z₀ x₁ y₁ z₁
    rw [mul_sub, mul_sub, mul_sub]
    have e1 : y₀ * (x₀ * z₁) = x₀ * (y₀ * z₁) := by rw [← mul_assoc, mul_comm y₀ x₀, mul_assoc]
    have e2 : z₀ * (x₀ * y₁) = x₀ * (z₀ * y₁) := by rw [← mul_assoc, mul_comm z₀ x₀, mul_assoc]
    have e3 : z₀ * (y₀ * x₁) = y₀ * (z₀ * x₁) := by rw [← mul_assoc, mul_comm z₀ y₀, mul_assoc]
    rw [e1, e2, e3]
    let A := x₀ * (y₀ * z₁)
    let B := x₀ * (z₀ * y₁)
    let C := y₀ * (z₀ * x₁)
    show ((A - B) - (A - C)) + (B - C) = 0
    calc
      ((A - B) - (A - C)) + (B - C)
          = ((A + -B) + (-A + C)) + (B + -C) := by
            rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
      _ = (A + (-B + (-A + C))) + (B + -C) := by rw [add_assoc A]
      _ = (A + (-A + (-B + C))) + (B + -C) := by
            rw [← add_assoc (-B) (-A) C, add_comm (-B) (-A), add_assoc (-A)]
      _ = ((A + -A) + (-B + C)) + (B + -C) := by rw [← add_assoc A (-A)]
      _ = (-B + C) + (B + -C) := by rw [add_neg_cancel, zero_add]
      _ = -B + (C + (-C + B)) := by rw [add_comm B (-C), add_assoc (-B)]
      _ = -B + ((C + -C) + B) := by rw [← add_assoc C (-C) B]
      _ = -B + B := by rw [add_neg_cancel, zero_add]
      _ = 0 := neg_add_cancel B
  have split_ab : ∀ c₁ c₂ c₃ : F,
      (a₀ * x₀ + b₀ * x₁) * c₁ - (a₀ * y₀ + b₀ * y₁) * c₂ + (a₀ * z₀ + b₀ * z₁) * c₃ =
      a₀ * (x₀ * c₁ - y₀ * c₂ + z₀ * c₃) + b₀ * (x₁ * c₁ - y₁ * c₂ + z₁ * c₃) := by
    intro c₁ c₂ c₃
    rw [right_distrib, right_distrib, right_distrib]
    rw [mul_assoc a₀, mul_assoc b₀, mul_assoc a₀, mul_assoc b₀, mul_assoc a₀, mul_assoc b₀]
    let X1 := a₀ * (x₀ * c₁)
    let Y1 := b₀ * (x₁ * c₁)
    let X2 := a₀ * (y₀ * c₂)
    let Y2 := b₀ * (y₁ * c₂)
    let X3 := a₀ * (z₀ * c₃)
    let Y3 := b₀ * (z₁ * c₃)
    have rearr : ((X1 + Y1) - (X2 + Y2)) + (X3 + Y3) = ((X1 - X2) + X3) + ((Y1 - Y2) + Y3) := by
      rw [sub_eq_add_neg, neg_add, sub_eq_add_neg X1 X2, sub_eq_add_neg Y1 Y2]
      calc
        ((X1 + Y1) + (-X2 + -Y2)) + (X3 + Y3)
            = X1 + (Y1 + (-X2 + (-Y2 + (X3 + Y3)))) := by
              rw [add_assoc (X1 + Y1), add_assoc (-X2), add_assoc X1]
        _ = X1 + (Y1 + (-X2 + (X3 + (-Y2 + Y3)))) := by
              rw [← add_assoc (-Y2) X3 Y3, add_comm (-Y2) X3, add_assoc X3]
        _ = X1 + (Y1 + ((-X2 + X3) + (-Y2 + Y3))) := by rw [← add_assoc (-X2) X3]
        _ = X1 + ((-X2 + X3) + (Y1 + (-Y2 + Y3))) := by
              rw [← add_assoc Y1 (-X2 + X3), add_comm Y1 (-X2 + X3), add_assoc (-X2 + X3)]
        _ = ((X1 + -X2) + X3) + ((Y1 + -Y2) + Y3) := by
              rw [← add_assoc X1 (-X2 + X3), ← add_assoc X1 (-X2) X3, ← add_assoc Y1 (-Y2) Y3]
    rw [rearr, ← mul_sub a₀, ← left_distrib a₀, ← mul_sub b₀, ← left_distrib b₀]
  rw [split_ab]
  rw [inner_a x₀ y₀ z₀ x₁ y₁ z₁]
  have inner_b : x₁ * (y₀ * z₁ - z₀ * y₁) - y₁ * (x₀ * z₁ - z₀ * x₁) + z₁ * (x₀ * y₁ - y₀ * x₁) = 0 := by
    -- Negate each parenthesized difference and use `inner_a x₁ y₁ z₁ x₀ y₀ z₀`
    have neg_diff : ∀ p q : F, p - q = -(q - p) := by
      intro p q
      rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]
    rw [neg_diff (y₀ * z₁) (z₀ * y₁), neg_diff (x₀ * z₁) (z₀ * x₁), neg_diff (x₀ * y₁) (y₀ * x₁)]
    rw [mul_comm z₀ y₁, mul_comm z₀ x₁, mul_comm y₀ x₁,
        mul_comm y₀ z₁, mul_comm x₀ z₁, mul_comm x₀ y₁]
    rw [mul_neg, mul_neg, mul_neg]
    have ha1 := inner_a x₁ y₁ z₁ x₀ y₀ z₀
    calc
      (- (x₁ * (y₁ * z₀ - z₁ * y₀)) - - (y₁ * (x₁ * z₀ - z₁ * x₀))) + - (z₁ * (x₁ * y₀ - y₁ * x₀))
          = - ((x₁ * (y₁ * z₀ - z₁ * y₀) - y₁ * (x₁ * z₀ - z₁ * x₀)) + z₁ * (x₁ * y₀ - y₁ * x₀)) := by
            let A1 := x₁ * (y₁ * z₀ - z₁ * y₀)
            let B1 := y₁ * (x₁ * z₀ - z₁ * x₀)
            let C1 := z₁ * (x₁ * y₀ - y₁ * x₀)
            show (-A1 - -B1) + -C1 = -((A1 - B1) + C1)
            rw [sub_eq_add_neg (-A1) (-B1), neg_neg B1, sub_eq_add_neg A1 B1,
                neg_add (A1 + -B1) C1, neg_add A1 (-B1), neg_neg B1]
      _ = -(0 : F) := by rw [ha1]
      _ = 0 := neg_zero
  rw [inner_b, mul_zero, mul_zero, add_zero, mul_zero]

/-- Universal `3 × 3` minor obstruction: if `HasRankAtMost F 2 M`, then every `3 × 3`
submatrix determinant `subDet3 M i₀ i₁ i₂ j₀ j₁ j₂` vanishes. -/
theorem subDet3_eq_zero_of_rank_le_two {F : Type u} [FieldR F] {m n : Nat}
    {M : Mat F m n} (h : HasRankAtMost F 2 M)
    (i₀ i₁ i₂ : Fin m) (j₀ j₁ j₂ : Fin n) :
    subDet3 M i₀ i₁ i₂ j₀ j₁ j₂ = 0 := by
  rcases h with ⟨U, V, hM⟩
  unfold subDet3
  have entry : ∀ i j, M i j = U i ⟨0, by decide⟩ * V ⟨0, by decide⟩ j + U i ⟨1, by decide⟩ * V ⟨1, by decide⟩ j := by
    intro i j
    rw [hM i j, finSum_two]
  rw [entry i₀ j₀, entry i₀ j₁, entry i₀ j₂,
      entry i₁ j₀, entry i₁ j₁, entry i₁ j₂,
      entry i₂ j₀, entry i₂ j₁, entry i₂ j₂]
  exact det3_rank2_factor_zero
    (U i₀ ⟨0, by decide⟩) (U i₀ ⟨1, by decide⟩)
    (U i₁ ⟨0, by decide⟩) (U i₁ ⟨1, by decide⟩)
    (U i₂ ⟨0, by decide⟩) (U i₂ ⟨1, by decide⟩)
    (V ⟨0, by decide⟩ j₀) (V ⟨0, by decide⟩ j₁) (V ⟨0, by decide⟩ j₂)
    (V ⟨1, by decide⟩ j₀) (V ⟨1, by decide⟩ j₁) (V ⟨1, by decide⟩ j₂)

/-! ### Partial Matrices and Minimum-Rank Completion -/

/-- A partial `m × n` matrix over `R`: `spec i j = true` marks specified entries,
with prescribed value `val i j`. -/
structure PartialMatrix (R : Type u) (m n : Nat) where
  spec : Fin m → Fin n → Bool
  val  : Fin m → Fin n → R

namespace PartialMatrix

/-- Two partial matrices share the exact same combinatorial specification pattern. -/
def SamePattern {R₁ : Type u} {R₂ : Type u} {m n : Nat}
    (P₁ : PartialMatrix R₁ m n) (P₂ : PartialMatrix R₂ m n) : Prop :=
  P₁.spec = P₂.spec

/-- Every specified entry is nonzero (so the zero/nonzero support coincides with `spec`). -/
def EverywhereNonzero {R : Type u} [Zero R] {m n : Nat} (P : PartialMatrix R m n) : Prop :=
  ∀ i j, P.spec i j = true → P.val i j ≠ 0

/-- `M` completes the partial matrix `P`. -/
def IsCompletion {R : Type u} {m n : Nat} (P : PartialMatrix R m n) (M : Mat R m n) : Prop :=
  ∀ i j, P.spec i j = true → M i j = P.val i j

/-- `M` is a symmetric completion of a square partial matrix `P`. -/
def IsSymCompletion {R : Type u} {n : Nat} (P : PartialMatrix R n n) (M : Mat R n n) : Prop :=
  IsSymmetric M ∧ P.IsCompletion M

/-- Extracted submatrix on row map `rows` and column map `cols`. -/
def submatrix {R : Type u} {m n a b : Nat} (M : Mat R m n)
    (rows : Fin a → Fin m) (cols : Fin b → Fin n) : Mat R a b :=
  fun x y => M (rows x) (cols y)

/-- `P` is locally of rank at most `r`: EVERY fully specified submatrix of ANY size `a × b`
has rank at most `r`. -/
def LocallyRankAtMost (R : Type u) [CommRingR R] {m n : Nat} (r : Nat)
    (P : PartialMatrix R m n) : Prop :=
  ∀ (a b : Nat) (rows : Fin a → Fin m) (cols : Fin b → Fin n),
    (∀ x y, P.spec (rows x) (cols y) = true) →
    HasRankAtMost R r (submatrix P.val rows cols)

end PartialMatrix

/-- `r` is the exact minimum completion rank `mr_R(P) = r` of partial matrix `P`. -/
def IsMinCompletionRank (R : Type u) [CommRingR R] {m n : Nat}
    (P : PartialMatrix R m n) (r : Nat) : Prop :=
  (∃ M : Mat R m n, P.IsCompletion M ∧ HasRankAtMost R r M) ∧
  (∀ r' : Nat, r' < r → ∀ M : Mat R m n, P.IsCompletion M → ¬ HasRankAtMost R r' M)

/-- `r` is the exact symmetric minimum completion rank `smr_R(P) = r` of square partial matrix `P`. -/
def IsMinSymCompletionRank (R : Type u) [CommRingR R] {n : Nat}
    (P : PartialMatrix R n n) (r : Nat) : Prop :=
  (∃ M : Mat R n n, P.IsSymCompletion M ∧ HasRankAtMost R r M) ∧
  (∀ r' : Nat, r' < r → ∀ M : Mat R n n, P.IsSymCompletion M → ¬ HasRankAtMost R r' M)

/-- Uniqueness of exact minimum completion rank. -/
theorem IsMinCompletionRank.unique {R : Type u} [CommRingR R] {m n r₁ r₂ : Nat}
    {P : PartialMatrix R m n}
    (h₁ : IsMinCompletionRank R P r₁) (h₂ : IsMinCompletionRank R P r₂) : r₁ = r₂ := by
  by_cases hlt : r₁ < r₂
  · rcases h₁.1 with ⟨M, hM, hrk⟩
    exact absurd hrk (h₂.2 r₁ hlt M hM)
  · by_cases hgt : r₂ < r₁
    · rcases h₂.1 with ⟨M, hM, hrk⟩
      exact absurd hrk (h₁.2 r₂ hgt M hM)
    · omega

/-- Uniqueness of exact symmetric minimum completion rank. -/
theorem IsMinSymCompletionRank.unique {R : Type u} [CommRingR R] {n r₁ r₂ : Nat}
    {P : PartialMatrix R n n}
    (h₁ : IsMinSymCompletionRank R P r₁) (h₂ : IsMinSymCompletionRank R P r₂) : r₁ = r₂ := by
  by_cases hlt : r₁ < r₂
  · rcases h₁.1 with ⟨M, hM, hrk⟩
    exact absurd hrk (h₂.2 r₁ hlt M hM)
  · by_cases hgt : r₂ < r₁
    · rcases h₂.1 with ⟨M, hM, hrk⟩
      exact absurd hrk (h₁.2 r₂ hgt M hM)
    · omega

end Conjecture00000007178
