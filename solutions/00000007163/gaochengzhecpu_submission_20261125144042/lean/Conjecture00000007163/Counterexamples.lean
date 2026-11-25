/-
  Conjecture 00000007163 — Core Lean 4.19.0 Formalization
  File: Conjecture00000007163/Counterexamples.lean

  Explicit first-principles counterexamples and infinite parametric families
  refuting both clauses of Conjecture 00000007163 across all standard matrix,
  spectral-gap, and positivity-modulus conventions.
-/

import Conjecture00000007163.PositiveBounds

namespace Conjecture00000007163

/-! ## 1. Small-Dimension Helpers, Symbolic Determinants, and Polynomial Expanders -/

theorem finSum2 (f : Fin 2 → Int) :
    finSum 2 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  simp [finSum]

theorem finSum3 (f : Fin 3 → Int) :
    finSum 3 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ := by
  simp [finSum]

theorem finSum4 (f : Fin 4 → Int) :
    finSum 4 f =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
  simp [finSum]

def mat2 (a00 a01 a10 a11 : Int) : IMat 2 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a00
    | 0, 1 => a01
    | 1, 0 => a10
    | _, _ => a11

def vec2 (v0 v1 : Int) : IVec 2 :=
  fun i =>
    match i.val with
    | 0 => v0
    | _ => v1

def mat3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : IMat 3 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a00 | 0, 1 => a01 | 0, _ => a02
    | 1, 0 => a10 | 1, 1 => a11 | 1, _ => a12
    | _, 0 => a20 | _, 1 => a21 | _, _ => a22

def vec3 (v0 v1 v2 : Int) : IVec 3 :=
  fun i =>
    match i.val with
    | 0 => v0
    | 1 => v1
    | _ => v2

def mat4 (a00 a01 a02 a03
          a10 a11 a12 a13
          a20 a21 a22 a23
          a30 a31 a32 a33 : Int) : IMat 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a00 | 0, 1 => a01 | 0, 2 => a02 | 0, _ => a03
    | 1, 0 => a10 | 1, 1 => a11 | 1, 2 => a12 | 1, _ => a13
    | 2, 0 => a20 | 2, 1 => a21 | 2, 2 => a22 | 2, _ => a23
    | _, 0 => a30 | _, 1 => a31 | _, 2 => a32 | _, _ => a33

def vec4 (v0 v1 v2 v3 : Int) : IVec 4 :=
  fun i =>
    match i.val with
    | 0 => v0
    | 1 => v1
    | 2 => v2
    | _ => v3

theorem fin2_cases {P : Fin 2 → Prop} (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) :
    ∀ i : Fin 2, P i := by
  intro ⟨v, hv⟩
  match v with
  | 0 => exact h0
  | 1 => exact h1

theorem fin3_cases {P : Fin 3 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) (h2 : P ⟨2, by decide⟩) :
    ∀ i : Fin 3, P i := by
  intro ⟨v, hv⟩
  match v with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2

theorem fin4_cases {P : Fin 4 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩)
    (h2 : P ⟨2, by decide⟩) (h3 : P ⟨3, by decide⟩) :
    ∀ i : Fin 4, P i := by
  intro ⟨v, hv⟩
  match v with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3

theorem det0_eq (M : IMat 0) : det M = 1 := rfl

theorem det1_eq (M : IMat 1) : det M = M ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  conv => lhs; unfold det
  simp [finSum, det0_eq]

theorem det2_expand (M : IMat 2) :
    det M = M ⟨0, by decide⟩ ⟨0, by decide⟩ * M ⟨1, by decide⟩ ⟨1, by decide⟩ -
            M ⟨0, by decide⟩ ⟨1, by decide⟩ * M ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  conv => lhs; unfold det
  rw [finSum2, det1_eq, det1_eq]
  simp [submatrix, skipFin, Int.neg_mul]
  omega

theorem det3_expand (M : IMat 3) :
    det M =
      M ⟨0, by decide⟩ ⟨0, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨0, by decide⟩) -
      M ⟨0, by decide⟩ ⟨1, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨1, by decide⟩) +
      M ⟨0, by decide⟩ ⟨2, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨2, by decide⟩) := by
  conv => lhs; unfold det
  rw [finSum3]
  simp [Int.neg_mul]
  omega

theorem det4_expand (M : IMat 4) :
    det M =
      M ⟨0, by decide⟩ ⟨0, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨0, by decide⟩) -
      M ⟨0, by decide⟩ ⟨1, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨1, by decide⟩) +
      M ⟨0, by decide⟩ ⟨2, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨2, by decide⟩) -
      M ⟨0, by decide⟩ ⟨3, by decide⟩ * det (submatrix M ⟨0, by decide⟩ ⟨3, by decide⟩) := by
  conv => lhs; unfold det
  rw [finSum4]
  simp [Int.neg_mul]
  omega

theorem charPolyEval_mat2 (a b c d x : Int) :
    charPolyEval (mat2 a b c d) x = (x - a) * (x - d) - b * c := by
  unfold charPolyEval
  rw [det2_expand]
  simp [charMat, mat2, Int.neg_mul, Int.mul_neg]

theorem det_mat3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) :
    det (mat3 a00 a01 a02 a10 a11 a12 a20 a21 a22) =
      a00 * (a11 * a22 - a12 * a21) -
      a01 * (a10 * a22 - a12 * a20) +
      a02 * (a10 * a21 - a11 * a20) := by
  rw [det3_expand, det2_expand, det2_expand, det2_expand]
  rfl

theorem poly2_expand (x a b : Int) :
    (x - a) * (x - b) = x * x + (-(a + b)) * x + a * b := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.neg_mul, Int.add_mul, Int.mul_comm x b]
  omega

theorem linear_mul_quad (x a c1 c0 : Int) :
    (x - a) * (x * x + c1 * x + c0) =
      x * (x * x) + (c1 - a) * (x * x) + (c0 - a * c1) * x - a * c0 := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add,
      Int.sub_mul, Int.sub_mul,
      ← Int.mul_assoc x c1 x, Int.mul_comm x c1, Int.mul_assoc c1 x x,
      Int.mul_comm x c0, ← Int.mul_assoc a c1 x]
  omega

theorem linear_mul_cubic (x a c2 c1 c0 : Int) :
    (x - a) * (x * (x * x) + c2 * (x * x) + c1 * x + c0) =
      x * (x * (x * x)) + (c2 - a) * (x * (x * x)) +
      (c1 - a * c2) * (x * x) + (c0 - a * c1) * x - a * c0 := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_add,
      Int.mul_add, Int.mul_add, Int.mul_add,
      Int.sub_mul, Int.sub_mul, Int.sub_mul,
      ← Int.mul_assoc x c2 (x * x), Int.mul_comm x c2, Int.mul_assoc c2 x (x * x),
      ← Int.mul_assoc x c1 x, Int.mul_comm x c1, Int.mul_assoc c1 x x,
      Int.mul_comm x c0,
      ← Int.mul_assoc a c2 (x * x), ← Int.mul_assoc a c1 x]
  omega

theorem matMul_mat2 (a00 a01 a10 a11 b00 b01 b10 b11 : Int) :
    matMul (mat2 a00 a01 a10 a11) (mat2 b00 b01 b10 b11) =
      mat2 (a00 * b00 + a01 * b10) (a00 * b01 + a01 * b11)
           (a10 * b00 + a11 * b10) (a10 * b01 + a11 * b11) := by
  funext i j
  revert j; revert i
  apply fin2_cases <;> apply fin2_cases <;> simp [matMul, finSum, mat2]

/-! ## 2. Refutation of Clause 1: Spectral Gap Does Not Require Almost-Irreducible Primitivity -/

def pow3 : Nat → Int
  | 0 => 1
  | k + 1 => pow3 k * 3

def diag31 : IMat 2 := mat2 3 0 0 1

theorem matPow_diag31 (k : Nat) :
    matPow diag31 k = mat2 (pow3 k) 0 0 1 := by
  induction k with
  | zero =>
    funext i j; revert j; revert i
    apply fin2_cases <;> apply fin2_cases <;> rfl
  | succ k ih =>
    unfold matPow
    rw [ih]
    unfold diag31
    rw [matMul_mat2]
    simp only [pow3]
    funext i j; revert j; revert i
    apply fin2_cases <;> apply fin2_cases <;> simp [mat2]

theorem diag31_disproves_clause1 :
    IsNonneg diag31 ∧
    (∀ x : Int, charPolyEval diag31 x = (x - 3) * (x - 1)) ∧
    IsEigenpair diag31 3 (vec2 1 0) ∧
    IsEigenpair diag31 1 (vec2 0 1) ∧
    (0 < (3 : Int) - 1) ∧
    ¬ IsIrreducible diag31 ∧
    ¬ IsPrimitive diag31 ∧
    ¬ HasSingleEssentialClass diag31 ∧
    ¬ IsBlockSupportedPrimitive diag31 := by
  have hnot_irr : ¬ IsIrreducible diag31 := by
    intro hirr
    rcases hirr ⟨0, by decide⟩ ⟨1, by decide⟩ with ⟨k, _, hkpos⟩
    rw [matPow_diag31 k] at hkpos
    simp [mat2] at hkpos
  refine ⟨?_, ?_, ?_, ?_, by decide, hnot_irr, ?_, ?_, ?_⟩
  · apply fin2_cases <;> apply fin2_cases <;> decide
  · intro x
    unfold diag31
    rw [charPolyEval_mat2]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide
  · refine ⟨⟨⟨1, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide
  · intro hprim
    exact hnot_irr (primitive_imp_irreducible hprim)
  · intro hsec
    have h0 : ∃ k₁ : Nat, 1 ≤ k₁ ∧ 0 < matPow diag31 k₁ ⟨0, by decide⟩ ⟨0, by decide⟩ :=
      ⟨1, Nat.le_refl 1, by decide⟩
    have h1 : ∃ k₂ : Nat, 1 ≤ k₂ ∧ 0 < matPow diag31 k₂ ⟨1, by decide⟩ ⟨1, by decide⟩ :=
      ⟨1, Nat.le_refl 1, by decide⟩
    rcases hsec ⟨0, by decide⟩ ⟨1, by decide⟩ h0 h1 with ⟨r, _, hrpos⟩
    rw [matPow_diag31 r] at hrpos
    simp [mat2] at hrpos
  · intro ⟨S, _, hzero, ⟨k, _, hkpos⟩⟩
    have hs0 : S ⟨0, by decide⟩ = true := by
      cases hs : S ⟨0, by decide⟩ with
      | true => rfl
      | false =>
        have hz := hzero ⟨0, by decide⟩ ⟨0, by decide⟩ (Or.inl hs)
        simp [diag31, mat2] at hz
    have hs1 : S ⟨1, by decide⟩ = true := by
      cases hs : S ⟨1, by decide⟩ with
      | true => rfl
      | false =>
        have hz := hzero ⟨1, by decide⟩ ⟨1, by decide⟩ (Or.inl hs)
        simp [diag31, mat2] at hz
    have hp := hkpos ⟨0, by decide⟩ ⟨1, by decide⟩ hs0 hs1
    rw [matPow_diag31 k] at hp
    simp [mat2] at hp

def periodicBlock3 : IMat 3 :=
  mat3 3 0 0
       0 0 1
       0 1 0

theorem periodicBlock3_row0_pow (k : Nat) :
    matPow periodicBlock3 k ⟨0, by decide⟩ ⟨0, by decide⟩ = pow3 k ∧
    matPow periodicBlock3 k ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
    matPow periodicBlock3 k ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rcases ih with ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [matPow, matMul, pow3]
      rw [finSum3, h0, h1, h2]
      simp [periodicBlock3, mat3]
    · simp only [matPow, matMul]
      rw [finSum3, h0, h1, h2]
      simp [periodicBlock3, mat3]
    · simp only [matPow, matMul]
      rw [finSum3, h0, h1, h2]
      simp [periodicBlock3, mat3]

theorem periodicBlock3_disproves_clause1 :
    IsNonneg periodicBlock3 ∧
    (∀ x : Int, charPolyEval periodicBlock3 x = (x - 3) * ((x - 1) * (x + 1))) ∧
    IsEigenpair periodicBlock3 3 (vec3 1 0 0) ∧
    IsEigenpair periodicBlock3 1 (vec3 0 1 1) ∧
    IsEigenpair periodicBlock3 (-1) (vec3 0 1 (-1)) ∧
    ¬ IsIrreducible periodicBlock3 ∧
    ¬ IsPrimitive periodicBlock3 ∧
    ¬ HasSingleEssentialClass periodicBlock3 ∧
    ¬ IsBlockSupportedPrimitive periodicBlock3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply fin3_cases <;> apply fin3_cases <;> decide
  · intro x
    have hchar : charMat periodicBlock3 x =
        mat3 (x - 3) 0 0 0 x (-1) 0 (-1) x := by
      funext i j; revert j; revert i
      apply fin3_cases <;> apply fin3_cases <;> simp [charMat, periodicBlock3, mat3]
    unfold charPolyEval
    rw [hchar, det_mat3]
    have hdiff : (x - 1) * (x + 1) = x * x - -1 * -1 := by
      rw [Int.sub_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      omega
    rw [hdiff]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide
  · refine ⟨⟨⟨1, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide
  · refine ⟨⟨⟨1, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide
  · intro hirr
    rcases hirr ⟨0, by decide⟩ ⟨1, by decide⟩ with ⟨k, _, hkpos⟩
    have hz := (periodicBlock3_row0_pow k).2.1
    omega
  · intro hprim
    rcases (primitive_imp_irreducible hprim) ⟨0, by decide⟩ ⟨1, by decide⟩ with ⟨k, _, hkpos⟩
    have hz := (periodicBlock3_row0_pow k).2.1
    omega
  · intro hsec
    have h0 : ∃ k₁ : Nat, 1 ≤ k₁ ∧ 0 < matPow periodicBlock3 k₁ ⟨0, by decide⟩ ⟨0, by decide⟩ :=
      ⟨1, Nat.le_refl 1, by decide⟩
    have h1 : ∃ k₂ : Nat, 1 ≤ k₂ ∧ 0 < matPow periodicBlock3 k₂ ⟨1, by decide⟩ ⟨1, by decide⟩ :=
      ⟨2, by decide, by decide⟩
    rcases hsec ⟨0, by decide⟩ ⟨1, by decide⟩ h0 h1 with ⟨r, _, hrpos⟩
    have hz := (periodicBlock3_row0_pow r).2.1
    omega
  · intro ⟨S, _, hzero, ⟨k, _, hkpos⟩⟩
    have hs0 : S ⟨0, by decide⟩ = true := by
      cases hs : S ⟨0, by decide⟩ with
      | true => rfl
      | false =>
        have hz := hzero ⟨0, by decide⟩ ⟨0, by decide⟩ (Or.inl hs)
        simp [periodicBlock3, mat3] at hz
    have hs1 : S ⟨1, by decide⟩ = true := by
      cases hs : S ⟨1, by decide⟩ with
      | true => rfl
      | false =>
        have hz := hzero ⟨1, by decide⟩ ⟨2, by decide⟩ (Or.inl hs)
        simp [periodicBlock3, mat3] at hz
    have hp := hkpos ⟨0, by decide⟩ ⟨1, by decide⟩ hs0 hs1
    have hz := (periodicBlock3_row0_pow k).2.1
    omega

def cycle2 : IMat 2 := mat2 0 2 2 0

def pow2 : Nat → Int
  | 0 => 1
  | k + 1 => pow2 k * 2

theorem matPow_cycle2_zeros (k : Nat) :
    (k % 2 = 0 → matPow cycle2 k ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
                 matPow cycle2 k ⟨0, by decide⟩ ⟨0, by decide⟩ = pow2 k) ∧
    (k % 2 = 1 → matPow cycle2 k ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
                 matPow cycle2 k ⟨0, by decide⟩ ⟨1, by decide⟩ = pow2 k) := by
  induction k with
  | zero =>
    constructor
    · intro _; decide
    · intro h; cases h
  | succ k ih =>
    rcases ih with ⟨iheven, ihodd⟩
    constructor
    · intro hmod
      have hkodd : k % 2 = 1 := by omega
      rcases ihodd hkodd with ⟨h00, h01⟩
      constructor
      · simp only [matPow, matMul]
        rw [finSum2, h00, h01]; simp [cycle2, mat2]
      · simp only [matPow, matMul, pow2]
        rw [finSum2, h00, h01]; simp [cycle2, mat2]
    · intro hmod
      have hkeven : k % 2 = 0 := by omega
      rcases iheven hkeven with ⟨h01, h00⟩
      constructor
      · simp only [matPow, matMul]
        rw [finSum2, h00, h01]; simp [cycle2, mat2]
      · simp only [matPow, matMul, pow2]
        rw [finSum2, h00, h01]; simp [cycle2, mat2]

theorem cycle2_irreducible_not_primitive :
    IsNonneg cycle2 ∧
    IsIrreducible cycle2 ∧
    ¬ IsPrimitive cycle2 ∧
    (∀ x : Int, charPolyEval cycle2 x = (x - 2) * (x + 2)) ∧
    IsEigenpair cycle2 2 (vec2 1 1) ∧
    IsEigenpair cycle2 (-2) (vec2 1 (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply fin2_cases <;> apply fin2_cases <;> decide
  · apply fin2_cases <;> apply fin2_cases
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
  · intro ⟨k, _, hkpos⟩
    rcases matPow_cycle2_zeros k with ⟨heven, hodd⟩
    by_cases h : k % 2 = 0
    · have hz := (heven h).1
      have hp := hkpos ⟨0, by decide⟩ ⟨1, by decide⟩
      omega
    · have hk1 : k % 2 = 1 := by omega
      have hz := (hodd hk1).1
      have hp := hkpos ⟨0, by decide⟩ ⟨0, by decide⟩
      omega
  · intro x
    unfold cycle2
    rw [charPolyEval_mat2]
    have h2 : x + 2 = x - (-2) := by omega
    rw [h2, poly2_expand x 2 (-2), poly2_expand x 0 0]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide

/-! ## 3. Refutation of Clause 2: Positivity-Modulus Bound Failures -/

def primZeroMod : IMat 2 := mat2 2 3 1 0

theorem primZeroMod_properties :
    IsNonneg primZeroMod ∧
    IsPrimitive primZeroMod ∧
    posModulusMin primZeroMod = 0 ∧
    doeblinModulus primZeroMod = 1 ∧
    (∀ x : Int, charPolyEval primZeroMod x = (x - 3) * (x + 1)) ∧
    IsEigenpair primZeroMod 3 (vec2 3 1) ∧
    IsEigenpair primZeroMod (-1) (vec2 (-1) 1) := by
  refine ⟨?_, ?_, by decide, by decide, ?_, ?_, ?_⟩
  · apply fin2_cases <;> apply fin2_cases <;> decide
  · refine ⟨2, by decide, ?_⟩
    apply fin2_cases <;> apply fin2_cases <;> decide
  · intro x
    unfold primZeroMod
    rw [charPolyEval_mat2, poly2_expand x 2 0]
    have h1 : x + 1 = x - (-1) := by omega
    rw [h1, poly2_expand x 3 (-1)]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin2_cases <;> decide

def symRank1Family (K : Int) : IMat 2 := mat2 (K * K) K K 1
def constDeltaFamily (K : Int) : IMat 2 := mat2 K K 1 1

theorem unbounded_gap_fixed_modulus_families (M : Int) :
    ∃ K : Int, 1 ≤ K ∧
      IsSymmetric (symRank1Family K) ∧
      IsStrictlyPositive (symRank1Family K) ∧
      posModulusMin (symRank1Family K) = 1 ∧
      (∀ x : Int, charPolyEval (symRank1Family K) x = x * (x - (K * K + 1))) ∧
      IsEigenpair (symRank1Family K) (K * K + 1) (vec2 K 1) ∧
      IsEigenpair (symRank1Family K) 0 (vec2 1 (-K)) ∧
      M < (K * K + 1) - 0 ∧
      IsStrictlyPositive (constDeltaFamily K) ∧
      posModulusMin (constDeltaFamily K) = 1 ∧
      doeblinModulus (constDeltaFamily K) = 2 ∧
      (∀ x : Int, charPolyEval (constDeltaFamily K) x = x * (x - (K + 1))) ∧
      IsEigenpair (constDeltaFamily K) (K + 1) (vec2 K 1) ∧
      IsEigenpair (constDeltaFamily K) 0 (vec2 1 (-1)) ∧
      M < (K + 1) - 0 := by
  let K : Int := if 1 ≤ M then M + 1 else 1
  have hK : 1 ≤ K := by dsimp [K]; split <;> omega
  have hM_lt_K : M < K + 1 := by dsimp [K]; split <;> omega
  have hKK : K ≤ K * K := by
    have hm := Int.mul_le_mul hK (Int.le_refl K) (by omega) (by omega)
    omega
  refine ⟨K, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply fin2_cases <;> apply fin2_cases <;> rfl
  · apply fin2_cases <;> apply fin2_cases
    · simp [symRank1Family, mat2]; omega
    · simp [symRank1Family, mat2]; omega
    · simp [symRank1Family, mat2]; omega
    · simp [symRank1Family, mat2]
  · unfold posModulusMin symRank1Family
    simp only [finMin, mat2]
    split <;> split <;> omega
  · intro x
    unfold symRank1Family
    rw [charPolyEval_mat2, poly2_expand x (K * K) 1]
    have hx0 : x = x - 0 := by omega
    conv => rhs; arg 1; rw [hx0]
    rw [poly2_expand x 0 (K * K + 1)]
    have hneg : -(0 + (K * K + 1)) = -(K * K + 1) := by omega
    rw [hneg]
    omega
  · refine ⟨⟨⟨1, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, symRank1Family, mat2, vec2]
      rw [Int.add_mul]
      omega
    · simp [matVec, finSum, symRank1Family, mat2, vec2]
  · refine ⟨⟨⟨0, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, symRank1Family, mat2, vec2]
      rw [Int.mul_neg]; omega
    · simp [matVec, finSum, symRank1Family, mat2, vec2]
      omega
  · omega
  · apply fin2_cases <;> apply fin2_cases
    · simp [constDeltaFamily, mat2]; omega
    · simp [constDeltaFamily, mat2]; omega
    · simp [constDeltaFamily, mat2]
    · simp [constDeltaFamily, mat2]
  · unfold posModulusMin constDeltaFamily
    simp only [finMin, mat2]
    split <;> split <;> omega
  · unfold doeblinModulus colMin constDeltaFamily
    rw [finSum2]
    simp only [finMin, mat2]
    split <;> omega
  · intro x
    unfold constDeltaFamily
    rw [charPolyEval_mat2, poly2_expand x K 1]
    have hx0 : x = x - 0 := by omega
    conv => rhs; arg 1; rw [hx0]
    rw [poly2_expand x 0 (K + 1)]
    have hneg : -(0 + (K + 1)) = -(K + 1) := by omega
    rw [hneg]
    omega
  · refine ⟨⟨⟨1, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, constDeltaFamily, mat2, vec2]
      rw [Int.add_mul]; omega
    · simp [matVec, finSum, constDeltaFamily, mat2, vec2]
  · refine ⟨⟨⟨0, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, constDeltaFamily, mat2, vec2]; omega
    · simp [matVec, finSum, constDeltaFamily, mat2, vec2]
  · omega

def doeblinFail3 : IMat 3 :=
  mat3 7 2 2
       2 7 2
       2 2 2

theorem doeblinFail3_properties :
    IsSymmetric doeblinFail3 ∧
    IsStrictlyPositive doeblinFail3 ∧
    posModulusMin doeblinFail3 = 2 ∧
    doeblinModulus doeblinFail3 = 6 ∧
    (∀ x : Int, charPolyEval doeblinFail3 x = (x - 10) * ((x - 5) * (x - 1))) ∧
    IsEigenpair doeblinFail3 10 (vec3 2 2 1) ∧
    IsEigenpair doeblinFail3 5 (vec3 1 (-1) 0) ∧
    IsEigenpair doeblinFail3 1 (vec3 1 1 (-4)) ∧
    posModulusMin doeblinFail3 < 10 - 5 ∧
    10 - 5 < doeblinModulus doeblinFail3 := by
  refine ⟨?_, ?_, by decide, by decide, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · apply fin3_cases <;> apply fin3_cases <;> decide
  · apply fin3_cases <;> apply fin3_cases <;> decide
  · intro x
    have hchar : charMat doeblinFail3 x =
        mat3 (x - 7) (-2) (-2) (-2) (x - 7) (-2) (-2) (-2) (x - 2) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    unfold charPolyEval
    rw [hchar, det_mat3]
    have hs1 : (x - 7) * (x - 2) - -2 * -2 = x * x + (-9) * x + 10 := by
      rw [poly2_expand x 7 2]; omega
    have hs2 : -2 * (x - 2) - -2 * -2 = (-2) * x := by
      rw [Int.mul_sub]; omega
    have hs3 : -2 * -2 - (x - 7) * -2 = 2 * x - 10 := by
      rw [Int.sub_mul]; omega
    rw [hs1, hs2, hs3, linear_mul_quad x 7 (-9) 10, poly2_expand x 5 1]
    have s51 : x * x + -(5 + 1) * x + 5 * 1 = x * x + (-6) * x + 5 := by omega
    rw [s51, linear_mul_quad x 10 (-6) 5]
    have t1 : (-2) * ((-2) * x) = 4 * x := by
      rw [← Int.mul_assoc (-2) (-2) x]; rfl
    have t2 : (-2) * (2 * x - 10) = (-4) * x + 20 := by
      rw [Int.mul_sub, ← Int.mul_assoc (-2) 2 x]; omega
    rw [t1, t2]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin3_cases <;> decide

def doeblinFail4 : IMat 4 :=
  mat4 4 1 1 1
       1 4 1 1
       1 1 1 1
       1 1 1 1

theorem doeblinFail4_properties :
    IsSymmetric doeblinFail4 ∧
    IsStrictlyPositive doeblinFail4 ∧
    posModulusMin doeblinFail4 = 1 ∧
    doeblinModulus doeblinFail4 = 4 ∧
    (∀ x : Int, charPolyEval doeblinFail4 x = x * ((x - 6) * ((x - 3) * (x - 1)))) ∧
    IsEigenpair doeblinFail4 6 (vec4 2 2 1 1) ∧
    IsEigenpair doeblinFail4 3 (vec4 1 (-1) 0 0) ∧
    IsEigenpair doeblinFail4 1 (vec4 1 1 (-2) (-2)) ∧
    IsEigenpair doeblinFail4 0 (vec4 0 0 1 (-1)) ∧
    posModulusMin doeblinFail4 < 6 - 3 ∧
    6 - 3 < doeblinModulus doeblinFail4 := by
  refine ⟨?_, ?_, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · apply fin4_cases <;> apply fin4_cases <;> decide
  · apply fin4_cases <;> apply fin4_cases <;> decide
  · intro x
    have hs0 : submatrix (charMat doeblinFail4 x) ⟨0, by decide⟩ ⟨0, by decide⟩ =
        mat3 (x - 4) (-1) (-1) (-1) (x - 1) (-1) (-1) (-1) (x - 1) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs1 : submatrix (charMat doeblinFail4 x) ⟨0, by decide⟩ ⟨1, by decide⟩ =
        mat3 (-1) (-1) (-1) (-1) (x - 1) (-1) (-1) (-1) (x - 1) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs2 : submatrix (charMat doeblinFail4 x) ⟨0, by decide⟩ ⟨2, by decide⟩ =
        mat3 (-1) (x - 4) (-1) (-1) (-1) (-1) (-1) (-1) (x - 1) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs3 : submatrix (charMat doeblinFail4 x) ⟨0, by decide⟩ ⟨3, by decide⟩ =
        mat3 (-1) (x - 4) (-1) (-1) (-1) (x - 1) (-1) (-1) (-1) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    unfold charPolyEval
    rw [det4_expand, hs0, hs1, hs2, hs3, det_mat3, det_mat3, det_mat3, det_mat3]
    have c0 : charMat doeblinFail4 x ⟨0, by decide⟩ ⟨0, by decide⟩ = x - 4 := rfl
    have c1 : charMat doeblinFail4 x ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 := rfl
    have c2 : charMat doeblinFail4 x ⟨0, by decide⟩ ⟨2, by decide⟩ = -1 := rfl
    have c3 : charMat doeblinFail4 x ⟨0, by decide⟩ ⟨3, by decide⟩ = -1 := rfl
    rw [c0, c1, c2, c3]
    have q11 : (x - 1) * (x - 1) - -1 * -1 = x * x + (-2) * x + 0 := by
      rw [poly2_expand x 1 1]; omega
    have l1 : -1 * (x - 1) - -1 * -1 = -x := by rw [Int.neg_mul]; omega
    have l2 : -1 * -1 - (x - 1) * -1 = x := by
      have s : (x - 1) * -1 = -x + 1 := by rw [Int.sub_mul]; omega
      rw [s]; omega
    have m0 : (x - 4) * ((x - 1) * (x - 1) - -1 * -1) -
              -1 * (-1 * (x - 1) - -1 * -1) +
              -1 * (-1 * -1 - (x - 1) * -1) =
              x * (x * x) + (-6) * (x * x) + 6 * x + 0 := by
      rw [q11, l1, l2, linear_mul_quad x 4 (-2) 0]; omega
    have m1 : -1 * ((x - 1) * (x - 1) - -1 * -1) -
              -1 * (-1 * (x - 1) - -1 * -1) +
              -1 * (-1 * -1 - (x - 1) * -1) =
              -(x * x) := by
      have s : -1 * (x * x + (-2) * x + 0) = -(x * x) + 2 * x := by
        rw [Int.mul_add, Int.mul_add, ← Int.mul_assoc (-1) (-2) x]; omega
      rw [q11, l1, l2, s]; omega
    have m2 : -1 * (-1 * (x - 1) - -1 * -1) -
              (x - 4) * (-1 * (x - 1) - -1 * -1) +
              -1 * (-1 * -1 - -1 * -1) =
              x * x + (-3) * x := by
      rw [l1]
      have p : (x - 4) * -x = -(x * x) + 4 * x := by
        rw [Int.sub_mul, Int.mul_neg, Int.mul_neg]; omega
      rw [p]; omega
    have m3 : -1 * (-1 * -1 - (x - 1) * -1) -
              (x - 4) * (-1 * -1 - (x - 1) * -1) +
              -1 * (-1 * -1 - -1 * -1) =
              -(x * x) + 3 * x := by
      rw [l2, Int.sub_mul x 4 x]
      have h1 : -1 * x = -x := by rw [Int.neg_mul, Int.one_mul]
      have h0 : -1 * (-1 * -1 - -1 * -1) = (0 : Int) := rfl
      rw [h1, h0]
      omega
    rw [m0, m1, m2, m3, linear_mul_cubic x 4 (-6) 6 0]
    have rhs_exp : x * ((x - 6) * ((x - 3) * (x - 1))) =
        x * (x * (x * x)) + (-10) * (x * (x * x)) + 27 * (x * x) + (-18) * x := by
      rw [poly2_expand x 3 1]
      have s31 : x * x + -(3 + 1) * x + 3 * 1 = x * x + (-4) * x + 3 := by omega
      rw [s31, linear_mul_quad x 6 (-4) 3]
      have s : x * (x * x) + (-4 - 6) * (x * x) + (3 - 6 * -4) * x - 6 * 3 =
          x * (x * x) + (-10) * (x * x) + 27 * x + (-18) := by omega
      rw [s, Int.mul_add, Int.mul_add, Int.mul_add,
          ← Int.mul_assoc x (-10) (x * x), Int.mul_comm x (-10), Int.mul_assoc (-10) x (x * x),
          ← Int.mul_assoc x 27 x, Int.mul_comm x 27, Int.mul_assoc 27 x x,
          Int.mul_comm x (-18)]
    rw [rhs_exp]
    omega
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨2, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide

def stochasticScaled4 : IMat 4 :=
  mat4 3 3 3 1
       3 3 1 3
       3 1 3 3
       1 3 3 3

theorem stochasticScaled4_properties :
    IsSymmetric stochasticScaled4 ∧
    IsStrictlyPositive stochasticScaled4 ∧
    HasConstantRowSum stochasticScaled4 10 ∧
    posModulusMin stochasticScaled4 = 1 ∧
    doeblinModulus stochasticScaled4 = 4 ∧
    IsEigenpair stochasticScaled4 10 (vec4 1 1 1 1) ∧
    IsEigenpair stochasticScaled4 2 (vec4 1 1 (-1) (-1)) ∧
    IsEigenpair stochasticScaled4 2 (vec4 1 (-1) 1 (-1)) ∧
    IsEigenpair stochasticScaled4 (-2) (vec4 1 (-1) (-1) 1) ∧
    (∀ x : Int, charPolyEval stochasticScaled4 x =
      (x - 10) * ((x - 2) * ((x - 2) * (x + 2)))) ∧
    doeblinModulus stochasticScaled4 < 10 - 2 := by
  refine ⟨?_, ?_, ?_, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · apply fin4_cases <;> apply fin4_cases <;> decide
  · apply fin4_cases <;> apply fin4_cases <;> decide
  · apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · refine ⟨⟨⟨0, by decide⟩, by decide⟩, ?_⟩
    funext i; revert i; apply fin4_cases <;> decide
  · intro x
    have hs0 : submatrix (charMat stochasticScaled4 x) ⟨0, by decide⟩ ⟨0, by decide⟩ =
        mat3 (x - 3) (-1) (-3) (-1) (x - 3) (-3) (-3) (-3) (x - 3) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs1 : submatrix (charMat stochasticScaled4 x) ⟨0, by decide⟩ ⟨1, by decide⟩ =
        mat3 (-3) (-1) (-3) (-3) (x - 3) (-3) (-1) (-3) (x - 3) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs2 : submatrix (charMat stochasticScaled4 x) ⟨0, by decide⟩ ⟨2, by decide⟩ =
        mat3 (-3) (x - 3) (-3) (-3) (-1) (-3) (-1) (-3) (x - 3) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    have hs3 : submatrix (charMat stochasticScaled4 x) ⟨0, by decide⟩ ⟨3, by decide⟩ =
        mat3 (-3) (x - 3) (-1) (-3) (-1) (x - 3) (-1) (-3) (-3) := by
      funext i j; revert j; revert i; apply fin3_cases <;> apply fin3_cases <;> rfl
    unfold charPolyEval
    rw [det4_expand, hs0, hs1, hs2, hs3, det_mat3, det_mat3, det_mat3, det_mat3]
    have c0 : charMat stochasticScaled4 x ⟨0, by decide⟩ ⟨0, by decide⟩ = x - 3 := rfl
    have c1 : charMat stochasticScaled4 x ⟨0, by decide⟩ ⟨1, by decide⟩ = -3 := rfl
    have c2 : charMat stochasticScaled4 x ⟨0, by decide⟩ ⟨2, by decide⟩ = -3 := rfl
    have c3 : charMat stochasticScaled4 x ⟨0, by decide⟩ ⟨3, by decide⟩ = -1 := rfl
    rw [c0, c1, c2, c3]
    have q33 : (x - 3) * (x - 3) - -3 * -3 = x * x + (-6) * x + 0 := by
      rw [poly2_expand x 3 3]; omega
    have l33 : -3 * (-1 * -3 - (x - 3) * -3) = (-9) * x + 18 := by
      have s : -1 * -3 - (x - 3) * -3 = 3 * x - 6 := by rw [Int.sub_mul]; omega
      rw [s, Int.mul_sub, ← Int.mul_assoc (-3) 3 x]; omega
    have m0 : (x - 3) * ((x - 3) * (x - 3) - -3 * -3) -
              -1 * (-1 * (x - 3) - -3 * -3) +
              -3 * (-1 * -3 - (x - 3) * -3) =
              x * (x * x) + (-9) * (x * x) + 8 * x + 12 := by
      rw [q33, linear_mul_quad x 3 (-6) 0, l33]
      have l1 : -1 * (-1 * (x - 3) - -3 * -3) = x + 6 := by rw [Int.neg_mul]; omega
      rw [l1]; omega
    have m1 : -3 * ((x - 3) * (x - 3) - -3 * -3) -
              -1 * (-3 * (x - 3) - -3 * -1) +
              -3 * (-3 * -3 - (x - 3) * -1) =
              (-3) * (x * x) + 12 * x - 12 := by
      rw [q33, Int.mul_add, Int.mul_add, ← Int.mul_assoc (-3) (-6) x]
      have l1 : -1 * (-3 * (x - 3) - -3 * -1) = 3 * x - 6 := by rw [Int.mul_sub]; omega
      have l2 : -3 * (-3 * -3 - (x - 3) * -1) = (-3) * x - 18 := by
        have s : -3 * -3 - (x - 3) * -1 = x + 6 := by rw [Int.sub_mul]; omega
        rw [s, Int.mul_add]; omega
      rw [l1, l2]; omega
    have m2 : -3 * (-1 * (x - 3) - -3 * -3) -
              (x - 3) * (-3 * (x - 3) - -3 * -1) +
              -3 * (-3 * -3 - -1 * -1) =
              3 * (x * x) - 12 * x + 12 := by
      have l1 : -3 * (-1 * (x - 3) - -3 * -3) = 3 * x + 18 := by
        rw [Int.neg_mul, Int.mul_sub]; omega
      have l2 : -3 * (x - 3) - -3 * -1 = (-3) * x + 6 := by rw [Int.mul_sub]; omega
      have l3 : (x - 3) * ((-3) * x + 6) = (-3) * (x * x) + 15 * x - 18 := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add,
            ← Int.mul_assoc x (-3) x, Int.mul_comm x (-3), Int.mul_assoc (-3) x x,
            ← Int.mul_assoc 3 (-3) x]
        omega
      rw [l1, l2, l3]; omega
    have m3 : -3 * (-1 * -3 - (x - 3) * -3) -
              (x - 3) * (-3 * -3 - (x - 3) * -1) +
              -1 * (-3 * -3 - -1 * -1) =
              -(x * x) + (-12) * x + 28 := by
      have l2 : -3 * -3 - (x - 3) * -1 = x - (-6) := by
        have s : (x - 3) * -1 = -x + 3 := by rw [Int.sub_mul]; omega
        rw [s]; omega
      rw [l33, l2, poly2_expand x 3 (-6)]
      omega
    rw [m0, m1, m2, m3, linear_mul_cubic x 3 (-9) 8 12]
    have t1 : (-3) * ((-3) * (x * x) + 12 * x - 12) = 9 * (x * x) - 36 * x + 36 := by
      rw [Int.mul_sub, Int.mul_add, ← Int.mul_assoc (-3) (-3) (x * x), ← Int.mul_assoc (-3) 12 x]
      omega
    have t2 : (-3) * (3 * (x * x) - 12 * x + 12) = (-9) * (x * x) + 36 * x - 36 := by
      rw [Int.mul_add, Int.mul_sub, ← Int.mul_assoc (-3) 3 (x * x), ← Int.mul_assoc (-3) 12 x]
      omega
    have rhs_exp : (x - 10) * ((x - 2) * ((x - 2) * (x + 2))) =
        x * (x * (x * x)) + (-12) * (x * (x * x)) + 16 * (x * x) + 48 * x - 80 := by
      have h2 : x + 2 = x - (-2) := by omega
      rw [h2, poly2_expand x 2 (-2)]
      have s0 : x * x + -(2 + -2) * x + 2 * -2 = x * x + 0 * x + (-4) := by omega
      rw [s0, linear_mul_quad x 2 0 (-4)]
      have s1 : x * (x * x) + (0 - 2) * (x * x) + (-4 - 2 * 0) * x - 2 * -4 =
          x * (x * x) + (-2) * (x * x) + (-4) * x + 8 := by omega
      rw [s1, linear_mul_cubic x 10 (-2) (-4) 8]
      omega
    rw [t1, t2, rhs_exp]
    omega

def ratioGapFamily (p : Int) : IMat 2 :=
  mat2 (p * p + 2 * p - 3) (2 * p) (2 * p) (2 * p + 1)

theorem ratioGapFamily_properties (p : Int) (hp : 2 ≤ p) :
    IsSymmetric (ratioGapFamily p) ∧
    IsStrictlyPositive (ratioGapFamily p) ∧
    posModulusMin (ratioGapFamily p) = intMin (p * p + 2 * p - 3) (2 * p) ∧
    entryMax (ratioGapFamily p) =
      (if p * p + 2 * p - 3 ≤ 2 * p + 1 then 2 * p + 1 else p * p + 2 * p - 3) ∧
    (∀ x : Int, charPolyEval (ratioGapFamily p) x =
      (x - (p + 1) * (p + 1)) * (x - (2 * p - 3))) ∧
    IsEigenpair (ratioGapFamily p) ((p + 1) * (p + 1)) (vec2 p 2) ∧
    IsEigenpair (ratioGapFamily p) (2 * p - 3) (vec2 2 (-p)) := by
  have hpp : 4 ≤ p * p := Int.mul_le_mul hp hp (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply fin2_cases <;> apply fin2_cases <;> rfl
  · apply fin2_cases <;> apply fin2_cases <;> (simp [ratioGapFamily, mat2]; omega)
  · unfold posModulusMin ratioGapFamily
    simp only [finMin, intMin, mat2]
    split <;> split <;> omega
  · unfold entryMax ratioGapFamily
    simp only [finMax, mat2]
    split <;> split <;> omega
  · intro x
    unfold ratioGapFamily
    rw [charPolyEval_mat2,
        poly2_expand x (p * p + 2 * p - 3) (2 * p + 1),
        poly2_expand x ((p + 1) * (p + 1)) (2 * p - 3)]
    have hp1 : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by
      rw [Int.add_mul, Int.mul_add]; omega
    have htr : -((p * p + 2 * p - 3) + (2 * p + 1)) =
               -(((p + 1) * (p + 1)) + (2 * p - 3)) := by
      rw [hp1]; omega
    have hconst : (p * p + 2 * p - 3) * (2 * p + 1) - 2 * p * (2 * p) =
                  ((p + 1) * (p + 1)) * (2 * p - 3) := by
      rw [hp1, Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul, Int.add_mul,
          Int.add_mul, Int.add_mul]
      have c1 : (p * p) * (2 * p) = 2 * (p * (p * p)) := by
        rw [← Int.mul_assoc (p * p) 2 p, Int.mul_comm (p * p) 2, Int.mul_assoc 2 (p * p) p,
            Int.mul_assoc p p p]
      have c2 : 2 * p * (2 * p) = 4 * (p * p) := by
        calc
          (2 * p) * (2 * p) = (2 * 2) * (p * p) := (int_mul_self_mul_self 2 p).symm
          _ = 4 * (p * p) := rfl
      rw [c1, c2]; omega
    rw [htr]; omega
  · refine ⟨⟨⟨1, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, ratioGapFamily, mat2, vec2]
      have hp1 : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by rw [Int.add_mul, Int.mul_add]; omega
      rw [hp1, Int.sub_mul, Int.add_mul, Int.add_mul, Int.add_mul]; omega
    · simp [matVec, finSum, ratioGapFamily, mat2, vec2]
      have hp1 : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by rw [Int.add_mul, Int.mul_add]; omega
      have hc : 2 * p * p = p * p * 2 := by
        rw [Int.mul_assoc 2 p p, Int.mul_comm 2 (p * p)]
      rw [hp1, Int.add_mul, Int.add_mul, hc]; omega
  · refine ⟨⟨⟨0, by decide⟩, by simp [vec2]⟩, ?_⟩
    funext i; revert i; apply fin2_cases
    · simp [matVec, finSum, ratioGapFamily, mat2, vec2]
      have hc : 2 * p * p = p * p * 2 := by
        rw [Int.mul_assoc 2 p p, Int.mul_comm 2 (p * p)]
      rw [Int.sub_mul, Int.add_mul, Int.mul_neg, hc]
      omega
    · simp [matVec, finSum, ratioGapFamily, mat2, vec2]
      rw [Int.add_mul, Int.sub_mul, Int.mul_neg, Int.mul_neg, Int.mul_neg]
      have hc : 2 * p * 2 = 4 * p := by
        rw [Int.mul_assoc 2 p 2, Int.mul_comm p 2, ← Int.mul_assoc 2 2 p]; rfl
      rw [hc]; omega

theorem ratioGapFamily_arbitrage (N : Int) (hN : 1 ≤ N) :
    ∃ p : Int, 3 ≤ p ∧
      let A := ratioGapFamily p
      let lam₁ := (p + 1) * (p + 1)
      let lam₂ := 2 * p - 3
      N * posModulusMin A < entryMax A ∧
      N * (A ⟨0, by decide⟩ ⟨1, by decide⟩ * A ⟨1, by decide⟩ ⟨0, by decide⟩) <
        A ⟨0, by decide⟩ ⟨0, by decide⟩ * A ⟨1, by decide⟩ ⟨1, by decide⟩ ∧
      (N - 1) * lam₁ < N * (lam₁ - lam₂) := by
  let p : Int := 2 * N + 3
  have hp3 : 3 ≤ p := by dsimp [p]; omega
  have hp2 : 2 ≤ p := by omega
  rcases ratioGapFamily_properties p hp2 with ⟨_, _, hpmin, hpmax, _, _, _⟩
  refine ⟨p, hp3, ?_⟩
  dsimp only
  have hp5 : 5 ≤ p := by dsimp [p]; omega
  have hpp : 5 * p ≤ p * p := Int.mul_le_mul hp5 (Int.le_refl p) (by omega) (by omega)
  have hmin_eq : posModulusMin (ratioGapFamily p) = 2 * p := by
    rw [hpmin]
    unfold intMin
    split <;> omega
  have hmax_eq : entryMax (ratioGapFamily p) = p * p + 2 * p - 3 := by
    rw [hpmax]
    split <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hmin_eq, hmax_eq]
    have h2N : N * (2 * p) = (p - 3) * p := by
      have hpdef : 2 * N = p - 3 := by dsimp [p]; omega
      rw [← Int.mul_assoc N 2 p, Int.mul_comm N 2, hpdef]
    rw [h2N, Int.sub_mul]
    omega
  · change N * ((2 * p) * (2 * p)) < (p * p + 2 * p - 3) * (2 * p + 1)
    have h4 : (2 * p) * (2 * p) = 4 * (p * p) := by
      calc
        (2 * p) * (2 * p) = (2 * 2) * (p * p) := (int_mul_self_mul_self 2 p).symm
        _ = 4 * (p * p) := rfl
    have hlhs : N * ((2 * p) * (2 * p)) = 2 * (p * (p * p)) - 6 * (p * p) := by
      have hpdef : 4 * N = 2 * p - 6 := by dsimp [p]; omega
      rw [h4, ← Int.mul_assoc N 4 (p * p), Int.mul_comm N 4, hpdef, Int.sub_mul,
          ← Int.mul_assoc 2 p (p * p)]
    have hrhs : (p * p + 2 * p - 3) * (2 * p + 1) =
        2 * (p * (p * p)) + 5 * (p * p) - 4 * p - 3 := by
      rw [Int.mul_add, Int.sub_mul, Int.add_mul,
          ← Int.mul_assoc (p * p) 2 p, Int.mul_comm (p * p) 2, Int.mul_assoc 2 (p * p) p,
          Int.mul_assoc p p p, h4]
      omega
    rw [hlhs, hrhs]; omega
  · have hp1 : (p + 1) * (p + 1) = p * p + 2 * p + 1 := by
      rw [Int.add_mul, Int.mul_add]; omega
    have hdiff : (N - 1) * ((p + 1) * (p + 1)) =
        N * ((p + 1) * (p + 1)) - (p + 1) * (p + 1) := by
      rw [Int.sub_mul]; omega
    have hrhs : N * ((p + 1) * (p + 1) - (2 * p - 3)) =
        N * ((p + 1) * (p + 1)) - N * (2 * p - 3) := Int.mul_sub _ _ _
    have hN2p : 2 * (N * (2 * p - 3)) = (p - 3) * (2 * p - 3) := by
      have hpdef : 2 * N = p - 3 := by dsimp [p]; omega
      rw [← Int.mul_assoc 2 N (2 * p - 3), hpdef]
    have hexp : (p - 3) * (2 * p - 3) = 2 * (p * p) - 9 * p + 9 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub,
          ← Int.mul_assoc p 2 p, Int.mul_comm p 2, Int.mul_assoc 2 p p]
      omega
    have hcmp : 2 * (N * (2 * p - 3)) < 2 * ((p + 1) * (p + 1)) := by
      rw [hN2p, hexp, hp1, Int.mul_add, Int.mul_add]
      omega
    omega

end Conjecture00000007163
