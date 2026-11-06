import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option linter.unnecessarySeqFocus false

namespace TLMC2761

@[irreducible] def powerWord {R : Type*} [Ring R] (x a b c : R) (e0 e1 e2 e3 : ℕ) : R :=
  x^e0*a*x^e1*b*x^e2*c*x^e3

def block {R : Type*} [Ring R] (x a b c : R) : R :=
    powerWord x a b c 3 0 0 0
     + powerWord x a b c 2 1 0 0
     + powerWord x a b c 2 0 1 0
     + powerWord x a b c 2 0 0 1
     - powerWord x a b c 1 2 0 0
     + powerWord x a b c 1 1 1 0
     - powerWord x a b c 1 1 0 1
     + powerWord x a b c 1 0 2 0
     + powerWord x a b c 1 0 1 1
     - powerWord x a b c 1 0 0 2
     - powerWord x a b c 0 3 0 0
     - powerWord x a b c 0 2 1 0
     - powerWord x a b c 0 2 0 1
     + powerWord x a b c 0 1 2 0
     - powerWord x a b c 0 1 1 1
     - powerWord x a b c 0 1 0 2
     + powerWord x a b c 0 0 3 0
     + powerWord x a b c 0 0 2 1
     - powerWord x a b c 0 0 1 2
     - powerWord x a b c 0 0 0 3

@[irreducible] def weakPolynomial {R : Type*} [Ring R] (x a b c : R) : R :=
  block x a b c - block x a c b - block x b a c +
    block x b c a + block x c a b - block x c b a

@[simp] theorem vec3_apply_2 {R : Type*} (x0 x1 x2 : R) :
    (![ x0,x1,x2 ] : Fin 3 → R) 2 = x2 := rfl

@[simp] theorem vec4_apply_2 {R : Type*} (x0 x1 x2 x3 : R) :
    (![ x0,x1,x2,x3 ] : Fin 4 → R) 2 = x2 := rfl

@[simp] theorem vec4_apply_3 {R : Type*} (x0 x1 x2 x3 : R) :
    (![ x0,x1,x2,x3 ] : Fin 4 → R) 3 = x3 := rfl

@[simp] theorem vec6_apply_2 {R : Type*} (x0 x1 x2 x3 x4 x5 : R) :
    (![ x0,x1,x2,x3,x4,x5 ] : Fin 6 → R) 2 = x2 := rfl

@[simp] theorem vec6_apply_3 {R : Type*} (x0 x1 x2 x3 x4 x5 : R) :
    (![ x0,x1,x2,x3,x4,x5 ] : Fin 6 → R) 3 = x3 := rfl

@[simp] theorem vec6_apply_4 {R : Type*} (x0 x1 x2 x3 x4 x5 : R) :
    (![ x0,x1,x2,x3,x4,x5 ] : Fin 6 → R) 4 = x4 := rfl

@[simp] theorem vec6_apply_5 {R : Type*} (x0 x1 x2 x3 x4 x5 : R) :
    (![ x0,x1,x2,x3,x4,x5 ] : Fin 6 → R) 5 = x5 := rfl

abbrev Mat := Matrix (Fin 3) (Fin 3) ℚ

def tracelessMatrix (x : Fin 8 → ℚ) : Mat := fun i j =>
  match i.val, j.val with
  | 0, 0 => x 0
  | 0, 1 => x 1
  | 0, _ => x 2
  | 1, 0 => x 3
  | 1, 1 => x 4
  | 1, _ => x 5
  | _, 0 => x 6
  | _, 1 => x 7
  | _, _ => -x 0-x 4

noncomputable def monomialMap (x : Mat) (e0 e1 e2 e3 : ℕ) :
    MultilinearMap ℚ (fun _ : Fin 3 => Mat) Mat :=
  (LinearMap.mulRight ℚ (x ^ e3)).compMultilinearMap
    ((MultilinearMap.mkPiAlgebraFin ℚ 3 Mat).compLinearMap
      ![LinearMap.mulLeft ℚ (x ^ e0), LinearMap.mulLeft ℚ (x ^ e1),
        LinearMap.mulLeft ℚ (x ^ e2)])

theorem monomialMap_apply (x : Mat) (e0 e1 e2 e3 : ℕ) (v : Fin 3 → Mat) :
    monomialMap x e0 e1 e2 e3 v =
      x ^ e0 * v 0 * x ^ e1 * v 1 * x ^ e2 * v 2 * x ^ e3 := by
  simp [monomialMap, MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

noncomputable def blockMap (x : Mat) :
    MultilinearMap ℚ (fun _ : Fin 3 => Mat) Mat :=
    monomialMap x 3 0 0 0
     + monomialMap x 2 1 0 0
     + monomialMap x 2 0 1 0
     + monomialMap x 2 0 0 1
     - monomialMap x 1 2 0 0
     + monomialMap x 1 1 1 0
     - monomialMap x 1 1 0 1
     + monomialMap x 1 0 2 0
     + monomialMap x 1 0 1 1
     - monomialMap x 1 0 0 2
     - monomialMap x 0 3 0 0
     - monomialMap x 0 2 1 0
     - monomialMap x 0 2 0 1
     + monomialMap x 0 1 2 0
     - monomialMap x 0 1 1 1
     - monomialMap x 0 1 0 2
     + monomialMap x 0 0 3 0
     + monomialMap x 0 0 2 1
     - monomialMap x 0 0 1 2
     - monomialMap x 0 0 0 3

theorem blockMap_apply (x : Mat) (v : Fin 3 → Mat) :
    blockMap x v = block x (v 0) (v 1) (v 2) := by
  simp [blockMap, monomialMap_apply, block, powerWord, mul_assoc]

noncomputable def weakMap (x : Mat) :
    MultilinearMap ℚ (fun _ : Fin 3 => Mat) Mat :=
  blockMap x - (blockMap x).domDomCongr (Equiv.swap 1 2) -
    (blockMap x).domDomCongr (Equiv.swap 0 1) +
    (blockMap x).domDomCongr ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) +
    (blockMap x).domDomCongr ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) -
    (blockMap x).domDomCongr (Equiv.swap 0 2)

theorem weakMap_apply (x : Mat) (v : Fin 3 → Mat) :
    weakMap x v = weakPolynomial x (v 0) (v 1) (v 2) := by
  simp [weakMap, blockMap_apply, weakPolynomial, Equiv.swap_apply_def]

def entry00 : Mat →ₗ[ℚ] ℚ where
  toFun a := a 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def weak00Map (x : Mat) :
    MultilinearMap ℚ (fun _ : Fin 3 => Mat) ℚ :=
  entry00.compMultilinearMap (weakMap x)

theorem weak_same12 (x a c : Mat) : weakPolynomial x a a c = 0 := by
  unfold weakPolynomial
  abel

theorem weak_same23 (x a b : Mat) : weakPolynomial x a b b = 0 := by
  unfold weakPolynomial
  abel

theorem weak_swap12 (x a b c : Mat) :
    weakPolynomial x b a c = -weakPolynomial x a b c := by
  unfold weakPolynomial
  abel

theorem weak_cyclic (x a b c : Mat) :
    weakPolynomial x b c a = weakPolynomial x a b c := by
  unfold weakPolynomial
  abel

def basisMatrix (i : Fin 9) : Mat :=
  Matrix.single ⟨i.val / 3, by have := i.isLt; omega⟩
    ⟨i.val % 3, by omega⟩ 1

theorem sandwich_entry (a b : Mat) (i j r s : Fin 3) (c : ℚ) :
    (a * Matrix.single i j c * b) r s = a r i * c * b j s := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_assoc]

theorem three_units_entry (a b c d : Mat) (i j k l m n r s : Fin 3) :
    ((a * Matrix.single i j (1 : ℚ) * b * Matrix.single k l (1 : ℚ) * c *
      Matrix.single m n (1 : ℚ) * d : Mat)) r s =
      a r i * b j k * c l m * d n s := by
  have heq : a * Matrix.single i j 1 * b * Matrix.single k l 1 * c * Matrix.single m n 1 * d =
      a * Matrix.single i n (b j k * c l m) * d := by
    calc
      _ = a * ((Matrix.single i j 1 * b * Matrix.single k l 1) * c *
          Matrix.single m n 1) * d := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.single_mul_mul_single, Matrix.single_mul_mul_single]; simp
  rw [heq, sandwich_entry]
  ring

theorem powerWord_single (x : Mat) (i j k l m n r s : Fin 3) (e0 e1 e2 e3 : ℕ) :
    (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ))
      (Matrix.single m n (1 : ℚ)) e0 e1 e2 e3 : Mat) r s =
      (x^e0) r i * (x^e1) j k * (x^e2) l m * (x^e3) n s :=
  by
    unfold powerWord
    exact three_units_entry (x^e0) (x^e1) (x^e2) (x^e3) i j k l m n r s

theorem weak_same13 (x a b : Mat) : weakPolynomial x a b a = 0 := by
  unfold weakPolynomial
  abel

theorem weak_swap23 (x a b c : Mat) :
    weakPolynomial x a c b = -weakPolynomial x a b c := by
  unfold weakPolynomial
  abel

theorem weak_swap13 (x a b c : Mat) :
    weakPolynomial x c b a = -weakPolynomial x a b c := by
  unfold weakPolynomial
  abel

theorem weak_entry_same12 (x a c : Mat) :
    weakPolynomial x a a c 0 0 = 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_same12 x a c)

theorem weak_entry_same23 (x a b : Mat) :
    weakPolynomial x a b b 0 0 = 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_same23 x a b)

theorem weak_entry_same13 (x a b : Mat) :
    weakPolynomial x a b a 0 0 = 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_same13 x a b)

theorem weak_entry_swap12 (x a b c : Mat) :
    weakPolynomial x b a c 0 0 = -weakPolynomial x a b c 0 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_swap12 x a b c)

theorem weak_entry_swap23 (x a b c : Mat) :
    weakPolynomial x a c b 0 0 = -weakPolynomial x a b c 0 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_swap23 x a b c)

theorem weak_entry_swap13 (x a b c : Mat) :
    weakPolynomial x c b a 0 0 = -weakPolynomial x a b c 0 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_swap13 x a b c)

theorem weak_entry_cyclic (x a b c : Mat) :
    weakPolynomial x b c a 0 0 = weakPolynomial x a b c 0 0 := by
  simpa only [Matrix.zero_apply, Matrix.neg_apply] using
    congrArg (fun t : Mat => t 0 0) (weak_cyclic x a b c)

theorem fin3_ne_0_1 : (0 : Fin 3) ≠ 1 := by decide

theorem fin3_ne_0_2 : (0 : Fin 3) ≠ 2 := by decide

theorem fin3_ne_1_0 : (1 : Fin 3) ≠ 0 := by decide

theorem fin3_ne_1_2 : (1 : Fin 3) ≠ 2 := by decide

theorem fin3_ne_2_0 : (2 : Fin 3) ≠ 0 := by decide

theorem fin3_ne_2_1 : (2 : Fin 3) ≠ 1 := by decide

def scalarBlock (x : Mat) (i j k l m n r s : Fin 3) : ℚ :=
    (x^3) r i * (x^0) j k * (x^0) l m * (x^0) n s
     + (x^2) r i * (x^1) j k * (x^0) l m * (x^0) n s
     + (x^2) r i * (x^0) j k * (x^1) l m * (x^0) n s
     + (x^2) r i * (x^0) j k * (x^0) l m * (x^1) n s
     - (x^1) r i * (x^2) j k * (x^0) l m * (x^0) n s
     + (x^1) r i * (x^1) j k * (x^1) l m * (x^0) n s
     - (x^1) r i * (x^1) j k * (x^0) l m * (x^1) n s
     + (x^1) r i * (x^0) j k * (x^2) l m * (x^0) n s
     + (x^1) r i * (x^0) j k * (x^1) l m * (x^1) n s
     - (x^1) r i * (x^0) j k * (x^0) l m * (x^2) n s
     - (x^0) r i * (x^3) j k * (x^0) l m * (x^0) n s
     - (x^0) r i * (x^2) j k * (x^1) l m * (x^0) n s
     - (x^0) r i * (x^2) j k * (x^0) l m * (x^1) n s
     + (x^0) r i * (x^1) j k * (x^2) l m * (x^0) n s
     - (x^0) r i * (x^1) j k * (x^1) l m * (x^1) n s
     - (x^0) r i * (x^1) j k * (x^0) l m * (x^2) n s
     + (x^0) r i * (x^0) j k * (x^3) l m * (x^0) n s
     + (x^0) r i * (x^0) j k * (x^2) l m * (x^1) n s
     - (x^0) r i * (x^0) j k * (x^1) l m * (x^2) n s
     - (x^0) r i * (x^0) j k * (x^0) l m * (x^3) n s

theorem block_single_formula (x : Mat) (i j k l m n r s : Fin 3) :
    (block x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ))
      (Matrix.single m n (1 : ℚ)) : Mat) r s = scalarBlock x i j k l m n r s := by
  change (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 3 0 0 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 2 1 0 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 2 0 1 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 2 0 0 1 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 2 0 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 1 1 0 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 1 0 1 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 0 2 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 0 1 1 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 1 0 0 2 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 3 0 0 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 2 1 0 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 2 0 1 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 1 2 0 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 1 1 1 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 1 0 2 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 0 3 0 : Mat) r s
     + (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 0 2 1 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 0 1 2 : Mat) r s
     - (powerWord x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) 0 0 0 3 : Mat) r s = _
  simp only [powerWord_single, scalarBlock]

theorem weak_single_formula (x : Mat) (i j k l m n r s : Fin 3) :
    (weakPolynomial x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ))
      (Matrix.single m n (1 : ℚ)) : Mat) r s =
      scalarBlock x i j k l m n r s - scalarBlock x i j m n k l r s -
      scalarBlock x k l i j m n r s + scalarBlock x k l m n i j r s +
      scalarBlock x m n i j k l r s - scalarBlock x m n k l i j r s := by
  unfold weakPolynomial
  change (block x (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) : Mat) r s -
    (block x (Matrix.single i j (1 : ℚ)) (Matrix.single m n (1 : ℚ)) (Matrix.single k l (1 : ℚ)) : Mat) r s -
    (block x (Matrix.single k l (1 : ℚ)) (Matrix.single i j (1 : ℚ)) (Matrix.single m n (1 : ℚ)) : Mat) r s +
    (block x (Matrix.single k l (1 : ℚ)) (Matrix.single m n (1 : ℚ)) (Matrix.single i j (1 : ℚ)) : Mat) r s +
    (block x (Matrix.single m n (1 : ℚ)) (Matrix.single i j (1 : ℚ)) (Matrix.single k l (1 : ℚ)) : Mat) r s -
    (block x (Matrix.single m n (1 : ℚ)) (Matrix.single k l (1 : ℚ)) (Matrix.single i j (1 : ℚ)) : Mat) r s = _
  simp only [block_single_formula]

theorem basis_0_1_2 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 2) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_3 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 3) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_1_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_3 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 3) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_2_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_3_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_3_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_3_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_3_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_3_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_4_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_4_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_4_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_4_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]

theorem basis_0_5_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_5_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_5_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_0_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_3 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 3) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_2_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_3_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_3_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_3_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_3_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_3_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_4_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_4_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_4_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_4_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_5_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_5_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_5_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_1_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_3_4 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
      (basisMatrix 4) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_3_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_3_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_3_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_3_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_4_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_4_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_4_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_4_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_5_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_5_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_5_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_2_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 0 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_4_5 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
      (basisMatrix 5) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_4_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_4_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_4_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_5_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_5_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_5_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_3_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_5_6 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
      (basisMatrix 6) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_5_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_5_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_4_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 1 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_5_6_7 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6)
      (basisMatrix 7) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_5_6_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_5_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 1 2 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

theorem basis_6_7_8 (x : Fin 8 → ℚ) :
    weakPolynomial (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7)
      (basisMatrix 8) 0 0 = 0 := by
  change (weakPolynomial (tracelessMatrix x) (Matrix.single 2 0 (1 : ℚ)) (Matrix.single 2 1 (1 : ℚ)) (Matrix.single 2 2 (1 : ℚ)) : Mat) 0 0 = 0
  rw [weak_single_formula]
  norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, scalarBlock, tracelessMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, pow_succ]
  <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem basis_00 (x : Fin 8 → ℚ) (i j k : Fin 9) :
    weakPolynomial (tracelessMatrix x) (basisMatrix i) (basisMatrix j)
      (basisMatrix k) 0 0 = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 8)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1)
  · exact basis_0_1_2 x
  · exact basis_0_1_3 x
  · exact basis_0_1_4 x
  · exact basis_0_1_5 x
  · exact basis_0_1_6 x
  · exact basis_0_1_7 x
  · exact basis_0_1_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 2)).trans (neg_eq_zero.mpr (basis_0_1_2 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2)
  · exact basis_0_2_3 x
  · exact basis_0_2_4 x
  · exact basis_0_2_5 x
  · exact basis_0_2_6 x
  · exact basis_0_2_7 x
  · exact basis_0_2_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_1_3 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_2_3 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3)
  · exact basis_0_3_4 x
  · exact basis_0_3_5 x
  · exact basis_0_3_6 x
  · exact basis_0_3_7 x
  · exact basis_0_3_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_1_4 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_2_4 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_3_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4)
  · exact basis_0_4_5 x
  · exact basis_0_4_6 x
  · exact basis_0_4_7 x
  · exact basis_0_4_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_1_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_2_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_3_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_4_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5)
  · exact basis_0_5_6 x
  · exact basis_0_5_7 x
  · exact basis_0_5_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_1_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_2_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_3_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_4_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6)
  · exact basis_0_6_7 x
  · exact basis_0_6_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_1_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_2_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_3_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_4_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_5_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7)
  · exact basis_0_7_8 x
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_1_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_2_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_3_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_4_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_5_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 0)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 2)).trans (neg_eq_zero.mpr (basis_0_1_2 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_1_3 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_1_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_1_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_1_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_1_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_1_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 2)).trans (basis_0_1_2 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2)
  · exact basis_1_2_3 x
  · exact basis_1_2_4 x
  · exact basis_1_2_5 x
  · exact basis_1_2_6 x
  · exact basis_1_2_7 x
  · exact basis_1_2_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 3)).trans (basis_0_1_3 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_1_2_3 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3)
  · exact basis_1_3_4 x
  · exact basis_1_3_5 x
  · exact basis_1_3_6 x
  · exact basis_1_3_7 x
  · exact basis_1_3_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 4)).trans (basis_0_1_4 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_2_4 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_3_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4)
  · exact basis_1_4_5 x
  · exact basis_1_4_6 x
  · exact basis_1_4_7 x
  · exact basis_1_4_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 5)).trans (basis_0_1_5 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_2_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_3_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_4_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5)
  · exact basis_1_5_6 x
  · exact basis_1_5_7 x
  · exact basis_1_5_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 6)).trans (basis_0_1_6 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_2_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_3_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_4_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6)
  · exact basis_1_6_7 x
  · exact basis_1_6_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 7)).trans (basis_0_1_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_2_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_3_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_4_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_5_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7)
  · exact basis_1_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 8)).trans (basis_0_1_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_2_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_3_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_4_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_5_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 2)).trans (basis_0_1_2 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_2_3 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_2_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_2_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_2_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_2_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_2_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 2)).trans (neg_eq_zero.mpr (basis_0_1_2 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 1)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_1_2_3 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_2_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_2_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_2_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_2_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_2_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 3)).trans (basis_0_2_3 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 3)).trans (basis_1_2_3 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3)
  · exact basis_2_3_4 x
  · exact basis_2_3_5 x
  · exact basis_2_3_6 x
  · exact basis_2_3_7 x
  · exact basis_2_3_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 4)).trans (basis_0_2_4 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 4)).trans (basis_1_2_4 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_2_3_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4)
  · exact basis_2_4_5 x
  · exact basis_2_4_6 x
  · exact basis_2_4_7 x
  · exact basis_2_4_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 5)).trans (basis_0_2_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 5)).trans (basis_1_2_5 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_3_5 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_4_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5)
  · exact basis_2_5_6 x
  · exact basis_2_5_7 x
  · exact basis_2_5_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 6)).trans (basis_0_2_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 6)).trans (basis_1_2_6 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_3_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_4_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6)
  · exact basis_2_6_7 x
  · exact basis_2_6_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 7)).trans (basis_0_2_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 7)).trans (basis_1_2_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_3_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_4_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_5_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7)
  · exact basis_2_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 8)).trans (basis_0_2_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 8)).trans (basis_1_2_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_3_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_4_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_5_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 3)).trans (basis_0_1_3 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 3)).trans (basis_0_2_3 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_3_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_3_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_3_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_3_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_3_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_1_3 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 3)).trans (basis_1_2_3 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_3_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_3_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_3_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_3_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_3_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_0_2_3 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 3)).trans (neg_eq_zero.mpr (basis_1_2_3 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 2)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 2)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_2_3_4 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_3_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_3_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_3_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_3_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 4)).trans (basis_0_3_4 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 4)).trans (basis_1_3_4 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 4)).trans (basis_2_3_4 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4)
  · exact basis_3_4_5 x
  · exact basis_3_4_6 x
  · exact basis_3_4_7 x
  · exact basis_3_4_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 5)).trans (basis_0_3_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 5)).trans (basis_1_3_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 5)).trans (basis_2_3_5 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_3_4_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5)
  · exact basis_3_5_6 x
  · exact basis_3_5_7 x
  · exact basis_3_5_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 6)).trans (basis_0_3_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 6)).trans (basis_1_3_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 6)).trans (basis_2_3_6 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_4_6 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6)
  · exact basis_3_6_7 x
  · exact basis_3_6_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 7)).trans (basis_0_3_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 7)).trans (basis_1_3_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 7)).trans (basis_2_3_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_4_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_5_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7)
  · exact basis_3_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 8)).trans (basis_0_3_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 8)).trans (basis_1_3_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 8)).trans (basis_2_3_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_4_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_5_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 4)).trans (basis_0_1_4 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 4)).trans (basis_0_2_4 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 4)).trans (basis_0_3_4 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_4_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_4_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_4_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_1_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 4)).trans (basis_1_2_4 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 4)).trans (basis_1_3_4 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_4_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_4_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_4_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_2_4 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_2_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 2)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 4)).trans (basis_2_3_4 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 2)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_4_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_4_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_4_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_0_3_4 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_1_3_4 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 4)).trans (neg_eq_zero.mpr (basis_2_3_4 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 3)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 3)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_3_4_5 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_4_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_4_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_4_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 5)).trans (basis_0_4_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 5)).trans (basis_1_4_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 5)).trans (basis_2_4_5 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 5)).trans (basis_3_4_5 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5)
  · exact basis_4_5_6 x
  · exact basis_4_5_7 x
  · exact basis_4_5_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 6)).trans (basis_0_4_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 6)).trans (basis_1_4_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 6)).trans (basis_2_4_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 6)).trans (basis_3_4_6 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_4_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6)
  · exact basis_4_6_7 x
  · exact basis_4_6_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 7)).trans (basis_0_4_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 7)).trans (basis_1_4_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 7)).trans (basis_2_4_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 7)).trans (basis_3_4_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_5_7 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7)
  · exact basis_4_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 8)).trans (basis_0_4_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 8)).trans (basis_1_4_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 8)).trans (basis_2_4_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 8)).trans (basis_3_4_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_5_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 5)).trans (basis_0_1_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 5)).trans (basis_0_2_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 5)).trans (basis_0_3_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 5)).trans (basis_0_4_5 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_5_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_5_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_1_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 5)).trans (basis_1_2_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 5)).trans (basis_1_3_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 5)).trans (basis_1_4_5 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_5_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_5_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_2_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_2_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 2)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 5)).trans (basis_2_3_5 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 5)).trans (basis_2_4_5 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 2)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_5_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_5_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_3_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_3_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_3_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 3)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 5)).trans (basis_3_4_5 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 3)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_5_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_5_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_0_4_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_1_4_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_2_4_5 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 5)).trans (neg_eq_zero.mpr (basis_3_4_5 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 4)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 4)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_4_5_6 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_5_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_5_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 6)).trans (basis_0_5_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 6)).trans (basis_1_5_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 6)).trans (basis_2_5_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 6)).trans (basis_3_5_6 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 6)).trans (basis_4_5_6 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6)
  · exact basis_5_6_7 x
  · exact basis_5_6_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 7)).trans (basis_0_5_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 7)).trans (basis_1_5_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 7)).trans (basis_2_5_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 7)).trans (basis_3_5_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 7)).trans (basis_4_5_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_5_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7)
  · exact basis_5_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 8)).trans (basis_0_5_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 8)).trans (basis_1_5_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 8)).trans (basis_2_5_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 8)).trans (basis_3_5_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 8)).trans (basis_4_5_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_6_8 x))
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 6)).trans (basis_0_1_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 6)).trans (basis_0_2_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 6)).trans (basis_0_3_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 6)).trans (basis_0_4_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 6)).trans (basis_0_5_6 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_1_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 6)).trans (basis_1_2_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 6)).trans (basis_1_3_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 6)).trans (basis_1_4_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 6)).trans (basis_1_5_6 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_2_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_2_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 2)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 6)).trans (basis_2_3_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 6)).trans (basis_2_4_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 6)).trans (basis_2_5_6 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 2)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_3_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_3_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_3_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 3)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 6)).trans (basis_3_4_6 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 6)).trans (basis_3_5_6 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 3)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_4_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_4_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_4_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_4_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 4)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 6)).trans (basis_4_5_6 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 4)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_0_5_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_1_5_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_2_5_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_3_5_6 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 6)).trans (neg_eq_zero.mpr (basis_4_5_6 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 5)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 5)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_5_6_7 x))
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_6_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 7)).trans (basis_0_6_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 7)).trans (basis_1_6_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 7)).trans (basis_2_6_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 7)).trans (basis_3_6_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 7)).trans (basis_4_6_7 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 7)).trans (basis_5_6_7 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7)
  · exact basis_6_7_8 x
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 8)).trans (basis_0_6_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 8)).trans (basis_1_6_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 8)).trans (basis_2_6_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 8)).trans (basis_3_6_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 8)).trans (basis_4_6_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 8)).trans (basis_5_6_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8)
  · exact (weak_entry_swap23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_6_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 7)).trans (basis_0_1_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 7)).trans (basis_0_2_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 7)).trans (basis_0_3_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 7)).trans (basis_0_4_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 7)).trans (basis_0_5_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 7)).trans (basis_0_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 0)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_1_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 7)).trans (basis_1_2_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 7)).trans (basis_1_3_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 7)).trans (basis_1_4_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 7)).trans (basis_1_5_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 7)).trans (basis_1_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 1)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_2_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_2_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 2)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 7)).trans (basis_2_3_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 7)).trans (basis_2_4_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 7)).trans (basis_2_5_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 7)).trans (basis_2_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 2)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_3_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_3_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_3_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 3)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 7)).trans (basis_3_4_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 7)).trans (basis_3_5_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 7)).trans (basis_3_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 3)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_4_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_4_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_4_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_4_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 4)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 7)).trans (basis_4_5_7 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 7)).trans (basis_4_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 4)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_5_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_5_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_5_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_5_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_5_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 5)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 5)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 7)).trans (basis_5_6_7 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 5)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_0_6_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_1_6_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_2_6_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_3_6_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_4_6_7 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 7)).trans (neg_eq_zero.mpr (basis_5_6_7 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 6)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 6)
  · exact (weak_entry_swap12 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_6_7_8 x))
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7) (basisMatrix 8)).trans (basis_0_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 8)).trans (basis_1_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 8)).trans (basis_2_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 8)).trans (basis_3_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 8)).trans (basis_4_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 8)).trans (basis_5_7_8 x)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 8)).trans (basis_6_7_8 x)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8)
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 0)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 8)).trans (basis_0_1_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 8)).trans (basis_0_2_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 8)).trans (basis_0_3_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 8)).trans (basis_0_4_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 8)).trans (basis_0_5_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 8)).trans (basis_0_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 0)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7) (basisMatrix 8)).trans (basis_0_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 0)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 1) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_1_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 1)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 8)).trans (basis_1_2_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 8)).trans (basis_1_3_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 8)).trans (basis_1_4_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 8)).trans (basis_1_5_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 8)).trans (basis_1_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 1)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 8)).trans (basis_1_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 1)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_2_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 2) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_2_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 2)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 8) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 8)).trans (basis_2_3_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 8)).trans (basis_2_4_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 8)).trans (basis_2_5_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 8)).trans (basis_2_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 2)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 8)).trans (basis_2_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 2)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_3_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_3_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 3) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_3_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 3)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 8) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 8)).trans (basis_3_4_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 8)).trans (basis_3_5_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 8)).trans (basis_3_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 3)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 8)).trans (basis_3_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 3)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_4_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 4) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_4_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 4)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 8) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 8)).trans (basis_4_5_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 8)).trans (basis_4_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 4)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 8)).trans (basis_4_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 4)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_5_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 5) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_5_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 5)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 8) (basisMatrix 5)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 8)).trans (basis_5_6_8 x))
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 5)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 8)).trans (basis_5_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 5)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_6_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 6) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_6_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 6)
  · exact (weak_entry_cyclic (tracelessMatrix x) (basisMatrix 7) (basisMatrix 8) (basisMatrix 6)).trans ((weak_entry_cyclic (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 8)).trans (basis_6_7_8 x))
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 6)
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 0) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_0_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 1) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_1_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 2) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_2_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 3) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_3_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 4) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_4_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 5) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_5_7_8 x))
  · exact (weak_entry_swap13 (tracelessMatrix x) (basisMatrix 6) (basisMatrix 7) (basisMatrix 8)).trans (neg_eq_zero.mpr (basis_6_7_8 x))
  · exact weak_entry_same23 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 7)
  · exact weak_entry_same13 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 0)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 1)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 2)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 3)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 4)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 5)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 6)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 7)
  · exact weak_entry_same12 (tracelessMatrix x) (basisMatrix 8) (basisMatrix 8)

def pairIndex (i j : Fin 3) : Fin 9 := ⟨3 * i.val + j.val, by omega⟩

theorem basisMatrix_pair (i j : Fin 3) :
    basisMatrix (pairIndex i j) = Matrix.single i j (1 : ℚ) := by
  fin_cases i <;> fin_cases j <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem weak_00 (x : Fin 8 → ℚ) (a b c : Mat) :
    weakPolynomial (tracelessMatrix x) a b c 0 0 = 0 := by
  have hz : weak00Map (tracelessMatrix x) = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => Matrix.stdBasis ℚ (Fin 3) (Fin 3))
    intro v
    change (weakMap (tracelessMatrix x) (fun i =>
      Matrix.stdBasis ℚ (Fin 3) (Fin 3) (v i))) 0 0 = 0
    have h := basis_00 x (pairIndex (v 0).1 (v 0).2)
      (pairIndex (v 1).1 (v 1).2) (pairIndex (v 2).1 (v 2).2)
    apply (congrArg (fun t : Mat => t 0 0) (weakMap_apply _ _)).trans
    have hb : ∀ ij : Fin 3 × Fin 3, Matrix.stdBasis ℚ (Fin 3) (Fin 3) ij =
        Matrix.single ij.1 ij.2 (1 : ℚ) := by
      rintro ⟨i,j⟩
      exact Matrix.stdBasis_eq_single ℚ i j
    simpa only [basisMatrix_pair, hb] using h
  have h := congrArg (fun f => f ![a,b,c]) hz
  simpa [weak00Map, entry00, weakMap_apply] using h

theorem weak_00_general (x a b c : Mat) (hx : Matrix.trace x = 0) :
    weakPolynomial x a b c 0 0 = 0 := by
  let v : Fin 8 → ℚ := ![x 0 0, x 0 1, x 0 2, x 1 0, x 1 1, x 1 2, x 2 0, x 2 1]
  have heq : tracelessMatrix v = x := by
    have h : x 2 2 = -x 0 0 - x 1 1 := by
      simp [Matrix.trace, Fin.sum_univ_succ] at hx
      linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tracelessMatrix, v, h]
  simpa only [heq] using weak_00 v a b c

def conjugation (p q : Mat) (hp : p * q = 1) (hq : q * p = 1) : Mat →+* Mat where
  toFun a := p * a * q
  map_one' := by simpa using hp
  map_mul' a b := by
    change p * (a * b) * q = (p * a * q) * (p * b * q)
    symm
    calc
      _ = p * a * (q * p) * b * q := by simp only [Matrix.mul_assoc]
      _ = p * (a * b) * q := by rw [hq]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  map_zero' := by simp
  map_add' a b := by simp only [Matrix.mul_add, Matrix.add_mul]

theorem weakPolynomial_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (x a b c : R) :
    f (weakPolynomial x a b c) = weakPolynomial (f x) (f a) (f b) (f c) := by
  simp only [weakPolynomial, block, powerWord, map_add, map_sub, map_mul, map_pow]

theorem trace_conjugation (p q x : Mat) (hq : q * p = 1) :
    Matrix.trace (p * x * q) = Matrix.trace x := by
  rw [Matrix.trace_mul_cycle, hq, Matrix.one_mul]

theorem zero_of_conjugate_entry (t : Mat)
    (h : ∀ p q : Mat, p * q = 1 → q * p = 1 → (p * t * q) 0 0 = 0) : t = 0 := by
  have h0 : t 0 0 = 0 := by
    have h0 := h (!![1, 0, 0; 0, 1, 0; 0, 0, 1]) (!![1, 0, 0; 0, 1, 0; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] using h0
  have h1 : t 1 1 = 0 := by
    have h0 := h (!![0, 1, 0; 1, 0, 0; 0, 0, 1]) (!![0, 1, 0; 1, 0, 0; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] using h0
  have h2 : t 2 2 = 0 := by
    have h0 := h (!![0, 0, 1; 0, 1, 0; 1, 0, 0]) (!![0, 0, 1; 0, 1, 0; 1, 0, 0]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] using h0
  ext i j
  change t i j = 0
  fin_cases i <;> fin_cases j
  · exact h0
  · change t 0 1 = 0
    have hc := h (!![1, 1, 0; 1, 0, 0; 0, 0, 1]) (!![0, 1, 0; 1, -1, 0; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h1, add_zero] using hc
  · change t 0 2 = 0
    have hc := h (!![1, 0, 1; 0, 1, 0; 1, 0, 0]) (!![0, 0, 1; 0, 1, 0; 1, 0, -1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h2, add_zero] using hc
  · change t 1 0 = 0
    have hc := h (!![1, 1, 0; 0, 1, 0; 0, 0, 1]) (!![1, -1, 0; 0, 1, 0; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h0, zero_add] using hc
  · exact h1
  · change t 1 2 = 0
    have hc := h (!![0, 1, 1; 0, 1, 0; 1, 0, 0]) (!![0, 0, 1; 0, 1, 0; 1, -1, 0]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h2, add_zero] using hc
  · change t 2 0 = 0
    have hc := h (!![1, 0, 1; 0, 1, 0; 0, 0, 1]) (!![1, 0, -1; 0, 1, 0; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h0, zero_add] using hc
  · change t 2 1 = 0
    have hc := h (!![0, 1, 1; 1, 0, 0; 0, 0, 1]) (!![0, 1, 0; 1, 0, -1; 0, 0, 1]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]) (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [fin3_ne_0_1, fin3_ne_0_2, fin3_ne_1_0, fin3_ne_1_2, fin3_ne_2_0, fin3_ne_2_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply])
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at hc
    simpa only [h1, zero_add] using hc
  · exact h2

theorem weak_zero (x a b c : Mat) (hx : Matrix.trace x = 0) :
    weakPolynomial x a b c = 0 := by
  apply zero_of_conjugate_entry
  intro p q hp hq
  let f := conjugation p q hp hq
  have h := weak_00_general (f x) (f a) (f b) (f c)
    (by change Matrix.trace (p*x*q) = 0; rw [trace_conjugation p q x hq, hx])
  have he := congrArg (fun t : Mat => t 0 0) (weakPolynomial_map f x a b c)
  exact he.trans h

abbrev MarkedTerm := Bool × List (Fin 4) × List (Fin 4)

def markedTerms : List MarkedTerm := [
  (true, [], [0, 0, 1, 2, 3]),
  (true, [0], [0, 1, 2, 3]),
  (true, [0, 0], [1, 2, 3]),
  (true, [], [0, 1, 0, 2, 3]),
  (true, [0], [1, 0, 2, 3]),
  (true, [0, 0, 1], [2, 3]),
  (true, [], [0, 1, 2, 0, 3]),
  (true, [0], [1, 2, 0, 3]),
  (true, [0, 0, 1, 2], [3]),
  (true, [], [0, 1, 2, 3, 0]),
  (true, [0], [1, 2, 3, 0]),
  (true, [0, 0, 1, 2, 3], []),
  (false, [], [1, 0, 0, 2, 3]),
  (false, [0, 1], [0, 2, 3]),
  (false, [0, 1, 0], [2, 3]),
  (true, [], [1, 0, 2, 0, 3]),
  (true, [0, 1], [2, 0, 3]),
  (true, [0, 1, 0, 2], [3]),
  (false, [], [1, 0, 2, 3, 0]),
  (false, [0, 1], [2, 3, 0]),
  (false, [0, 1, 0, 2, 3], []),
  (true, [], [1, 2, 0, 0, 3]),
  (true, [0, 1, 2], [0, 3]),
  (true, [0, 1, 2, 0], [3]),
  (true, [], [1, 2, 0, 3, 0]),
  (true, [0, 1, 2], [3, 0]),
  (true, [0, 1, 2, 0, 3], []),
  (false, [], [1, 2, 3, 0, 0]),
  (false, [0, 1, 2, 3], [0]),
  (false, [0, 1, 2, 3, 0], []),
  (false, [1], [0, 0, 2, 3]),
  (false, [1, 0], [0, 2, 3]),
  (false, [1, 0, 0], [2, 3]),
  (false, [1], [0, 2, 0, 3]),
  (false, [1, 0], [2, 0, 3]),
  (false, [1, 0, 0, 2], [3]),
  (false, [1], [0, 2, 3, 0]),
  (false, [1, 0], [2, 3, 0]),
  (false, [1, 0, 0, 2, 3], []),
  (true, [1], [2, 0, 0, 3]),
  (true, [1, 0, 2], [0, 3]),
  (true, [1, 0, 2, 0], [3]),
  (false, [1], [2, 0, 3, 0]),
  (false, [1, 0, 2], [3, 0]),
  (false, [1, 0, 2, 0, 3], []),
  (false, [1], [2, 3, 0, 0]),
  (false, [1, 0, 2, 3], [0]),
  (false, [1, 0, 2, 3, 0], []),
  (true, [1, 2], [0, 0, 3]),
  (true, [1, 2, 0], [0, 3]),
  (true, [1, 2, 0, 0], [3]),
  (true, [1, 2], [0, 3, 0]),
  (true, [1, 2, 0], [3, 0]),
  (true, [1, 2, 0, 0, 3], []),
  (false, [1, 2], [3, 0, 0]),
  (false, [1, 2, 0, 3], [0]),
  (false, [1, 2, 0, 3, 0], []),
  (false, [1, 2, 3], [0, 0]),
  (false, [1, 2, 3, 0], [0]),
  (false, [1, 2, 3, 0, 0], [])]

def signed {R : Type*} [AddGroup R] (positive : Bool) (a : R) : R :=
  if positive then a else -a

def evalWord {R : Type*} [Monoid R] (v : Fin 4 → R) (w : List (Fin 4)) : R :=
  (w.map v).prod

def dblock {R : Type*} [Ring R] (y x a b c : R) : R :=
  (markedTerms.map fun t => signed t.1
    (evalWord ![y,a,b,c] t.2.1 * x * evalWord ![y,a,b,c] t.2.2)).sum

def gblock {R : Type*} [Ring R] (y a b c z : R) : R :=
  (markedTerms.map fun t => signed t.1
    (evalWord ![y,a,b,c] t.2.2 * z * evalWord ![y,a,b,c] t.2.1)).sum

def differential {R : Type*} [Ring R] (y x a b c : R) : R :=
  dblock y x a b c - dblock y x a c b - dblock y x b a c +
    dblock y x b c a + dblock y x c a b - dblock y x c b a

def gradient {R : Type*} [Ring R] (y a b c z : R) : R :=
  gblock y a b c z - gblock y a c b z - gblock y b a c z +
    gblock y b c a z + gblock y c a b z - gblock y c b a z

theorem block_polarization {R : Type*} [Ring R] (y x a b c : R) :
    block (y+x) a b c - block (y-x) a b c - (block x a b c + block x a b c) =
      dblock y x a b c + dblock y x a b c := by
  simp [block, powerWord, dblock, markedTerms, evalWord, signed]
  noncomm_ring

theorem weak_polarization {R : Type*} [Ring R] (y x a b c : R) :
    weakPolynomial (y+x) a b c - weakPolynomial (y-x) a b c -
      (weakPolynomial x a b c + weakPolynomial x a b c) =
      differential y x a b c + differential y x a b c := by
  calc
    _ = (block (y+x) a b c - block (y-x) a b c - (block x a b c + block x a b c)) -
        (block (y+x) a c b - block (y-x) a c b - (block x a c b + block x a c b)) -
        (block (y+x) b a c - block (y-x) b a c - (block x b a c + block x b a c)) +
        (block (y+x) b c a - block (y-x) b c a - (block x b c a + block x b c a)) +
        (block (y+x) c a b - block (y-x) c a b - (block x c a b + block x c a b)) -
        (block (y+x) c b a - block (y-x) c b a - (block x c b a + block x c b a)) := by
          unfold weakPolynomial
          abel
    _ = (dblock y x a b c + dblock y x a b c) -
        (dblock y x a c b + dblock y x a c b) -
        (dblock y x b a c + dblock y x b a c) +
        (dblock y x b c a + dblock y x b c a) +
        (dblock y x c a b + dblock y x c a b) -
        (dblock y x c b a + dblock y x c b a) := by
          rw [block_polarization, block_polarization, block_polarization,
            block_polarization, block_polarization, block_polarization]
    _ = _ := by unfold differential; abel

theorem trace_rotation (l r z x : Mat) :
    Matrix.trace ((r*z*l)*x) = Matrix.trace (z*(l*x*r)) := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm r (z*(l*x))

theorem trace_gblock (y a b c z x : Mat) :
    Matrix.trace (gblock y a b c z * x) = Matrix.trace (z * dblock y x a b c) := by
  unfold gblock dblock
  generalize markedTerms = ts
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, mul_add, Matrix.trace_add]
    rw [ih]
    congr 1
    rcases t with ⟨positive,l,r⟩
    cases positive <;> simp only [signed, Bool.false_eq_true, if_false, if_true,
      neg_mul, mul_neg, Matrix.trace_neg]
    · exact congrArg Neg.neg (trace_rotation _ _ _ _)
    · exact trace_rotation _ _ _ _

theorem trace_gradient (y a b c z x : Mat) :
    Matrix.trace (gradient y a b c z * x) =
      Matrix.trace (z * differential y x a b c) := by
  simp only [gradient, differential, sub_mul, add_mul, mul_sub, mul_add,
    Matrix.trace_sub, Matrix.trace_add, trace_gblock]

theorem differential_zero (y x a b c : Mat)
    (hy : Matrix.trace y = 0) (hx : Matrix.trace x = 0) :
    differential y x a b c = 0 := by
  have h := weak_polarization y x a b c
  rw [weak_zero (y+x) a b c (by simp [hy,hx]),
    weak_zero (y-x) a b c (by simp [hy,hx]), weak_zero x a b c hx] at h
  ext i j
  change differential y x a b c i j = 0
  have ht := congrArg (fun t : Mat => t i j) h
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply] at ht
  linarith

theorem gradient_scalar (y a b c z : Mat) (hy : Matrix.trace y = 0) :
    gradient y a b c z = (gradient y a b c z 0 0) • (1 : Mat) := by
  let g := gradient y a b c z
  have h : ∀ x : Mat, Matrix.trace x = 0 → Matrix.trace (g*x) = 0 := by
    intro x hx
    dsimp [g]
    rw [trace_gradient, differential_zero y x a b c hy hx]
    simp
  have hoff : ∀ i j : Fin 3, i ≠ j → g i j = 0 := by
    intro i j hij
    have ht := h (Matrix.single j i 1) (Matrix.trace_single_eq_of_ne j i 1 hij.symm)
    simpa [Matrix.trace_mul_single] using ht
  have hdiag : ∀ i : Fin 3, g i i = g 0 0 := by
    intro i
    have ht := h (Matrix.single i i 1 - Matrix.single 0 0 1) (by simp)
    simpa [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_mul_single,
      sub_eq_zero] using ht
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [g, Matrix.smul_apply, Matrix.one_apply] using hdiag i
  · change g i j = ((g 0 0) • (1 : Mat)) i j
    rw [hoff i j hij]
    simp [Matrix.smul_apply, hij]

open scoped Pointwise

abbrev WordAlgebra (m : ℕ) := MonoidAlgebra ℚ (FreeMonoid (Fin m))

noncomputable def freeNormalForm (m : ℕ) :
    FreeAlgebra ℚ (Fin m) ≃ₐ[ℚ] WordAlgebra m :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid

theorem freeNormalForm_generator {m : ℕ} (i : Fin m) :
    freeNormalForm m (FreeAlgebra.ι ℚ i) = MonoidAlgebra.single (FreeMonoid.of i) (1 : ℚ) := by
  change FreeAlgebra.lift ℚ (fun j => MonoidAlgebra.of ℚ (FreeMonoid (Fin m))
    (FreeMonoid.of j)) (FreeAlgebra.ι ℚ i) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

noncomputable def generator {m : ℕ} (i : Fin m) : WordAlgebra m :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

noncomputable def evaluate {m : ℕ} (v : Fin m → Mat) : WordAlgebra m →ₐ[ℚ] Mat :=
  MonoidAlgebra.lift ℚ Mat (FreeMonoid (Fin m)) (FreeMonoid.lift v)

theorem evaluate_generator {m : ℕ} (v : Fin m → Mat) (i : Fin m) :
    evaluate v (generator i) = v i := by simp [evaluate, generator]

theorem map_signed {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S] (f : F) (b : Bool) (x : R) :
    f (signed b x) = signed b (f x) := by cases b <;> simp [signed]

theorem map_evalWord {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S] (f : F)
    (v : Fin 4 → R) (w : List (Fin 4)) :
    f (evalWord v w) = evalWord (fun i => f (v i)) w := by
  simp only [evalWord, map_list_prod, List.map_map, Function.comp_def]

theorem map_gblock {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S] (f : F) (y a b c z : R) :
    f (gblock y a b c z) = gblock (f y) (f a) (f b) (f c) (f z) := by
  have hv : (fun i => f ((![y,a,b,c] : Fin 4 → R) i)) = ![f y,f a,f b,f c] := by
    funext i; fin_cases i <;> rfl
  simp only [gblock, map_list_sum, List.map_map, Function.comp_def, map_signed, map_mul, map_evalWord, hv]

theorem map_gradient {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S] (f : F) (y a b c z : R) :
    f (gradient y a b c z) = gradient (f y) (f a) (f b) (f c) (f z) := by
  simp only [gradient, map_add, map_sub, map_gblock]

noncomputable def centralPolynomial : WordAlgebra 6 :=
  gradient (generator 0 * generator 1 - generator 1 * generator 0)
    (generator 2) (generator 3) (generator 4) (generator 5)

noncomputable def freePolynomial : FreeAlgebra ℚ (Fin 6) :=
  (freeNormalForm 6).symm centralPolynomial

theorem freePolynomial_normal_form : freeNormalForm 6 freePolynomial = centralPolynomial := by
  simp [freePolynomial]

theorem evaluate_central (v : Fin 6 → Mat) :
    evaluate v centralPolynomial = gradient (v 0*v 1-v 1*v 0) (v 2) (v 3) (v 4) (v 5) := by
  simp only [centralPolynomial, map_gradient, map_sub, map_mul, evaluate_generator]

theorem evaluate_central_scalar (v : Fin 6 → Mat) :
    evaluate v centralPolynomial = (evaluate v centralPolynomial 0 0) • (1 : Mat) := by
  rw [evaluate_central]
  exact gradient_scalar _ _ _ _ _ (by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (v 0) (v 1), sub_self])

def witness : Fin 6 → Mat := ![
  !![1,0,0;0,0,0;0,0,0],
  !![0,1,1;0,0,0;-1,0,0],
  !![0,0,0;0,0,0;0,0,1],
  !![0,0,0;1,0,0;0,0,0],
  !![0,0,0;0,0,0;1,0,0],
  !![0,0,0;0,0,0;0,1,0]]

theorem witness_value : evaluate witness centralPolynomial = (2 : ℚ) • (1 : Mat) := by
  have h00 : evaluate witness centralPolynomial 0 0 = 2 := by
    rw [evaluate_central]
    norm_num (config := { maxSteps := 1000000 }) [witness, gradient, gblock, markedTerms, signed, evalWord,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]
  rw [evaluate_central_scalar, h00]

theorem centralPolynomial_ne_zero : centralPolynomial ≠ 0 := by
  intro h
  have hw := witness_value
  rw [h, map_zero] at hw
  have he := congrArg (fun a : Mat => a 0 0) hw
  norm_num at he

def Homogeneous {m : ℕ} (p : WordAlgebra m) (n : ℕ) : Prop :=
  ∀ w ∈ p.coeff.support, w.length = n

theorem homogeneous_zero {m n : ℕ} : Homogeneous (0 : WordAlgebra m) n := by
  simp [Homogeneous]

theorem homogeneous_one {m : ℕ} : Homogeneous (1 : WordAlgebra m) 0 := by
  intro w hw
  have he : w = 1 := by simpa [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] using hw
  subst w
  rfl

theorem homogeneous_generator {m : ℕ} (i : Fin m) : Homogeneous (generator i) 1 := by
  intro w hw
  have he : w = FreeMonoid.of i := by simpa [generator, MonoidAlgebra.coeff_single] using hw
  subst w
  rfl

theorem homogeneous_add {m n : ℕ} {p q : WordAlgebra m}
    (hp : Homogeneous p n) (hq : Homogeneous q n) : Homogeneous (p+q) n := by
  classical
  intro w hw
  have hh : w ∈ p.coeff.support ∪ q.coeff.support :=
    Finsupp.support_add (by simpa only [MonoidAlgebra.coeff_add] using hw)
  rcases Finset.mem_union.mp hh with h | h
  · exact hp w h
  · exact hq w h

theorem homogeneous_neg {m n : ℕ} {p : WordAlgebra m} (hp : Homogeneous p n) :
    Homogeneous (-p) n := by
  intro w hw
  exact hp w (by simpa only [MonoidAlgebra.coeff_neg, Finsupp.support_neg] using hw)

theorem homogeneous_sub {m n : ℕ} {p q : WordAlgebra m}
    (hp : Homogeneous p n) (hq : Homogeneous q n) : Homogeneous (p-q) n := by
  simpa only [sub_eq_add_neg] using homogeneous_add hp (homogeneous_neg hq)

theorem homogeneous_mul {m n k : ℕ} {p q : WordAlgebra m}
    (hp : Homogeneous p n) (hq : Homogeneous q k) : Homogeneous (p*q) (n+k) := by
  classical
  intro w hw
  have hh := MonoidAlgebra.support_coeff_mul_subset p q hw
  rcases Finset.mem_mul.mp hh with ⟨a,ha,b,hb,rfl⟩
  rw [FreeMonoid.length_mul, hp a ha, hq b hb]

theorem homogeneous_signed {m n : ℕ} {p : WordAlgebra m}
    (hp : Homogeneous p n) (b : Bool) : Homogeneous (signed b p) n := by
  cases b <;> simp only [signed, Bool.false_eq_true, if_false, if_true]
  · exact homogeneous_neg hp
  · exact hp

theorem homogeneous_sum {m n : ℕ} (ps : List (WordAlgebra m))
    (h : ∀ p ∈ ps, Homogeneous p n) : Homogeneous ps.sum n := by
  induction ps with
  | nil => exact homogeneous_zero
  | cons p ps ih =>
    exact homogeneous_add (h p (by simp)) (ih (by intro q hq; exact h q (by simp [hq])))

theorem homogeneous_word {m : ℕ} (v : Fin 4 → WordAlgebra m) (weight : Fin 4 → ℕ)
    (h : ∀ i, Homogeneous (v i) (weight i)) (w : List (Fin 4)) :
    Homogeneous (evalWord v w) (w.map weight).sum := by
  induction w with
  | nil => exact homogeneous_one
  | cons i w ih => exact homogeneous_mul (h i) ih

def letterWeight : Fin 4 → ℕ := ![2,1,1,1]

theorem marked_weight : ∀ t ∈ markedTerms,
    (t.2.1.map letterWeight).sum + (t.2.2.map letterWeight).sum = 7 := by decide

theorem homogeneous_gblock {m : ℕ} (y a b c z : WordAlgebra m)
    (hy : Homogeneous y 2) (ha : Homogeneous a 1) (hb : Homogeneous b 1)
    (hc : Homogeneous c 1) (hz : Homogeneous z 1) : Homogeneous (gblock y a b c z) 8 := by
  apply homogeneous_sum
  intro p hp
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  apply homogeneous_signed
  have he : ∀ i : Fin 4, Homogeneous ((![y,a,b,c] : Fin 4 → WordAlgebra m) i)
      (letterWeight i) := by intro i; fin_cases i <;> assumption
  have hl := homogeneous_word _ letterWeight he t.2.1
  have hr := homogeneous_word _ letterWeight he t.2.2
  have htotal := homogeneous_mul (homogeneous_mul hr hz) hl
  have hw := marked_weight t ht
  have heq : (t.2.2.map letterWeight).sum + 1 + (t.2.1.map letterWeight).sum = 8 := by omega
  simpa only [heq] using htotal

theorem homogeneous_gradient {m : ℕ} (y a b c z : WordAlgebra m)
    (hy : Homogeneous y 2) (ha : Homogeneous a 1) (hb : Homogeneous b 1)
    (hc : Homogeneous c 1) (hz : Homogeneous z 1) : Homogeneous (gradient y a b c z) 8 := by
  unfold gradient
  exact homogeneous_sub (homogeneous_add (homogeneous_add
    (homogeneous_sub (homogeneous_sub (homogeneous_gblock _ _ _ _ _ hy ha hb hc hz)
      (homogeneous_gblock _ _ _ _ _ hy ha hc hb hz))
      (homogeneous_gblock _ _ _ _ _ hy hb ha hc hz))
      (homogeneous_gblock _ _ _ _ _ hy hb hc ha hz))
      (homogeneous_gblock _ _ _ _ _ hy hc ha hb hz))
      (homogeneous_gblock _ _ _ _ _ hy hc hb ha hz)

theorem centralPolynomial_homogeneous : Homogeneous centralPolynomial 8 := by
  unfold centralPolynomial
  apply homogeneous_gradient
  · exact homogeneous_sub (homogeneous_mul (homogeneous_generator 0) (homogeneous_generator 1))
      (homogeneous_mul (homogeneous_generator 1) (homogeneous_generator 0))
  all_goals exact homogeneous_generator _

noncomputable def degree {m : ℕ} (p : WordAlgebra m) : ℕ :=
  p.coeff.support.sup FreeMonoid.length

theorem degree_eq_of_homogeneous {m n : ℕ} {p : WordAlgebra m}
    (hp : Homogeneous p n) (hne : p ≠ 0) : degree p = n := by
  have hc : p.coeff ≠ 0 := by
    intro h
    exact hne (MonoidAlgebra.coeff_eq_zero.mp h)
  have hs : p.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hc
  obtain ⟨w,hw⟩ := hs
  unfold degree
  apply le_antisymm
  · exact Finset.sup_le (fun w hw => le_of_eq (hp w hw))
  · rw [← hp w hw]
    exact Finset.le_sup hw

theorem centralPolynomial_degree : degree centralPolynomial = 8 :=
  degree_eq_of_homogeneous centralPolynomial_homogeneous centralPolynomial_ne_zero

theorem centralPolynomial_constant_zero : centralPolynomial.coeff 1 = 0 := by
  by_contra h
  have hh := centralPolynomial_homogeneous 1 (Finsupp.mem_support_iff.mpr h)
  norm_num at hh

def IsCentralPolynomial {m : ℕ} (p : WordAlgebra m) : Prop :=
  (∀ v : Fin m → Mat, ∀ b : Mat, evaluate v p * b = b * evaluate v p) ∧
    ∃ v : Fin m → Mat, evaluate v p ≠ 0

theorem centralPolynomial_central : IsCentralPolynomial centralPolynomial := by
  constructor
  · intro v b
    rw [evaluate_central_scalar v]
    simp
  · refine ⟨witness, ?_⟩
    rw [witness_value]
    intro h
    have he := congrArg (fun a : Mat => a 0 0) h
    norm_num at he

def centralDegrees : Set ℕ := {n | ∃ m, ∃ p : WordAlgebra m,
  0 < degree p ∧ IsCentralPolynomial p ∧ degree p = n}

theorem eight_mem : 8 ∈ centralDegrees :=
  ⟨6, centralPolynomial, by rw [centralPolynomial_degree]; decide,
    centralPolynomial_central, centralPolynomial_degree⟩

noncomputable def minimalCentralDegree : ℕ := by
  classical
  exact Nat.find (show ∃ n, n ∈ centralDegrees from ⟨8,eight_mem⟩)

theorem minimalCentralDegree_mem : minimalCentralDegree ∈ centralDegrees := by
  classical
  exact Nat.find_spec _

theorem minimalCentralDegree_minimal {n : ℕ} (hn : n ∈ centralDegrees) :
    minimalCentralDegree ≤ n := by
  classical
  exact Nat.find_min' _ hn

theorem minimalCentralDegree_le_eight : minimalCentralDegree ≤ 8 :=
  minimalCentralDegree_minimal eight_mem

theorem counterexample : minimalCentralDegree ≠ 3^2 := by
  have h := minimalCentralDegree_le_eight
  norm_num at *
  omega

theorem native_free_evaluation {m : ℕ} (v : Fin m → Mat) (p : FreeAlgebra ℚ (Fin m)) :
    FreeAlgebra.lift ℚ v p = evaluate v (freeNormalForm m p) := by
  have hh : (evaluate v).comp (freeNormalForm m).toAlgHom = FreeAlgebra.lift ℚ v := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [freeNormalForm_generator, evaluate, MonoidAlgebra.lift_single]
  exact (AlgHom.congr_fun hh p).symm

theorem native_polynomial_witness :
    degree (freeNormalForm 6 freePolynomial) = 8 ∧
    (freeNormalForm 6 freePolynomial).coeff 1 = 0 ∧
    (∀ v : Fin 6 → Mat, ∀ b : Mat,
      FreeAlgebra.lift ℚ v freePolynomial * b = b * FreeAlgebra.lift ℚ v freePolynomial) ∧
    FreeAlgebra.lift ℚ witness freePolynomial ≠ 0 := by
  simp only [native_free_evaluation, freePolynomial_normal_form]
  exact ⟨centralPolynomial_degree, centralPolynomial_constant_zero,
    centralPolynomial_central.1, by
      rw [witness_value]
      intro h
      have he := congrArg (fun a : Mat => a 0 0) h
      norm_num at he⟩

end TLMC2761
