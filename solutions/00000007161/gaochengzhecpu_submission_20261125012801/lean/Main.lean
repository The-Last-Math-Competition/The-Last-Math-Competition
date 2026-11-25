/-
  Conjecture 00000007161 — Nonnegative Inverse Eigenvalue Problem (NIEP):
  Complete Formalization & Refutation Across All Readings in Core Lean 4.19.0.

  Zero external dependencies, zero sorry/admit/native_decide/custom axioms.
-/

namespace Conjecture00000007161

/-! ## Elementary Integer Ring Helpers -/

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases Int.le_total 0 a with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
      have hneg : 0 ≤ -a := by omega
      have heq : (-a) * (-a) = a * a := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [← heq]
      exact Int.mul_nonneg hneg hneg

theorem int_mul_eq_zero_iff {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  Int.mul_eq_zero.mp h

/-- Standard quadratic root expansion `(t - r1)(t - r2) = t^2 - (r1 + r2)t + r1 r2`. -/
theorem quad_roots_expand (t r1 r2 : Int) :
    (t - r1) * (t - r2) = t * t - (r1 + r2) * t + r1 * r2 := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.add_mul, Int.mul_comm t r2]
  omega

/-- Standard cubic root expansion `(t - r1)(t - r2)(t - r3)`. -/
theorem cubic_roots_expand (t r1 r2 r3 : Int) :
    (t - r1) * (t - r2) * (t - r3) =
    t * t * t - (r1 + r2 + r3) * (t * t) +
      (r1 * r2 + r1 * r3 + r2 * r3) * t - r1 * r2 * r3 := by
  rw [quad_roots_expand t r1 r2]
  rw [Int.mul_sub (t * t - (r1 + r2) * t + r1 * r2) t r3]
  rw [Int.add_mul (t * t - (r1 + r2) * t) (r1 * r2) t,
      Int.sub_mul (t * t) ((r1 + r2) * t) t,
      Int.add_mul (t * t - (r1 + r2) * t) (r1 * r2) r3,
      Int.sub_mul (t * t) ((r1 + r2) * t) r3]
  have h1 : (r1 + r2) * t * t = (r1 + r2) * (t * t) := Int.mul_assoc (r1 + r2) t t
  have h2 : t * t * r3 = r3 * (t * t) := Int.mul_comm (t * t) r3
  have h3 : (r1 + r2) * (t * t) + r3 * (t * t) = (r1 + r2 + r3) * (t * t) :=
    (Int.add_mul (r1 + r2) r3 (t * t)).symm
  have h4 : (r1 + r2) * t * r3 = (r1 * r3 + r2 * r3) * t := by
    rw [Int.add_mul r1 r2 t, Int.add_mul,
        Int.mul_assoc r1 t r3, Int.mul_comm t r3, ← Int.mul_assoc r1 r3 t,
        Int.mul_assoc r2 t r3, Int.mul_comm t r3, ← Int.mul_assoc r2 r3 t,
        Int.add_mul]
  have h5 : r1 * r2 * t + (r1 * r3 + r2 * r3) * t =
      (r1 * r2 + r1 * r3 + r2 * r3) * t := by
    rw [← Int.add_mul (r1 * r2) (r1 * r3 + r2 * r3) t]
    have : r1 * r2 + (r1 * r3 + r2 * r3) = r1 * r2 + r1 * r3 + r2 * r3 := by omega
    rw [this]
  rw [h1, h2, h4]
  omega

theorem cubic_diff_helper (s u v : Int) :
    (s - u) * (s * s + u * s + v) = s * (s * s) + (v - u * u) * s - u * v := by
  rw [Int.sub_mul s u (s * s + u * s + v),
      Int.mul_add s (s * s + u * s) v, Int.mul_add s (s * s) (u * s),
      Int.mul_add u (s * s + u * s) v, Int.mul_add u (s * s) (u * s),
      Int.sub_mul v (u * u) s]
  have a2 : s * (u * s) = u * (s * s) := by
    rw [← Int.mul_assoc s u s, Int.mul_comm s u, Int.mul_assoc u s s]
  have a3 : u * (u * s) = u * u * s := (Int.mul_assoc u u s).symm
  have a4 : s * v = v * s := Int.mul_comm s v
  rw [a2, a3, a4]
  omega

/-! ## Section 1: Gaussian Integers `ℤ[i]` for Exact Complex Spectral Evaluation -/

/-- Exact Gaussian integers `a + b i` (`a, b ∈ ℤ`). -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace GaussInt

def ofInt (n : Int) : GaussInt := ⟨n, 0⟩
def zero : GaussInt := ⟨0, 0⟩
def one : GaussInt := ⟨1, 0⟩
def I : GaussInt := ⟨0, 1⟩
def negI : GaussInt := ⟨0, -1⟩

def add (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩
def mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def sq (z : GaussInt) : GaussInt := mul z z

theorem ext {z w : GaussInt} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

theorem mul_comm (z w : GaussInt) : mul z w = mul w z := by
  apply ext <;> dsimp [mul]
  · rw [Int.mul_comm z.re w.re, Int.mul_comm z.im w.im]
  · rw [Int.mul_comm z.re w.im, Int.mul_comm z.im w.re, Int.add_comm]

theorem mul_assoc (u v w : GaussInt) : mul (mul u v) w = mul u (mul v w) := by
  apply ext <;> dsimp [mul]
  · rw [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add]
    rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
    omega
  · rw [Int.sub_mul, Int.add_mul, Int.mul_add, Int.mul_sub]
    rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
    omega

theorem sub_mul_add (z w : GaussInt) : mul (sub z w) (add z w) = sub (sq z) (sq w) := by
  apply ext <;> dsimp [mul, sub, add, sq]
  · rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_add, Int.mul_add]
    rw [Int.mul_comm w.re z.re, Int.mul_comm w.im z.im]
    omega
  · rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_add, Int.mul_add]
    rw [Int.mul_comm z.re w.im, Int.mul_comm w.im z.re,
        Int.mul_comm z.im w.re, Int.mul_comm w.re z.im]
    omega

theorem I_sq : sq I = ofInt (-1) := rfl
theorem negI_sq : sq negI = ofInt (-1) := rfl

end GaussInt

/-! ## Section 2: General `n × n` Integer Matrices, Nonnegativity, and Power Traces -/

/-- An `n × n` matrix over `ℤ`. -/
abbrev Mat (n : Nat) := Fin n → Fin n → Int

/-- An `n`-vector over `ℤ`. -/
abbrev Vec (n : Nat) := Fin n → Int

/-- Entrywise nonnegativity `A_{ij} ≥ 0`. -/
def IsNonneg (n : Nat) (A : Mat n) : Prop :=
  ∀ i j : Fin n, 0 ≤ A i j

/-- Matrix symmetry `A_{ij} = A_{ji}`. -/
def IsSymmetric (n : Nat) (A : Mat n) : Prop :=
  ∀ i j : Fin n, A i j = A j i

/-- Zero diagonal (hollow matrix, implying trace zero). -/
def IsZeroDiag (n : Nat) (A : Mat n) : Prop :=
  ∀ i : Fin n, A i i = 0

/-- Summation `∑_{k < m} f(k)` for bounded indices in `Fin n`. -/
def finSumAux (n : Nat) : (m : Nat) → (m ≤ n) → (Fin n → Int) → Int
  | 0, _, _ => 0
  | m + 1, hm, f =>
      finSumAux n m (Nat.le_of_succ_le hm) f + f ⟨m, hm⟩

/-- Exact finite sum `∑_{i : Fin n} f i`. -/
def finSum (n : Nat) (f : Fin n → Int) : Int :=
  finSumAux n n (Nat.le_refl n) f

theorem finSumAux_nonneg (n : Nat) (m : Nat) (hm : m ≤ n) (f : Fin n → Int)
    (hf : ∀ i : Fin n, 0 ≤ f i) : 0 ≤ finSumAux n m hm f := by
  induction m with
  | zero => exact Int.le_refl 0
  | succ k ih =>
      unfold finSumAux
      have h1 : 0 ≤ finSumAux n k (Nat.le_of_succ_le hm) f := ih (Nat.le_of_succ_le hm)
      have h2 : 0 ≤ f ⟨k, hm⟩ := hf ⟨k, hm⟩
      omega

/-- Sum of nonnegative integers over `Fin n` is nonnegative. -/
theorem finSum_nonneg (n : Nat) (f : Fin n → Int) (hf : ∀ i : Fin n, 0 ≤ f i) :
    0 ≤ finSum n f :=
  finSumAux_nonneg n n (Nat.le_refl n) f hf

theorem finSumAux_zero (n : Nat) (m : Nat) (hm : m ≤ n) (f : Fin n → Int)
    (hf : ∀ i : Fin n, f i = 0) : finSumAux n m hm f = 0 := by
  induction m with
  | zero => rfl
  | succ k ih =>
      unfold finSumAux
      rw [ih (Nat.le_of_succ_le hm), hf ⟨k, hm⟩]
      rfl

theorem finSum_zero (n : Nat) (f : Fin n → Int) (hf : ∀ i : Fin n, f i = 0) :
    finSum n f = 0 :=
  finSumAux_zero n n (Nat.le_refl n) f hf

theorem finSumAux_add (n : Nat) (m : Nat) (hm : m ≤ n) (f g : Fin n → Int) :
    finSumAux n m hm (fun i => f i + g i) =
    finSumAux n m hm f + finSumAux n m hm g := by
  induction m with
  | zero => rfl
  | succ k ih =>
      unfold finSumAux
      rw [ih (Nat.le_of_succ_le hm)]
      dsimp
      omega

theorem finSum_add (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g :=
  finSumAux_add n n (Nat.le_refl n) f g

theorem finSumAux_sub (n : Nat) (m : Nat) (hm : m ≤ n) (f g : Fin n → Int) :
    finSumAux n m hm (fun i => f i - g i) =
    finSumAux n m hm f - finSumAux n m hm g := by
  induction m with
  | zero => rfl
  | succ k ih =>
      unfold finSumAux
      rw [ih (Nat.le_of_succ_le hm)]
      dsimp
      omega

theorem finSum_sub (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g :=
  finSumAux_sub n n (Nat.le_refl n) f g

theorem finSumAux_const (n : Nat) (m : Nat) (hm : m ≤ n) (c : Int) :
    finSumAux n m hm (fun _ => c) = (m : Int) * c := by
  induction m with
  | zero => simp [finSumAux]
  | succ k ih =>
      unfold finSumAux
      rw [ih (Nat.le_of_succ_le hm)]
      dsimp
      have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hcast, Int.add_mul, Int.one_mul]

theorem finSum_const (n : Nat) (c : Int) :
    finSum n (fun _ => c) = (n : Int) * c :=
  finSumAux_const n n (Nat.le_refl n) c

theorem finSumAux_delta (n : Nat) (m : Nat) (hm : m ≤ n) (p : Fin n) (v : Int) :
    finSumAux n m hm (fun j => if j = p then v else 0) =
    if p.val < m then v else 0 := by
  induction m with
  | zero => simp [finSumAux]
  | succ k ih =>
      unfold finSumAux
      rw [ih (Nat.le_of_succ_le hm)]
      dsimp
      by_cases hpk : p.val = k
      · have heq : (⟨k, hm⟩ : Fin n) = p := Fin.ext hpk.symm
        have hlt : ¬ (p.val < k) := by omega
        have hlt2 : p.val < k + 1 := by omega
        simp [heq, hlt, hlt2]
      · have hne : (⟨k, hm⟩ : Fin n) ≠ p := by
          intro h; apply hpk; exact congrArg Fin.val h.symm
        by_cases hlt : p.val < k
        · have hlt2 : p.val < k + 1 := by omega
          simp [hne, hlt, hlt2]
        · have hlt2 : ¬ (p.val < k + 1) := by omega
          simp [hne, hlt, hlt2]

theorem finSum_delta (n : Nat) (p : Fin n) (v : Int) :
    finSum n (fun j => if j = p then v else 0) = v := by
  unfold finSum
  rw [finSumAux_delta n n (Nat.le_refl n) p v]
  simp [p.isLt]

/-- Identity matrix `I_n`. -/
def matId (n : Nat) : Mat n :=
  fun i j => if i = j then 1 else 0

/-- Matrix addition `A + B`. -/
def matAdd (n : Nat) (A B : Mat n) : Mat n :=
  fun i j => A i j + B i j

/-- Matrix multiplication `A B`. -/
def matMul (n : Nat) (A B : Mat n) : Mat n :=
  fun i j => finSum n (fun k => A i k * B k j)

/-- Matrix-vector product `A v`. -/
def matVecMul (n : Nat) (A : Mat n) (v : Vec n) : Vec n :=
  fun i => finSum n (fun j => A i j * v j)

/-- Scalar multiple of a vector `c • v`. -/
def smulVec (n : Nat) (c : Int) (v : Vec n) : Vec n :=
  fun i => c * v i

/-- Matrix powers `A^k`. -/
def matPow (n : Nat) (A : Mat n) : Nat → Mat n
  | 0 => matId n
  | k + 1 => matMul n (matPow n A k) A

/-- Matrix trace `tr(A) = ∑_i A_{ii}`. -/
def trace (n : Nat) (A : Mat n) : Int :=
  finSum n (fun i => A i i)

/-- Every zero-diagonal matrix has trace `0`. -/
theorem trace_eq_zero_of_zeroDiag (n : Nat) (A : Mat n) (h : IsZeroDiag n A) :
    trace n A = 0 :=
  finSum_zero n (fun i => A i i) h

/-- Every entrywise nonnegative matrix has nonnegative trace. -/
theorem trace_nonneg_of_nonneg (n : Nat) (A : Mat n) (hA : IsNonneg n A) :
    0 ≤ trace n A :=
  finSum_nonneg n (fun i => A i i) (fun i => hA i i)

/-- Product of two nonnegative `n × n` matrices is entrywise nonnegative. -/
theorem matMul_nonneg (n : Nat) (A B : Mat n)
    (hA : IsNonneg n A) (hB : IsNonneg n B) : IsNonneg n (matMul n A B) := by
  intro i j
  unfold matMul
  apply finSum_nonneg
  intro k
  exact Int.mul_nonneg (hA i k) (hB k j)

/-- Identity matrix `I_n` is entrywise nonnegative. -/
theorem matId_nonneg (n : Nat) : IsNonneg n (matId n) := by
  intro i j; unfold matId; split <;> omega

/-- Every power `A^k` (`k ≥ 0`) of a nonnegative matrix is entrywise nonnegative. -/
theorem matPow_nonneg (n : Nat) (A : Mat n) (hA : IsNonneg n A) (k : Nat) :
    IsNonneg n (matPow n A k) := by
  induction k with
  | zero => exact matId_nonneg n
  | succ m ih => exact matMul_nonneg n (matPow n A m) A ih hA

/-- Universal Newton power-sum obstruction: `tr(A^k) ≥ 0` for every nonnegative `A` and `k ≥ 0`. -/
theorem trace_pow_nonneg_of_nonneg (n : Nat) (A : Mat n) (hA : IsNonneg n A) (k : Nat) :
    0 ≤ trace n (matPow n A k) :=
  trace_nonneg_of_nonneg n (matPow n A k) (matPow_nonneg n A hA k)

/-- Universal trace-of-squares obstruction: `tr(A^2) ≥ 0` for every nonnegative `A`. -/
theorem trace_sq_nonneg_of_nonneg (n : Nat) (A : Mat n) (hA : IsNonneg n A) :
    0 ≤ trace n (matMul n A A) :=
  trace_nonneg_of_nonneg n (matMul n A A) (matMul_nonneg n A A hA hA)

/-! ### Explicit `2 × 2` and `3 × 3` Characteristic Polynomials and Expansions -/

def i2_0 : Fin 2 := ⟨0, by omega⟩
def i2_1 : Fin 2 := ⟨1, by omega⟩

def i3_0 : Fin 3 := ⟨0, by omega⟩
def i3_1 : Fin 3 := ⟨1, by omega⟩
def i3_2 : Fin 3 := ⟨2, by omega⟩

def det2 (A : Mat 2) : Int :=
  A i2_0 i2_0 * A i2_1 i2_1 - A i2_0 i2_1 * A i2_1 i2_0

/-- Characteristic polynomial `det(t I_2 - A)` evaluated at `t ∈ ℤ`. -/
def charPoly2 (A : Mat 2) (t : Int) : Int :=
  (t - A i2_0 i2_0) * (t - A i2_1 i2_1) - A i2_0 i2_1 * A i2_1 i2_0

theorem charPoly2_expand (A : Mat 2) (t : Int) :
    charPoly2 A t =
    t * t - (A i2_0 i2_0 + A i2_1 i2_1) * t +
      (A i2_0 i2_0 * A i2_1 i2_1 - A i2_0 i2_1 * A i2_1 i2_0) := by
  unfold charPoly2
  rw [quad_roots_expand t (A i2_0 i2_0) (A i2_1 i2_1)]
  omega

/-- Characteristic polynomial `det(z I_2 - A)` evaluated at `z ∈ ℤ[i]`. -/
def charPoly2G (A : Mat 2) (z : GaussInt) : GaussInt :=
  let tr := A i2_0 i2_0 + A i2_1 i2_1
  let dt := det2 A
  GaussInt.add (GaussInt.sub (GaussInt.sq z) (GaussInt.mul (GaussInt.ofInt tr) z))
    (GaussInt.ofInt dt)

/-- Characteristic polynomial `det(t I_3 - A)` evaluated at `t ∈ ℤ`. -/
def charPoly3 (A : Mat 3) (t : Int) : Int :=
  let b00 := t - A i3_0 i3_0
  let b01 := -A i3_0 i3_1
  let b02 := -A i3_0 i3_2
  let b10 := -A i3_1 i3_0
  let b11 := t - A i3_1 i3_1
  let b12 := -A i3_1 i3_2
  let b20 := -A i3_2 i3_0
  let b21 := -A i3_2 i3_1
  let b22 := t - A i3_2 i3_2
  b00 * (b11 * b22 - b12 * b21) -
  b01 * (b10 * b22 - b12 * b20) +
  b02 * (b10 * b21 - b11 * b20)

theorem charPoly3_expand (A : Mat 3) (t : Int) :
    let a00 := A i3_0 i3_0; let a01 := A i3_0 i3_1; let a02 := A i3_0 i3_2
    let a10 := A i3_1 i3_0; let a11 := A i3_1 i3_1; let a12 := A i3_1 i3_2
    let a20 := A i3_2 i3_0; let a21 := A i3_2 i3_1; let a22 := A i3_2 i3_2
    charPoly3 A t =
    t * t * t - (a00 + a11 + a22) * (t * t) +
      (a00 * a11 + a00 * a22 + a11 * a22 - a01 * a10 - a02 * a20 - a12 * a21) * t -
      (a00 * a11 * a22 + a01 * a12 * a20 + a02 * a10 * a21 -
       a00 * a12 * a21 - a01 * a10 * a22 - a02 * a11 * a20) := by
  dsimp
  unfold charPoly3
  let a00 := A i3_0 i3_0; let a01 := A i3_0 i3_1; let a02 := A i3_0 i3_2
  let a10 := A i3_1 i3_0; let a11 := A i3_1 i3_1; let a12 := A i3_1 i3_2
  let a20 := A i3_2 i3_0; let a21 := A i3_2 i3_1; let a22 := A i3_2 i3_2
  change (t - a00) * ((t - a11) * (t - a22) - -a12 * -a21) -
         -a01 * (-a10 * (t - a22) - -a12 * -a20) +
         -a02 * (-a10 * -a21 - (t - a11) * -a20) =
         t * t * t - (a00 + a11 + a22) * (t * t) +
           (a00 * a11 + a00 * a22 + a11 * a22 - a01 * a10 - a02 * a20 - a12 * a21) * t -
           (a00 * a11 * a22 + a01 * a12 * a20 + a02 * a10 * a21 -
            a00 * a12 * a21 - a01 * a10 * a22 - a02 * a11 * a20)
  have p1 : -a12 * -a21 = a12 * a21 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have p2 : -a12 * -a20 = a12 * a20 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have p3 : -a10 * -a21 = a10 * a21 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  rw [p1, p2, p3]
  have term1 : (t - a00) * ((t - a11) * (t - a22) - a12 * a21) =
      (t - a00) * (t - a11) * (t - a22) - (a12 * a21) * t + a00 * a12 * a21 := by
    rw [Int.mul_sub, ← Int.mul_assoc (t - a00) (t - a11) (t - a22),
        Int.sub_mul t a00 (a12 * a21), Int.mul_comm t (a12 * a21),
        ← Int.mul_assoc a00 a12 a21]
    omega
  have term2 : -(-a01 * (-a10 * (t - a22) - a12 * a20)) =
      -(a01 * a10) * t + a01 * a10 * a22 - a01 * a12 * a20 := by
    rw [Int.neg_mul a01, Int.neg_neg, Int.mul_sub a01,
        Int.neg_mul a10 (t - a22), Int.mul_neg a01,
        Int.mul_sub a10 t a22, Int.mul_sub a01,
        ← Int.mul_assoc a01 a10 t, ← Int.mul_assoc a01 a10 a22,
        ← Int.mul_assoc a01 a12 a20, Int.neg_mul (a01 * a10) t]
    omega
  have term3 : -a02 * (a10 * a21 - (t - a11) * -a20) =
      -(a02 * a20) * t + a02 * a11 * a20 - a02 * a10 * a21 := by
    rw [Int.mul_neg (t - a11) a20, Int.sub_mul t a11 a20,
        Int.neg_mul a02, Int.mul_sub a02, Int.mul_neg a02,
        Int.mul_sub a02 (t * a20) (a11 * a20),
        ← Int.mul_assoc a02 a10 a21,
        ← Int.mul_assoc a02 t a20, Int.mul_comm a02 t, Int.mul_assoc t a02 a20,
        Int.mul_comm t (a02 * a20),
        ← Int.mul_assoc a02 a11 a20, Int.neg_mul (a02 * a20) t]
    omega
  have hsub12 :
      (t - a00) * ((t - a11) * (t - a22) - a12 * a21) -
      -a01 * (-a10 * (t - a22) - a12 * a20) =
      (t - a00) * ((t - a11) * (t - a22) - a12 * a21) +
      -(-a01 * (-a10 * (t - a22) - a12 * a20)) := Int.sub_eq_add_neg
  have hrhs_t :
      (a00 * a11 + a00 * a22 + a11 * a22 - a01 * a10 - a02 * a20 - a12 * a21) * t =
      (a00 * a11 + a00 * a22 + a11 * a22) * t - (a01 * a10) * t -
        (a02 * a20) * t - (a12 * a21) * t := by
    rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
  have hn1 : -(a01 * a10) * t = -((a01 * a10) * t) := Int.neg_mul (a01 * a10) t
  have hn2 : -(a02 * a20) * t = -((a02 * a20) * t) := Int.neg_mul (a02 * a20) t
  rw [hsub12, term1, term2, term3, cubic_roots_expand t a00 a11 a22, hrhs_t, hn1, hn2]
  omega

/-- Strong connectivity / irreducibility of a nonnegative `2 × 2` matrix (`I + A > 0`). -/
def IsIrreducible2 (A : Mat 2) : Prop :=
  ∀ i j : Fin 2, 0 < (matAdd 2 (matId 2) A) i j

/-- Strong connectivity / irreducibility of a nonnegative `3 × 3` matrix (`I + A + A^2 > 0`). -/
def IsIrreducible3 (A : Mat 3) : Prop :=
  ∀ i j : Fin 3, 0 < (matAdd 3 (matAdd 3 (matId 3) A) (matMul 3 A A)) i j

/-- `A ∈ M_2(ℤ_{≥0})` realizes integer spectrum `(r1, r2)`. -/
def Realizes2Int (A : Mat 2) (r1 r2 : Int) : Prop :=
  IsNonneg 2 A ∧ ∀ t : Int, charPoly2 A t = (t - r1) * (t - r2)

/-- `A ∈ M_2(ℤ_{≥0})` realizes Gaussian-integer spectrum `(z1, z2)`. -/
def Realizes2Gauss (A : Mat 2) (z1 z2 : GaussInt) : Prop :=
  IsNonneg 2 A ∧
  ∀ z : GaussInt, charPoly2G A z = GaussInt.mul (GaussInt.sub z z1) (GaussInt.sub z z2)

/-- `A ∈ M_3(ℤ_{≥0})` realizes integer spectrum `(r1, r2, r3)`. -/
def Realizes3Int (A : Mat 3) (r1 r2 r3 : Int) : Prop :=
  IsNonneg 3 A ∧ ∀ t : Int, charPoly3 A t = (t - r1) * (t - r2) * (t - r3)

/-- Helper constructor for `2 × 2` matrices from literal rows. -/
def mkMat2 (a00 a01 a10 a11 : Int) : Mat 2 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a00 | 0, _ => a01
    | _, 0 => a10 | _, _ => a11

/-- Helper constructor for `3 × 3` matrices from literal rows. -/
def mkMat3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : Mat 3 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a00 | 0, 1 => a01 | 0, _ => a02
    | 1, 0 => a10 | 1, 1 => a11 | 1, _ => a12
    | _, 0 => a20 | _, 1 => a21 | _, _ => a22

theorem mkMat2_nonneg {a00 a01 a10 a11 : Int}
    (h00 : 0 ≤ a00) (h01 : 0 ≤ a01) (h10 : 0 ≤ a10) (h11 : 0 ≤ a11) :
    IsNonneg 2 (mkMat2 a00 a01 a10 a11) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩
  unfold mkMat2; dsimp
  match i, j with
  | 0, 0 => exact h00 | 0, _ + 1 => exact h01
  | _ + 1, 0 => exact h10 | _ + 1, _ + 1 => exact h11

theorem mkMat3_nonneg {a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int}
    (h00 : 0 ≤ a00) (h01 : 0 ≤ a01) (h02 : 0 ≤ a02)
    (h10 : 0 ≤ a10) (h11 : 0 ≤ a11) (h12 : 0 ≤ a12)
    (h20 : 0 ≤ a20) (h21 : 0 ≤ a21) (h22 : 0 ≤ a22) :
    IsNonneg 3 (mkMat3 a00 a01 a02 a10 a11 a12 a20 a21 a22) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩
  unfold mkMat3; dsimp
  match i, j with
  | 0, 0 => exact h00 | 0, 1 => exact h01 | 0, _ + 2 => exact h02
  | 1, 0 => exact h10 | 1, 1 => exact h11 | 1, _ + 2 => exact h12
  | _ + 2, 0 => exact h20 | _ + 2, 1 => exact h21 | _ + 2, _ + 2 => exact h22

theorem fin2_cases {P : Fin 2 → Prop} (h0 : P i2_0) (h1 : P i2_1) : ∀ i : Fin 2, P i := by
  intro ⟨k, hk⟩
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | k + 2 => omega

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P i3_0) (h1 : P i3_1) (h2 : P i3_2) :
    ∀ i : Fin 3, P i := by
  intro ⟨k, hk⟩
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | k + 3 => omega

/-! ## Section 3: Positive Non-Vacuity Witnesses (Cyclic Permutation Matrices) -/

/-- `2 × 2` cyclic permutation matrix `P_2 = [[0, 1], [1, 0]]`. -/
def P2 : Mat 2 := mkMat2 0 1 1 0

/-- `3 × 3` cyclic permutation matrix `P_3 = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]`. -/
def P3 : Mat 3 := mkMat3 0 1 0 0 0 1 1 0 0

theorem P2_positive_witness :
    IsNonneg 2 P2 ∧ IsSymmetric 2 P2 ∧ IsZeroDiag 2 P2 ∧ IsIrreducible2 P2 ∧
    Realizes2Int P2 1 (-1) := by
  have hnn : IsNonneg 2 P2 := mkMat2_nonneg (by omega) (by omega) (by omega) (by omega)
  refine ⟨hnn, ?_, ?_, ?_, ⟨hnn, ?_⟩⟩
  · exact fin2_cases (fin2_cases rfl rfl) (fin2_cases rfl rfl)
  · exact fin2_cases rfl rfl
  · exact fin2_cases (fin2_cases (by decide) (by decide)) (fin2_cases (by decide) (by decide))
  · intro t
    rw [charPoly2_expand, quad_roots_expand]
    dsimp [P2, mkMat2, i2_0, i2_1]

theorem P3_positive_witness :
    IsNonneg 3 P3 ∧ IsZeroDiag 3 P3 ∧ IsIrreducible3 P3 ∧
    (∀ t : Int, charPoly3 P3 t = t ^ 3 - 1 ∧ t ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1)) := by
  have hnn : IsNonneg 3 P3 := mkMat3_nonneg
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨hnn, fin3_cases rfl rfl rfl, ?_, ?_⟩
  · exact fin3_cases
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
  · intro t
    have hpow3 : t ^ 3 = t * t * t := by
      simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc]
    have hpow2 : t ^ 2 = t * t := by
      simp [Int.pow_succ, Int.pow_zero]
    rw [charPoly3_expand, hpow3, hpow2]
    dsimp [P3, mkMat3, i3_0, i3_1, i3_2]
    refine ⟨by omega, ?_⟩
    rw [Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_add, Int.mul_one,
        ← Int.mul_assoc t t t]
    omega

/-- Over `ℤ[i]`, `(z - 1)(z - i)(z + 1)(z + i) = z^4 - 1`, witnessing the 4-cycle spectrum `(1, i, -1, -i)`. -/
theorem four_cycle_roots_factorization (z : GaussInt) :
    GaussInt.mul
      (GaussInt.mul (GaussInt.sub z GaussInt.one) (GaussInt.sub z GaussInt.I))
      (GaussInt.mul (GaussInt.add z GaussInt.one) (GaussInt.add z GaussInt.I)) =
    GaussInt.sub (GaussInt.sq (GaussInt.sq z)) GaussInt.one := by
  let a := GaussInt.sub z GaussInt.one
  let b := GaussInt.sub z GaussInt.I
  let c := GaussInt.add z GaussInt.one
  let d := GaussInt.add z GaussInt.I
  have h1 : GaussInt.mul (GaussInt.mul a b) (GaussInt.mul c d) =
      GaussInt.mul (GaussInt.mul a c) (GaussInt.mul b d) := by
    rw [GaussInt.mul_assoc a b (GaussInt.mul c d),
        ← GaussInt.mul_assoc b c d,
        GaussInt.mul_comm b c,
        GaussInt.mul_assoc c b d,
        ← GaussInt.mul_assoc a c (GaussInt.mul b d)]
  rw [h1]
  have hac : GaussInt.mul a c = GaussInt.sub (GaussInt.sq z) GaussInt.one := by
    dsimp [a, c]; rw [GaussInt.sub_mul_add]; rfl
  have hbd : GaussInt.mul b d = GaussInt.add (GaussInt.sq z) GaussInt.one := by
    dsimp [b, d]; rw [GaussInt.sub_mul_add]
    apply GaussInt.ext <;> dsimp [GaussInt.sub, GaussInt.add, GaussInt.sq,
      GaussInt.mul, GaussInt.I, GaussInt.one] <;> omega
  rw [hac, hbd, GaussInt.sub_mul_add]
  rfl

/-- General `n × n` scaled cyclic shift matrix `r P_{cyc}` (`n ≥ 1`, `r ≥ 0`). -/
def cyclicShiftMat (n : Nat) (_hn : 0 < n) (r : Int) : Mat n :=
  fun i j => if j.val = (i.val + 1) % n then r else 0

theorem cyclicShiftMat_nonneg (n : Nat) (hn : 0 < n) (r : Int) (hr : 0 ≤ r) :
    IsNonneg n (cyclicShiftMat n hn r) := by
  intro i j; unfold cyclicShiftMat; split <;> omega

/-! ## Section 4: Refutation of Reading I — Cyclic Root-of-Unity Lists & Unions -/

/-- Universal model of a cyclic root-of-unity piece `{r ζ_k^s : 0 ≤ s < k}` (`k ≥ 1, r ≥ 0`)
    over an arbitrary spectral carrier `α` equipped with a modulus map `absMap : α → α`:
    every piece contains its positive real generator `r` (`s = 0`), and every element `z`
    in the piece has `absMap z = r`. -/
structure CyclicPiece (α : Type) (absMap : α → α) where
  radius : α
  elems : List α
  radius_mem : radius ∈ elems
  abs_eq_radius : ∀ z ∈ elems, absMap z = radius

/-- `L` can be covered/partitioned by a collection of cyclic root-of-unity pieces. -/
def CoveredByCyclicPieces {α : Type} (absMap : α → α) (L : List α) : Prop :=
  ∃ pieces : List (CyclicPiece α absMap),
    (∀ z, z ∈ L ↔ ∃ P ∈ pieces, z ∈ P.elems)

/-- **Modulus-Presence Obstruction Theorem:** Every spectrum covered by cyclic root-of-unity
    pieces (including single cyclic lists and arbitrary disjoint unions of cyclic lists)
    must contain `absMap z` whenever it contains `z`. -/
theorem abs_mem_of_coveredByCyclicPieces {α : Type} {absMap : α → α} {L : List α}
    (hcov : CoveredByCyclicPieces absMap L) :
    ∀ z ∈ L, absMap z ∈ L := by
  rcases hcov with ⟨pieces, hiff⟩
  intro z hz
  rcases (hiff z).mp hz with ⟨P, hPmem, hzP⟩
  have hrad : absMap z = P.radius := P.abs_eq_radius z hzP
  rw [hrad]
  exact (hiff P.radius).mpr ⟨P, hPmem, P.radius_mem⟩

/-- Absolute value map `z ↦ |z|` on `ℤ`. -/
def intAbsMap (x : Int) : Int := (x.natAbs : Int)

/-- **Counterexample 1 (`n = 2`, positive-trace diagonal):**
    `diag(2, 1)` is nonnegative and realizes `(2, 1)`, which is not a single 2-cycle `(r, -r)`. -/
def diag21 : Mat 2 := mkMat2 2 0 0 1

theorem diag21_non_cyclic :
    Realizes2Int diag21 2 1 ∧ ¬ (∃ r : Int, (2 : Int) + 1 = r + (-r)) := by
  refine ⟨⟨mkMat2_nonneg (by omega) (by omega) (by omega) (by omega), ?_⟩, ?_⟩
  · intro t
    rw [charPoly2_expand, quad_roots_expand]
    dsimp [diag21, mkMat2, i2_0, i2_1]
  · intro ⟨r, hr⟩; omega

/-- **Counterexample 2 (`n = 3`, symmetric, zero-diagonal, irreducible `{0,1}`-matrix):**
    `K3Adj = J_3 - I_3` realizes `(2, -1, -1)`, which is neither a cyclic root-of-unity list
    nor any union of cyclic root-of-unity lists. -/
def K3Adj : Mat 3 := mkMat3 0 1 1 1 0 1 1 1 0

theorem K3Adj_realizes_and_not_union_cyclic :
    IsNonneg 3 K3Adj ∧ IsSymmetric 3 K3Adj ∧ IsZeroDiag 3 K3Adj ∧ IsIrreducible3 K3Adj ∧
    Realizes3Int K3Adj 2 (-1) (-1) ∧
    ¬ CoveredByCyclicPieces intAbsMap [2, -1, -1] := by
  have hnn : IsNonneg 3 K3Adj := mkMat3_nonneg
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨hnn, ?_, fin3_cases rfl rfl rfl, ?_, ⟨hnn, ?_⟩, ?_⟩
  · exact fin3_cases
      (fin3_cases rfl rfl rfl)
      (fin3_cases rfl rfl rfl)
      (fin3_cases rfl rfl rfl)
  · exact fin3_cases
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
  · intro t
    rw [charPoly3_expand, cubic_roots_expand]
    dsimp [K3Adj, mkMat3, i3_0, i3_1, i3_2]
  · intro hcov
    have hmem : intAbsMap (-1) ∈ ([2, -1, -1] : List Int) :=
      abs_mem_of_coveredByCyclicPieces hcov (-1) (by simp)
    have habs : intAbsMap (-1) = 1 := rfl
    rw [habs] at hmem
    simp at hmem

/-! ### Infinite Family 1: Hollow All-Ones Matrices `A_n = J_n - I_n` for All `n ≥ 3` -/

/-- Hollow all-ones matrix `A_n = J_n - I_n` (`0` on diagonal, `1` off diagonal). -/
def hollowOnes (n : Nat) : Mat n :=
  fun i j => if i = j then 0 else 1

/-- All-ones vector `1_n`. -/
def allOnes (n : Nat) : Vec n := fun _ => 1

/-- Standard basis difference vector `e_0 - e_k` (`n ≥ 1`). -/
def diffBasis (n : Nat) (hn : 0 < n) (k : Fin n) : Vec n :=
  fun j => (if j = ⟨0, hn⟩ then 1 else 0) - (if j = k then 1 else 0)

/-- Spectrum list `[n - 1, -1, ..., -1]` of `J_n - I_n`. -/
def hollowSpectrum (n : Nat) : List Int :=
  ((n - 1 : Nat) : Int) :: List.replicate (n - 1) (-1)

theorem hollowOnes_eigen_allOnes (n : Nat) (hn : 1 ≤ n) :
    matVecMul n (hollowOnes n) (allOnes n) =
    smulVec n ((n - 1 : Nat) : Int) (allOnes n) := by
  funext i
  unfold matVecMul hollowOnes allOnes smulVec
  have hrew : (fun j : Fin n => (if i = j then (0 : Int) else 1) * 1) =
      (fun j : Fin n => 1 - (if j = i then 1 else 0)) := by
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · have hji : i ≠ j := fun h => hij h.symm
      simp [hij, hji]
  rw [hrew, finSum_sub, finSum_const, finSum_delta]
  dsimp
  omega

theorem hollowOnes_eigen_diffBasis (n : Nat) (hn : 0 < n) (k : Fin n) (hk : 0 < k.val) :
    (diffBasis n hn k ⟨0, hn⟩ ≠ 0) ∧
    matVecMul n (hollowOnes n) (diffBasis n hn k) =
    smulVec n (-1) (diffBasis n hn k) := by
  have hk0 : (⟨0, hn⟩ : Fin n) ≠ k := by
    intro h
    have hval : (0 : Nat) = k.val := congrArg Fin.val h
    omega
  refine ⟨?_, ?_⟩
  · unfold diffBasis
    simp [hk0]
  · funext i
    unfold matVecMul diffBasis smulVec
    have hlin : (fun j : Fin n =>
          hollowOnes n i j * ((if j = ⟨0, hn⟩ then 1 else 0) - (if j = k then 1 else 0))) =
        (fun j : Fin n =>
          (if j = ⟨0, hn⟩ then hollowOnes n i ⟨0, hn⟩ else 0) -
          (if j = k then hollowOnes n i k else 0)) := by
      funext j
      rw [Int.mul_sub]
      by_cases hj0 : j = ⟨0, hn⟩
      · subst hj0; simp [hk0]
      · by_cases hjk : j = k
        · subst hjk; simp [hj0]
        · simp [hj0, hjk]
    rw [hlin, finSum_sub, finSum_delta, finSum_delta]
    unfold hollowOnes
    by_cases hi0 : i = ⟨0, hn⟩
    · subst hi0; simp [hk0]
    · by_cases hik : i = k
      · subst hik; simp [hi0]
      · simp [hi0, hik]

/-- **Infinite Family Theorem (`n ≥ 3`):** For every `n ≥ 3`, `hollowOnes n = J_n - I_n`
    is nonnegative, symmetric, and zero-diagonal, has Perron eigenvalue `n - 1` on `1_n`
    and eigenvalue `-1` on all `n - 1` independent vectors `e_0 - e_k` (`1 ≤ k < n`),
    and its spectrum `hollowSpectrum n` cannot be covered by cyclic root-of-unity pieces. -/
theorem hollowOnes_infinite_counterexample_family (n : Nat) (hn : 3 ≤ n) :
    IsNonneg n (hollowOnes n) ∧
    IsSymmetric n (hollowOnes n) ∧
    IsZeroDiag n (hollowOnes n) ∧
    matVecMul n (hollowOnes n) (allOnes n) = smulVec n ((n - 1 : Nat) : Int) (allOnes n) ∧
    (∀ k : Fin n, 0 < k.val →
      matVecMul n (hollowOnes n) (diffBasis n (by omega) k) =
      smulVec n (-1) (diffBasis n (by omega) k)) ∧
    ¬ CoveredByCyclicPieces intAbsMap (hollowSpectrum n) := by
  refine ⟨?_, ?_, ?_, hollowOnes_eigen_allOnes n (by omega), ?_, ?_⟩
  · intro i j; unfold hollowOnes; split <;> omega
  · intro i j; unfold hollowOnes
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  · intro i; unfold hollowOnes; simp
  · intro k hk
    exact (hollowOnes_eigen_diffBasis n (by omega) k hk).2
  · intro hcov
    have hneg_mem : (-1 : Int) ∈ hollowSpectrum n := by
      unfold hollowSpectrum
      cases hnm1 : n - 1 with
      | zero => omega
      | succ m => simp [List.replicate]
    have h1_mem : intAbsMap (-1) ∈ hollowSpectrum n :=
      abs_mem_of_coveredByCyclicPieces hcov (-1) hneg_mem
    have habs : intAbsMap (-1) = 1 := rfl
    rw [habs] at h1_mem
    unfold hollowSpectrum at h1_mem
    simp only [List.mem_cons] at h1_mem
    rcases h1_mem with hhead | htail
    · omega
    · have hrep : 1 = (-1 : Int) := List.eq_of_mem_replicate htail
      omega

/-! ### Infinite Family 2: Suleimanova's General Companion Theorem for All `n` -/

/-- Evaluates `c_0 + c_1 t + c_2 t^2 + ...` at `t ∈ ℤ`. -/
def evalLow : List Int → Int → Int
  | [], _ => 0
  | c :: cs, t => c + t * evalLow cs t

/-- Evaluates `∏_{m ∈ mus} (t + m)` at `t ∈ ℤ`. -/
def prodPlus : List Nat → Int → Int
  | [], _ => 1
  | m :: ms, t => (t + (m : Int)) * prodPlus ms t

/-- Sum of a list of natural numbers. -/
def natListSum : List Nat → Nat
  | [] => 0
  | m :: ms => m + natListSum ms

theorem zipWith_add_nonneg : ∀ (l1 l2 : List Int),
    (∀ x ∈ l1, 0 ≤ x) → (∀ y ∈ l2, 0 ≤ y) →
    ∀ z ∈ List.zipWith (· + ·) l1 l2, 0 ≤ z
  | [], _, _, _, _, hz => by cases hz
  | _ :: _, [], _, _, _, hz => by cases hz
  | a :: as, b :: bs, hl1, hl2, z, hz => by
      simp only [List.zipWith, List.mem_cons] at hz
      rcases hz with rfl | hztail
      · have ha := hl1 a (by simp)
        have hb := hl2 b (by simp)
        omega
      · exact zipWith_add_nonneg as bs
          (fun x hx => hl1 x (by simp [hx]))
          (fun y hy => hl2 y (by simp [hy])) z hztail

theorem evalLow_zipWith_add (t : Int) : ∀ (l1 l2 : List Int), l1.length = l2.length →
    evalLow (List.zipWith (· + ·) l1 l2) t = evalLow l1 t + evalLow l2 t
  | [], [], _ => by simp [evalLow]
  | [], _ :: _, hl => by cases hl
  | _ :: _, [], hl => by cases hl
  | a :: as, b :: bs, hl => by
      simp only [List.zipWith, evalLow]
      rw [evalLow_zipWith_add t as bs (Nat.succ.inj hl), Int.mul_add]
      omega

theorem evalLow_append_zero (t : Int) : ∀ (l : List Int),
    evalLow (l ++ [0]) t = evalLow l t
  | [] => by simp [evalLow]
  | a :: as => by simp [evalLow, evalLow_append_zero t as]

theorem evalLow_map_mul_append_one (t c : Int) : ∀ (l : List Int),
    evalLow ((l ++ [1]).map (fun x => c * x)) t =
    c * evalLow l t + c * (t ^ l.length)
  | [] => by simp [evalLow, Int.mul_one]
  | a :: as => by
      have ih := evalLow_map_mul_append_one t c as
      change c * a + t * evalLow ((as ++ [1]).map (fun x => c * x)) t =
             c * (a + t * evalLow as t) + c * (t ^ (as.length + 1))
      rw [ih, Int.mul_add, Int.mul_add, Int.pow_succ,
          ← Int.mul_assoc t c (evalLow as t), Int.mul_comm t c, Int.mul_assoc c t (evalLow as t),
          ← Int.mul_assoc t c (t ^ as.length), Int.mul_comm t c,
          Int.mul_assoc c t (t ^ as.length), Int.mul_comm t (t ^ as.length)]
      omega

theorem prodPlus_monic_nonneg (mus : List Nat) :
    ∃ qs : List Int,
      qs.length = mus.length ∧
      (∀ q ∈ qs, 0 ≤ q) ∧
      (∀ t : Int, prodPlus mus t = t ^ mus.length + evalLow qs t) := by
  induction mus with
  | nil =>
      refine ⟨[], rfl, ?_, ?_⟩
      · intro _ hq; cases hq
      · intro t; simp [prodPlus, evalLow]
  | cons m ms ih =>
      rcases ih with ⟨qs, hlen, hq_nonneg, heval⟩
      let shifted : List Int := 0 :: qs
      let scaled : List Int := (qs ++ [1]).map (fun x => (m : Int) * x)
      let qs' : List Int := List.zipWith (· + ·) shifted scaled
      have hlen' : qs'.length = (m :: ms).length := by
        simp [qs', shifted, scaled, hlen]
      have hnonneg' : ∀ q ∈ qs', 0 ≤ q := by
        apply zipWith_add_nonneg shifted scaled
        · intro x hx
          simp only [shifted, List.mem_cons] at hx
          rcases hx with rfl | hxq
          · omega
          · exact hq_nonneg x hxq
        · intro x hx
          simp only [scaled, List.mem_map, List.mem_append, List.mem_singleton] at hx
          rcases hx with ⟨y, hy, rfl⟩
          have hy0 : 0 ≤ y := by
            rcases hy with hyq | rfl
            · exact hq_nonneg y hyq
            · omega
          exact Int.mul_nonneg (by omega) hy0
      refine ⟨qs', hlen', hnonneg', ?_⟩
      intro t
      unfold prodPlus
      rw [heval t]
      dsimp [qs']
      rw [evalLow_zipWith_add t shifted scaled (by simp [shifted, scaled])]
      have hsh_eval : evalLow shifted t = t * evalLow qs t := by
        simp [shifted, evalLow]
      rw [hsh_eval, evalLow_map_mul_append_one t (m : Int) qs, hlen]
      simp only [List.length_cons, Int.pow_succ]
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (t ^ ms.length) t]
      omega

/-- **Suleimanova's General Nonnegative Companion Theorem (`∀ n`):**
    For any nonnegative integers `mus = [μ_2, ..., μ_n]` and `lam ≥ ∑ μ_k`,
    `(t - lam) * ∏ (t + μ_k) = t^n - ∑_{j=0}^{n-1} c_j t^j` with ALL `c_j ≥ 0`. -/
theorem suleimanova_nonneg_companion_poly (mus : List Nat) (lam : Nat)
    (hdom : natListSum mus ≤ lam) :
    ∃ cs : List Int,
      cs.length = mus.length + 1 ∧
      (∀ c ∈ cs, 0 ≤ c) ∧
      (∀ t : Int,
        (t - (lam : Int)) * prodPlus mus t = t ^ (mus.length + 1) - evalLow cs t) := by
  induction mus generalizing lam with
  | nil =>
      refine ⟨[(lam : Int)], rfl, ?_, ?_⟩
      · intro c hc; simp at hc; subst hc; omega
      · intro t; simp [prodPlus, evalLow, Int.pow_succ, Int.pow_zero]
  | cons m ms ih =>
      unfold natListSum at hdom
      have hdom' : natListSum ms ≤ lam - m := by omega
      rcases ih (lam - m) hdom' with ⟨cs', hlen', hcs'_nonneg, heval'⟩
      rcases prodPlus_monic_nonneg ms with ⟨qs, hqlen, hqs_nonneg, hqeval⟩
      let lm : Int := (lam : Int) * (m : Int)
      let term1 : List Int := 0 :: cs'
      let term2 : List Int := (qs ++ [1]).map (fun x => lm * x) ++ [0]
      let cs : List Int := List.zipWith (· + ·) term1 term2
      have hlen_cs : cs.length = (m :: ms).length + 1 := by
        simp [cs, term1, term2, hlen', hqlen]
      have hlm_nonneg : 0 ≤ lm := Int.mul_nonneg (by omega) (by omega)
      have hcs_nonneg : ∀ c ∈ cs, 0 ≤ c := by
        apply zipWith_add_nonneg term1 term2
        · intro x hx
          simp only [term1, List.mem_cons] at hx
          rcases hx with rfl | hxc
          · omega
          · exact hcs'_nonneg x hxc
        · intro x hx
          simp only [term2, List.mem_append, List.mem_map, List.mem_singleton] at hx
          rcases hx with ⟨y, hy, rfl⟩ | rfl
          · have hy0 : 0 ≤ y := by
              rcases hy with hyq | rfl
              · exact hqs_nonneg y hyq
              · omega
            exact Int.mul_nonneg hlm_nonneg hy0
          · omega
      refine ⟨cs, hlen_cs, hcs_nonneg, ?_⟩
      intro t
      dsimp [cs]
      rw [evalLow_zipWith_add t term1 term2 (by simp [term1, term2, hlen', hqlen])]
      have ht1_eval : evalLow term1 t = t * evalLow cs' t := by simp [term1, evalLow]
      have ht2_eval : evalLow term2 t = lm * prodPlus ms t := by
        dsimp [term2]
        rw [evalLow_append_zero t, evalLow_map_mul_append_one t lm qs, hqlen,
            hqeval t, Int.mul_add]
        omega
      rw [ht1_eval, ht2_eval]
      change (t - (lam : Int)) * ((t + (m : Int)) * prodPlus ms t) =
             t ^ (ms.length + 1 + 1) - (t * evalLow cs' t + lm * prodPlus ms t)
      have hlam_split : ((lam - m : Nat) : Int) = (lam : Int) - (m : Int) := by omega
      have hquad : (t - (lam : Int)) * (t + (m : Int)) =
          t * (t - ((lam - m : Nat) : Int)) - lm := by
        rw [hlam_split]
        dsimp [lm]
        rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_sub,
            Int.mul_comm (lam : Int) t]
        omega
      rw [← Int.mul_assoc (t - (lam : Int)) (t + (m : Int)) (prodPlus ms t),
          hquad, Int.sub_mul,
          Int.mul_assoc t (t - ((lam - m : Nat) : Int)) (prodPlus ms t),
          heval' t, Int.mul_sub]
      have hpow_step : t * (t ^ (ms.length + 1)) = t ^ (ms.length + 1 + 1) := by
        rw [Int.pow_succ t (ms.length + 1), Int.mul_comm t (t ^ (ms.length + 1))]
      rw [hpow_step]
      omega

/-! ## Section 5: Refutation of Reading II — Nonnegative Circulant Matrices -/

/-- General `3 × 3` circulant matrix `circ(c0, c1, c2)`. -/
def circulant3 (c0 c1 c2 : Int) : Mat 3 :=
  mkMat3 c0 c1 c2 c2 c0 c1 c1 c2 c0

/-- **Gauss Sum-of-Three-Squares Identity for `3 × 3` Circulant Characteristic Polynomials:**
    `2 * det(t I_3 - circ(c0, c1, c2)) = (t - (c0 + c1 + c2)) * ((t - c0 + c1)^2 + (t - c0 + c2)^2 + (c1 - c2)^2)`. -/
theorem circulant3_charPoly_sum_of_squares (c0 c1 c2 t : Int) :
    2 * charPoly3 (circulant3 c0 c1 c2) t =
    (t - (c0 + c1 + c2)) *
      ((t - c0 + c1) * (t - c0 + c1) +
       (t - c0 + c2) * (t - c0 + c2) +
       (c1 - c2) * (c1 - c2)) := by
  unfold charPoly3 circulant3 mkMat3
  dsimp [i3_0, i3_1, i3_2]
  let s := t - c0
  have hs : t - (c0 + c1 + c2) = s - c1 - c2 := by dsimp [s]; omega
  change 2 * (s * (s * s - -c1 * -c2) - -c1 * (-c2 * s - -c1 * -c1) +
              -c2 * (-c2 * -c2 - s * -c1)) =
         (t - (c0 + c1 + c2)) *
           ((s + c1) * (s + c1) + (s + c2) * (s + c2) + (c1 - c2) * (c1 - c2))
  rw [hs]
  have hlhs :
      s * (s * s - -c1 * -c2) - -c1 * (-c2 * s - -c1 * -c1) +
      -c2 * (-c2 * -c2 - s * -c1) =
      s * (s * s) - 3 * (c1 * c2 * s) - c1 * (c1 * c1) - c2 * (c2 * c2) := by
    have p1 : -c1 * -c2 = c1 * c2 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have p2 : -c1 * -c1 = c1 * c1 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have p3 : -c2 * -c2 = c2 * c2 := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have p4 : -c2 * s = -(c2 * s) := Int.neg_mul c2 s
    have p5 : s * -c1 = -(s * c1) := Int.mul_neg s c1
    rw [p1, p2, p3, p4, p5]
    have t1 : s * (s * s - c1 * c2) = s * (s * s) - c1 * c2 * s := by
      rw [Int.mul_sub, Int.mul_comm s (c1 * c2)]
    have t2 : -(-c1 * (-(c2 * s) - c1 * c1)) = -(c1 * c2 * s) - c1 * (c1 * c1) := by
      rw [Int.neg_mul c1, Int.neg_neg, Int.mul_sub, Int.mul_neg, Int.mul_assoc c1 c2 s]
    have t3 : -c2 * (c2 * c2 - -(s * c1)) = -(c2 * (c2 * c2)) - c1 * c2 * s := by
      rw [Int.neg_mul c2, Int.mul_sub, Int.mul_neg,
          ← Int.mul_assoc c2 s c1, Int.mul_comm c2 s, Int.mul_assoc s c2 c1,
          Int.mul_comm c2 c1, Int.mul_comm s (c1 * c2)]
      omega
    have hsub12 :
        s * (s * s - c1 * c2) - -c1 * (-(c2 * s) - c1 * c1) =
        s * (s * s - c1 * c2) + -(-c1 * (-(c2 * s) - c1 * c1)) := Int.sub_eq_add_neg
    rw [hsub12, t1, t2, t3]
    omega
  have hquad :
      (s + c1) * (s + c1) + (s + c2) * (s + c2) + (c1 - c2) * (c1 - c2) =
      2 * (s * s + (c1 + c2) * s + (c1 * c1 - c1 * c2 + c2 * c2)) := by
    have q1 : (s + c1) * (s + c1) = s * s + 2 * (c1 * s) + c1 * c1 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm s c1]
      omega
    have q2 : (s + c2) * (s + c2) = s * s + 2 * (c2 * s) + c2 * c2 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm s c2]
      omega
    have q3 : (c1 - c2) * (c1 - c2) = c1 * c1 - 2 * (c1 * c2) + c2 * c2 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm c2 c1]
      omega
    have q4 : (c1 + c2) * s = c1 * s + c2 * s := Int.add_mul c1 c2 s
    rw [q1, q2, q3, q4]
    omega
  rw [hlhs, hquad]
  have hrhs :
      (s - c1 - c2) * (2 * (s * s + (c1 + c2) * s + (c1 * c1 - c1 * c2 + c2 * c2))) =
      2 * ((s - (c1 + c2)) * (s * s + (c1 + c2) * s + (c1 * c1 - c1 * c2 + c2 * c2))) := by
    have hsub : s - c1 - c2 = s - (c1 + c2) := by omega
    rw [hsub, ← Int.mul_assoc, Int.mul_comm (s - (c1 + c2)) 2, Int.mul_assoc]
  rw [hrhs]
  let u := c1 + c2
  let v := c1 * c1 - c1 * c2 + c2 * c2
  have hcubic : (s - u) * (s * s + u * s + v) = s * (s * s) + (v - u * u) * s - u * v :=
    cubic_diff_helper s u v
  have hvu : v - u * u = -(3 * (c1 * c2)) := by
    dsimp [u, v]
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm c2 c1]
    omega
  have huv : u * v = c1 * (c1 * c1) + c2 * (c2 * c2) := by
    dsimp [u, v]
    rw [Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_add, Int.mul_sub]
    have b3 : c1 * (c1 * c2) = c1 * c1 * c2 := (Int.mul_assoc c1 c1 c2).symm
    have b4 : c2 * (c1 * c1) = c1 * c1 * c2 := Int.mul_comm c2 (c1 * c1)
    have b5 : c1 * (c2 * c2) = c1 * c2 * c2 := (Int.mul_assoc c1 c2 c2).symm
    have b6 : c2 * (c1 * c2) = c1 * c2 * c2 := by
      rw [← Int.mul_assoc, Int.mul_comm c2 c1]
    rw [b3, b4, b5, b6]
    omega
  change 2 * (s * (s * s) - 3 * (c1 * c2 * s) - c1 * (c1 * c1) - c2 * (c2 * c2)) =
         2 * ((s - u) * (s * s + u * s + v))
  rw [hcubic, hvu, huv]
  have hm3 : -(3 * (c1 * c2)) * s = -(3 * (c1 * c2 * s)) := by
    rw [Int.neg_mul, Int.mul_assoc]
  rw [hm3]
  omega

/-- Auxiliary lemma: any root `t` of `charPoly3 (circulant3 c0 c1 c2) t = 0` equals
    either `c0 + c1 + c2` or `c0 - c1`. -/
theorem circulant3_root_dichotomy (c0 c1 c2 t : Int)
    (ht : charPoly3 (circulant3 c0 c1 c2) t = 0) :
    t = c0 + c1 + c2 ∨ t = c0 - c1 := by
  have h2 := circulant3_charPoly_sum_of_squares c0 c1 c2 t
  rw [ht] at h2
  have hprod :
      (t - (c0 + c1 + c2)) *
        ((t - c0 + c1) * (t - c0 + c1) +
         (t - c0 + c2) * (t - c0 + c2) +
         (c1 - c2) * (c1 - c2)) = 0 := by omega
  rcases int_mul_eq_zero_iff hprod with hlin | hsq
  · left; omega
  · right
    have s1 := int_sq_nonneg (t - c0 + c1)
    have s2 := int_sq_nonneg (t - c0 + c2)
    have s3 := int_sq_nonneg (c1 - c2)
    have hz1 : (t - c0 + c1) * (t - c0 + c1) = 0 := by omega
    rcases int_mul_eq_zero_iff hz1 with h0 | h0 <;> omega

/-- **Universal `3 × 3` Real/Integer Circulant Obstruction Theorem:**
    No `3 × 3` integer circulant matrix (even allowing negative entries) can realize
    three pairwise distinct integer eigenvalues. -/
theorem no_circulant3_three_distinct_roots (c0 c1 c2 r1 r2 r3 : Int)
    (hpoly : ∀ t : Int, charPoly3 (circulant3 c0 c1 c2) t = (t - r1) * (t - r2) * (t - r3)) :
    r1 = r2 ∨ r2 = r3 ∨ r1 = r3 := by
  have hr1 : charPoly3 (circulant3 c0 c1 c2) r1 = 0 := by rw [hpoly r1]; omega
  have hr2 : charPoly3 (circulant3 c0 c1 c2) r2 = 0 := by rw [hpoly r2]; omega
  have hr3 : charPoly3 (circulant3 c0 c1 c2) r3 = 0 := by rw [hpoly r3]; omega
  rcases circulant3_root_dichotomy c0 c1 c2 r1 hr1 with h1a | h1b <;>
  rcases circulant3_root_dichotomy c0 c1 c2 r2 hr2 with h2a | h2b <;>
  rcases circulant3_root_dichotomy c0 c1 c2 r3 hr3 with h3a | h3b <;>
  omega

/-- **Counterexample 3 (`n = 3`, trace-zero, irreducible/primitive integer matrix):**
    `M_3 = [[0, 1, 0], [0, 0, 1], [6, 7, 0]]` realizes `(3, -1, -2)`, refuting BOTH
    the circulant reading AND the cyclic-root-of-unity / union-of-cyclic-lists reading! -/
def M3 : Mat 3 := mkMat3 0 1 0 0 0 1 6 7 0

theorem M3_refutes_circulant_and_cyclic :
    IsNonneg 3 M3 ∧ IsZeroDiag 3 M3 ∧ IsIrreducible3 M3 ∧
    Realizes3Int M3 3 (-1) (-2) ∧
    (¬ ∃ c0 c1 c2 : Int,
        ∀ t : Int, charPoly3 (circulant3 c0 c1 c2) t = (t - 3) * (t - -1) * (t - -2)) ∧
    (¬ CoveredByCyclicPieces intAbsMap [3, -1, -2]) := by
  have hnn : IsNonneg 3 M3 := mkMat3_nonneg
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨hnn, fin3_cases rfl rfl rfl, ?_, ⟨hnn, ?_⟩, ?_, ?_⟩
  · exact fin3_cases
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
  · intro t
    rw [charPoly3_expand, cubic_roots_expand]
    dsimp [M3, mkMat3, i3_0, i3_1, i3_2]
  · intro ⟨c0, c1, c2, hpoly⟩
    have hdup := no_circulant3_three_distinct_roots c0 c1 c2 3 (-1) (-2) hpoly
    omega
  · intro hcov
    have hmem : intAbsMap (-1) ∈ ([3, -1, -2] : List Int) :=
      abs_mem_of_coveredByCyclicPieces hcov (-1) (by simp)
    have habs : intAbsMap (-1) = 1 := rfl
    rw [habs] at hmem
    simp at hmem

/-- **Counterexample 4 (`n = 3`, symmetric, irreducible nonnegative matrix):**
    `S_3 = [[0, 2, 1], [2, 0, 1], [1, 1, 1]]` realizes `(3, 0, -2)`, showing even symmetric
    irreducible nonnegative matrices realize non-circulant, non-cyclic spectra. -/
def S3 : Mat 3 := mkMat3 0 2 1 2 0 1 1 1 1

theorem S3_symmetric_refutes_circulant_and_cyclic :
    IsNonneg 3 S3 ∧ IsSymmetric 3 S3 ∧ IsIrreducible3 S3 ∧
    Realizes3Int S3 3 0 (-2) ∧
    (¬ ∃ c0 c1 c2 : Int,
        ∀ t : Int, charPoly3 (circulant3 c0 c1 c2) t = (t - 3) * (t - 0) * (t - -2)) ∧
    (¬ CoveredByCyclicPieces intAbsMap [3, 0, -2]) := by
  have hnn : IsNonneg 3 S3 := mkMat3_nonneg
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨hnn, ?_, ?_, ⟨hnn, ?_⟩, ?_, ?_⟩
  · exact fin3_cases
      (fin3_cases rfl rfl rfl)
      (fin3_cases rfl rfl rfl)
      (fin3_cases rfl rfl rfl)
  · exact fin3_cases
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
      (fin3_cases (by decide) (by decide) (by decide))
  · intro t
    rw [charPoly3_expand, cubic_roots_expand]
    dsimp [S3, mkMat3, i3_0, i3_1, i3_2]
  · intro ⟨c0, c1, c2, hpoly⟩
    have hdup := no_circulant3_three_distinct_roots c0 c1 c2 3 0 (-2) hpoly
    omega
  · intro hcov
    have hmem : intAbsMap (-2) ∈ ([3, 0, -2] : List Int) :=
      abs_mem_of_coveredByCyclicPieces hcov (-2) (by simp)
    have habs : intAbsMap (-2) = 2 := rfl
    rw [habs] at hmem
    simp at hmem

/-! ## Section 6: Refutation of Reading III — Complex Phase Rotation & Lattice Operations -/

/-- Newton's power-sum identity for `2 × 2` Gaussian-integer spectra:
    if `A` realizes `(z1, z2)`, then `Re(z1^2 + z2^2) = tr(A^2)`. -/
theorem realizes2Gauss_sum_sq_eq_trace_sq (A : Mat 2) (z1 z2 : GaussInt)
    (hR : Realizes2Gauss A z1 z2) :
    (GaussInt.add (GaussInt.sq z1) (GaussInt.sq z2)).re = trace 2 (matMul 2 A A) := by
  rcases hR with ⟨_, hpoly⟩
  have h0 := congrArg GaussInt.re (hpoly GaussInt.zero)
  have h1 := congrArg GaussInt.re (hpoly GaussInt.one)
  have hm1 := congrArg GaussInt.re (hpoly (GaussInt.ofInt (-1)))
  have h0_im := congrArg GaussInt.im (hpoly GaussInt.zero)
  have h1_im := congrArg GaussInt.im (hpoly GaussInt.one)
  unfold charPoly2G det2 at h0 h1 hm1 h0_im h1_im
  dsimp [GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.sq,
    GaussInt.zero, GaussInt.one, GaussInt.ofInt] at h0 h1 hm1 h0_im h1_im
  let a00 := A i2_0 i2_0
  let a01 := A i2_0 i2_1
  let a10 := A i2_1 i2_0
  let a11 := A i2_1 i2_1
  have htr2 : trace 2 (matMul 2 A A) = a00 * a00 + 2 * (a01 * a10) + a11 * a11 := by
    unfold trace matMul finSum finSumAux
    change (0 + (0 + a00 * a00 + a01 * a10)) + (0 + a10 * a01 + a11 * a11) =
           a00 * a00 + 2 * (a01 * a10) + a11 * a11
    rw [Int.mul_comm a10 a01]
    omega
  rw [htr2]
  dsimp [GaussInt.add, GaussInt.sq, GaussInt.mul]
  -- Expand `(0 - x)(0 - y)`, `(1 - x)(1 - y)`, `(-1 - x)(-1 - y)` cleanly
  have e0 : (0 - z1.re) * (0 - z2.re) - (0 - z1.im) * (0 - z2.im) =
      z1.re * z2.re - z1.im * z2.im := by
    have p1 : (0 - z1.re) * (0 - z2.re) = z1.re * z2.re := by
      have : 0 - z1.re = -z1.re := by omega
      have : 0 - z2.re = -z2.re := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    have p2 : (0 - z1.im) * (0 - z2.im) = z1.im * z2.im := by
      have : 0 - z1.im = -z1.im := by omega
      have : 0 - z2.im = -z2.im := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    omega
  have e1 : (1 - z1.re) * (1 - z2.re) - (0 - z1.im) * (0 - z2.im) =
      1 - (z1.re + z2.re) + z1.re * z2.re - z1.im * z2.im := by
    rw [quad_roots_expand 1 z1.re z2.re]
    have p2 : (0 - z1.im) * (0 - z2.im) = z1.im * z2.im := by
      have : 0 - z1.im = -z1.im := by omega
      have : 0 - z2.im = -z2.im := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    omega
  have em1 : (-1 - z1.re) * (-1 - z2.re) - (0 - z1.im) * (0 - z2.im) =
      1 + (z1.re + z2.re) + z1.re * z2.re - z1.im * z2.im := by
    rw [quad_roots_expand (-1) z1.re z2.re]
    have p2 : (0 - z1.im) * (0 - z2.im) = z1.im * z2.im := by
      have : 0 - z1.im = -z1.im := by omega
      have : 0 - z2.im = -z2.im := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    omega
  have ei0 : (0 - z1.re) * (0 - z2.im) + (0 - z1.im) * (0 - z2.re) =
      z1.re * z2.im + z1.im * z2.re := by
    have p1 : (0 - z1.re) * (0 - z2.im) = z1.re * z2.im := by
      have : 0 - z1.re = -z1.re := by omega
      have : 0 - z2.im = -z2.im := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    have p2 : (0 - z1.im) * (0 - z2.re) = z1.im * z2.re := by
      have : 0 - z1.im = -z1.im := by omega
      have : 0 - z2.re = -z2.re := by omega
      simp_all [Int.neg_mul, Int.mul_neg]
    omega
  have ei1 : (1 - z1.re) * (0 - z2.im) + (0 - z1.im) * (1 - z2.re) =
      -(z1.im + z2.im) + z1.re * z2.im + z1.im * z2.re := by
    have p1 : (1 - z1.re) * (0 - z2.im) = -z2.im + z1.re * z2.im := by
      rw [Int.sub_mul, Int.one_mul]
      have : z1.re * (0 - z2.im) = -(z1.re * z2.im) := by
        have h : 0 - z2.im = -z2.im := by omega
        rw [h, Int.mul_neg]
      omega
    have p2 : (0 - z1.im) * (1 - z2.re) = -z1.im + z1.im * z2.re := by
      rw [Int.mul_sub, Int.mul_one]
      have : (0 - z1.im) * z2.re = -(z1.im * z2.re) := by
        have h : 0 - z1.im = -z1.im := by omega
        rw [h, Int.neg_mul]
      omega
    omega
  rw [e0] at h0
  rw [e1] at h1
  rw [em1] at hm1
  rw [ei0] at h0_im
  rw [ei1] at h1_im
  have hsum_re : z1.re + z2.re = a00 + a11 := by
    dsimp [a00, a11]; omega
  have hsum_im : z1.im + z2.im = 0 := by omega
  have hprod_re : z1.re * z2.re - z1.im * z2.im = a00 * a11 - a01 * a10 := by
    dsimp [a00, a01, a10, a11]; omega
  have halg :
      (z1.re * z1.re - z1.im * z1.im) + (z2.re * z2.re - z2.im * z2.im) =
      (z1.re + z2.re) * (z1.re + z2.re) - (z1.im + z2.im) * (z1.im + z2.im) -
      2 * (z1.re * z2.re - z1.im * z2.im) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add,
        Int.add_mul, Int.mul_add, Int.mul_add,
        Int.mul_comm z2.re z1.re, Int.mul_comm z2.im z1.im]
    omega
  rw [halg, hsum_re, hsum_im, hprod_re]
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm a11 a00]
  omega

/-- **Complex Phase Rotation Obstruction Theorem:**
    For every integer radius `r ≥ 1`, rotating the cyclic spectrum `(r, -r)` by `π/2`
    yields `(r i, -r i)`, which has `Re((r i)^2 + (-r i)^2) = -2 r^2 < 0` and is NOT
    realized by ANY nonnegative `2 × 2` matrix! -/
theorem no_nonneg2_realizes_rotated_cyclic (r : Int) (hr : 1 ≤ r) :
    let z1 : GaussInt := ⟨0, r⟩
    let z2 : GaussInt := ⟨0, -r⟩
    (GaussInt.add (GaussInt.sq z1) (GaussInt.sq z2)).re = -2 * (r * r) ∧
    ¬ ∃ A : Mat 2, Realizes2Gauss A z1 z2 := by
  dsimp
  have hsq : (GaussInt.add (GaussInt.sq ⟨0, r⟩) (GaussInt.sq ⟨0, -r⟩)).re = -2 * (r * r) := by
    dsimp [GaussInt.add, GaussInt.sq, GaussInt.mul]
    have hneg : (-r) * (-r) = r * r := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega
  refine ⟨hsq, ?_⟩
  intro ⟨A, hR⟩
  have htr_nonneg : 0 ≤ trace 2 (matMul 2 A A) := trace_sq_nonneg_of_nonneg 2 A hR.1
  have heq := realizes2Gauss_sum_sq_eq_trace_sq A ⟨0, r⟩ ⟨0, -r⟩ hR
  rw [hsq] at heq
  have hr2 : 1 ≤ r * r := by
    have := Int.mul_le_mul hr hr (by omega) (by omega)
    omega
  omega

/-- Special case `r = 1`: `P_2 ≥ 0` realizes `(1, -1)`, yet its `π/2` rotation `(i, -i)`
    is realized by NO nonnegative `2 × 2` matrix. -/
theorem P2_realizes_one_negOne_but_rotation_I_negI_unrealizable :
    Realizes2Gauss P2 GaussInt.one (GaussInt.neg GaussInt.one) ∧
    ¬ ∃ A : Mat 2, Realizes2Gauss A GaussInt.I GaussInt.negI := by
  refine ⟨⟨P2_positive_witness.1, ?_⟩, ?_⟩
  · intro z
    have hneg : GaussInt.sub z (GaussInt.neg GaussInt.one) = GaussInt.add z GaussInt.one := by
      apply GaussInt.ext <;> dsimp [GaussInt.sub, GaussInt.add, GaussInt.neg, GaussInt.one] <;> omega
    rw [hneg, GaussInt.sub_mul_add]
    apply GaussInt.ext <;>
    dsimp [charPoly2G, det2, P2, mkMat2, i2_0, i2_1,
      GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.sq, GaussInt.one, GaussInt.ofInt] <;>
    omega
  · exact (no_nonneg2_realizes_rotated_cyclic 1 (by omega)).2

/-! ### Coordinate Circular-Shift Invariance & Lattice Meet Obstruction -/

/-- Circular left shift `(x_1, x_2, ..., x_n) ↦ (x_2, ..., x_n, x_1)` on lists. -/
def rotList {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

/-- Evaluates `∏_{r ∈ L} (t - r)`. -/
def polyOfRoots : List Int → Int → Int
  | [], _ => 1
  | r :: rs, t => (t - r) * polyOfRoots rs t

theorem polyOfRoots_append (L1 L2 : List Int) (t : Int) :
    polyOfRoots (L1 ++ L2) t = polyOfRoots L1 t * polyOfRoots L2 t := by
  induction L1 with
  | nil => simp [polyOfRoots]
  | cons a as ih => simp [polyOfRoots, ih, Int.mul_assoc]

/-- Circular coordinate shifts leave the characteristic polynomial `∏ (t - λ_k)` invariant,
    hence generate NO new unordered spectra from cyclic lists. -/
theorem polyOfRoots_rotList_eq (L : List Int) (t : Int) :
    polyOfRoots (rotList L) t = polyOfRoots L t := by
  cases L with
  | nil => rfl
  | cons x xs => simp [rotList, polyOfRoots_append, polyOfRoots, Int.mul_comm]

/-- Componentwise meet `(min a1 b1, min a2 b2)` on ordered pairs. -/
def pairMeet (u v : Int × Int) : Int × Int :=
  (if u.1 ≤ v.1 then u.1 else v.1, if u.2 ≤ v.2 then u.2 else v.2)

/-- **Componentwise Lattice Meet Obstruction (`n = 2`):**
    Both `(1, -1)` and its circular shift `(-1, 1)` are realized by `P_2 ≥ 0`, yet their
    componentwise meet `(-1, -1)` has negative sum `-2 < 0` and is NOT nonnegative realizable! -/
theorem circular_shift_meet_unrealizable_dim2 :
    Realizes2Int P2 1 (-1) ∧
    Realizes2Int P2 (-1) 1 ∧
    pairMeet (1, -1) (-1, 1) = (-1, -1) ∧
    ¬ ∃ A : Mat 2, Realizes2Int A (-1) (-1) := by
  refine ⟨P2_positive_witness.2.2.2.2, ?_, rfl, ?_⟩
  · refine ⟨P2_positive_witness.1, ?_⟩
    intro t
    rw [P2_positive_witness.2.2.2.2.2 t, Int.mul_comm]
  · intro ⟨A, hA_nonneg, hpoly⟩
    have h0 := hpoly 0
    have h1 := hpoly 1
    rw [charPoly2_expand, quad_roots_expand] at h0 h1
    have ha00 : 0 ≤ A i2_0 i2_0 := hA_nonneg i2_0 i2_0
    have ha11 : 0 ≤ A i2_1 i2_1 := hA_nonneg i2_1 i2_1
    omega

/-- **Componentwise Lattice Meet Obstruction (`n = 3`):**
    All three circular shifts of `(2, -1, -1)` are realized by `K3Adj ≥ 0`, yet their
    componentwise meet `(-1, -1, -1)` has negative trace `-3 < 0` and is NOT
    nonnegative realizable! -/
theorem circular_shift_meet_unrealizable_dim3 :
    Realizes3Int K3Adj 2 (-1) (-1) ∧
    Realizes3Int K3Adj (-1) 2 (-1) ∧
    Realizes3Int K3Adj (-1) (-1) 2 ∧
    ¬ ∃ A : Mat 3, Realizes3Int A (-1) (-1) (-1) := by
  have hK := K3Adj_realizes_and_not_union_cyclic.2.2.2.2.1
  refine ⟨hK, ⟨hK.1, ?_⟩, ⟨hK.1, ?_⟩, ?_⟩
  · intro t; rw [hK.2 t]; rw [Int.mul_comm (t - 2) (t - -1)]
  · intro t; rw [hK.2 t]
    rw [Int.mul_comm (t - 2) (t - -1), Int.mul_assoc,
        Int.mul_comm (t - 2) (t - -1), ← Int.mul_assoc]
  · intro ⟨A, hA_nonneg, hpoly⟩
    have h0 := hpoly 0
    have h1 := hpoly 1
    have hm1 := hpoly (-1)
    rw [charPoly3_expand A 0, cubic_roots_expand 0 (-1) (-1) (-1)] at h0
    rw [charPoly3_expand A 1, cubic_roots_expand 1 (-1) (-1) (-1)] at h1
    rw [charPoly3_expand A (-1), cubic_roots_expand (-1) (-1) (-1) (-1)] at hm1
    dsimp at h0 h1 hm1
    have d0 : 0 ≤ A i3_0 i3_0 := hA_nonneg i3_0 i3_0
    have d1 : 0 ≤ A i3_1 i3_1 := hA_nonneg i3_1 i3_1
    have d2 : 0 ≤ A i3_2 i3_2 := hA_nonneg i3_2 i3_2
    omega

/-! ## Section 7: Combined Master Disproof Theorem -/

/-- **Master Disproof Summary (`conjecture_00000007161_completely_refuted`):**
    Simultaneously packages:
    1. Positive non-vacuity witness (`P_2` realizes cyclic `(1, -1)`),
    2. Trace-zero symmetric irreducible `{0,1}`-counterexample `K_3` realizing `(2, -1, -1)`
       (not covered by cyclic root-of-unity lists),
    3. Trace-zero irreducible counterexample `M_3` realizing `(3, -1, -2)`
       (neither circulant-realizable nor covered by cyclic root-of-unity lists),
    4. Complex phase-rotation failure (`(i, -i)` is realized by no nonnegative `2 × 2` matrix),
    5. Componentwise lattice-meet failure on circular shifts (`(-1, -1)` and `(-1, -1, -1)`
       are realized by no nonnegative matrices). -/
theorem conjecture_00000007161_completely_refuted :
    Realizes2Int P2 1 (-1) ∧
    (IsNonneg 3 K3Adj ∧ IsSymmetric 3 K3Adj ∧ IsZeroDiag 3 K3Adj ∧ IsIrreducible3 K3Adj ∧
      Realizes3Int K3Adj 2 (-1) (-1) ∧ ¬ CoveredByCyclicPieces intAbsMap [2, -1, -1]) ∧
    (IsNonneg 3 M3 ∧ IsZeroDiag 3 M3 ∧ IsIrreducible3 M3 ∧
      Realizes3Int M3 3 (-1) (-2) ∧
      (¬ ∃ c0 c1 c2 : Int,
          ∀ t : Int, charPoly3 (circulant3 c0 c1 c2) t = (t - 3) * (t - -1) * (t - -2)) ∧
      (¬ CoveredByCyclicPieces intAbsMap [3, -1, -2])) ∧
    (Realizes2Gauss P2 GaussInt.one (GaussInt.neg GaussInt.one) ∧
      ¬ ∃ A : Mat 2, Realizes2Gauss A GaussInt.I GaussInt.negI) ∧
    (pairMeet (1, -1) (-1, 1) = (-1, -1) ∧ ¬ ∃ A : Mat 2, Realizes2Int A (-1) (-1)) :=
  ⟨P2_positive_witness.2.2.2.2,
   K3Adj_realizes_and_not_union_cyclic,
   M3_refutes_circulant_and_cyclic,
   P2_realizes_one_negOne_but_rotation_I_negI_unrealizable,
   ⟨rfl, circular_shift_meet_unrealizable_dim2.2.2.2⟩⟩

end Conjecture00000007161
