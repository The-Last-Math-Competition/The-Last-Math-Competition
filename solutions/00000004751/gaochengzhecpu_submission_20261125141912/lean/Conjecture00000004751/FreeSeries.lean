/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000004751:
 Module 2: Interval Partitions, Formal Power Series Composition, Free Moment–Cumulant
 Transform, Boxed Convolution, and Universal Polynomial Positivity Certificates.
-/

import Conjecture00000004751.Noncrossing

set_option maxRecDepth 200000

namespace Conjecture00000004751

/-! ### 1. Interval Partitions `Int(n)` and Exact Cardinality `2^(n-1)` -/

/-- Appends element `x` to the last block of a non-empty interval partition. -/
def appendToLastBlock (x : Nat) : Partition → Partition
  | [] => [[x]]
  | [b] => [b ++ [x]]
  | b :: rest => b :: appendToLastBlock x rest

/-- Generates all canonical interval partitions `Int(n)` of `{0, ..., n-1}`. -/
def allIntervalPartitions : Nat → List Partition
  | 0 => [[]]
  | 1 => [[[0]]]
  | n + 2 =>
      (allIntervalPartitions (n + 1)).foldr
        (fun pi acc => (pi ++ [[n + 1]]) :: appendToLastBlock (n + 1) pi :: acc) []

private theorem foldr_double_length {α β : Type} (f1 f2 : α → β) :
    ∀ (xs : List α) (init : List β),
      (xs.foldr (fun x acc => f1 x :: f2 x :: acc) init).length = 2 * xs.length + init.length
  | [], init => by simp
  | x :: xs, init => by
      simp [List.foldr, foldr_double_length f1 f2 xs init]
      omega

/-- Universal theorem: for every `n : Nat`, `|Int(n + 1)| = 2^n`. -/
theorem intervalPartitions_card (n : Nat) :
    (allIntervalPartitions (n + 1)).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [allIntervalPartitions]
      rw [foldr_double_length (fun pi => pi ++ [[k + 1]]) (appendToLastBlock (k + 1))
          (allIntervalPartitions (k + 1)) []]
      simp [ih, Nat.pow_succ]
      omega

/-! ### 2. Formal Power Series, Composition, and Free Moment–Cumulant Maps -/

/-- Formal power series `∑_{n ≥ 0} f(n) z^n` over `Int`. -/
abbrev FPS := Nat → Int

/-- Cauchy product of formal power series. -/
def fpsMul (f g : FPS) (n : Nat) : Int :=
  (List.range (n + 1)).foldl (fun s i => s + f i * g (n - i)) 0

/-- `k`-th Cauchy power `g^k` of a formal power series. -/
def fpsPow (g : FPS) : Nat → FPS
  | 0 => fun n => if n == 0 then 1 else 0
  | k + 1 => fpsMul (fpsPow g k) g

/-- Formal composition `(f ∘ g)(z)` for centered series (`g 0 = 0`). -/
def fpsComp (f g : FPS) (n : Nat) : Int :=
  if n == 0 then f 0
  else (List.range n).foldl (fun s j => s + f (j + 1) * fpsPow g (j + 1) n) 0

/-- Combinatorial interval-partition formula for `[z^n] (C_f ∘ C_g)(z)`. -/
def intervalCompCoeff (a b : Nat → Int) (n : Nat) : Int :=
  if n == 0 then 0
  else
    (allIntervalPartitions n).foldl
      (fun s pi =>
        s + a pi.length * pi.foldl (fun prod blk => prod * b blk.length) 1) 0

/-- Exact verification that `[z^n] (C_f ∘ C_g)(z)` equals the interval-partition sum
    for `n = 1..6` on algebraically independent prime-power test weights. -/
theorem fpsComp_eq_intervalComp_1_to_6 :
    let a : Nat → Int := fun k => if k == 0 then 0 else Int.ofNat (2 ^ k + k)
    let b : Nat → Int := fun m => if m == 0 then 0 else Int.ofNat (3 ^ m - m)
    (List.range 7).all (fun n => fpsComp a b n == intervalCompCoeff a b n) = true := by decide

/-- Free moments `m_n` from free cumulants `κ_k` via Nica–Speicher sum over `NC(n)`. -/
def freeMomentsFromCumulants (kap : Nat → Int) (n : Nat) : Int :=
  if n == 0 then 1
  else
    (allNC n).foldl
      (fun s pi => s + pi.foldl (fun prod blk => prod * kap blk.length) 1) 0

/-- Free cumulants `κ_n` from moments `m_k` via Möbius inversion on `NC(n)`. -/
def freeCumulantsFromMoments (m : Nat → Int) (n : Nat) : Int :=
  if n == 0 then 0
  else
    (allNC n).foldl
      (fun s pi =>
        s + mobiusToTopFormula n pi * pi.foldl (fun prod blk => prod * m blk.length) 1) 0

/-- Exact moment–cumulant Möbius inversion identity verified up to order 6. -/
theorem moment_cumulant_mobius_inversion_1_to_6 :
    let kap : Nat → Int := fun k =>
      match k with
      | 1 => 2 | 2 => -3 | 3 => 5 | 4 => -7 | 5 => 11 | 6 => -13 | _ => 0
    let m := freeMomentsFromCumulants kap
    (List.range 7).all (fun n =>
      if n == 0 then m 0 == 1 else freeCumulantsFromMoments m n == kap n) = true := by decide

/-- Nica–Speicher boxed convolution `(a ⋆ b)_n = ∑_{pi ∈ NC(n)} a_pi * b_{K(pi)}`. -/
def boxedConv (a b : Nat → Int) (n : Nat) : Int :=
  if n == 0 then 0
  else
    (allNC n).foldl
      (fun s pi =>
        let kp := kreweras n pi
        let wa := pi.foldl (fun prod blk => prod * a blk.length) 1
        let wb := kp.foldl (fun prod blk => prod * b blk.length) 1
        s + wa * wb) 0

/-! ### 3. Polynomial Quadratic Forms and Universal Rademacher Positivity -/

/-- Univariate polynomial over `Int`, represented as `[c_0, c_1, ..., c_d]`. -/
abbrev IntPoly := List Int

/-- Evaluates `p(x)` via Horner's rule. -/
def polyEval : IntPoly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * polyEval cs x

/-- Scalar multiplication of a polynomial. -/
def polyScale (a : Int) : IntPoly → IntPoly
  | [] => []
  | c :: cs => (a * c) :: polyScale a cs

/-- Addition of two polynomials. -/
def polyAdd : IntPoly → IntPoly → IntPoly
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => (c + d) :: polyAdd cs ds

/-- Multiplication of two polynomials in `ℤ[x]`. -/
def polyMul : IntPoly → IntPoly → IntPoly
  | [], _ => []
  | c :: cs, q => polyAdd (polyScale c q) (0 :: polyMul cs q)

/-- Formal square `p(x)^2` in `ℤ[x]`. -/
def polySq (p : IntPoly) : IntPoly := polyMul p p

/-- Linear moment functional `⟨m, p⟩ = ∑_{i ≥ 0} p_i m_i` via tail-indexed recursion. -/
def momentEvalAux (m : Nat → Int) : Nat → IntPoly → Int
  | _, [] => 0
  | idx, c :: cs => c * m idx + momentEvalAux m (idx + 1) cs

def momentEval (m : Nat → Int) (p : IntPoly) : Int :=
  momentEvalAux m 0 p

theorem polyEval_scale (a : Int) (q : IntPoly) (x : Int) :
    polyEval (polyScale a q) x = a * polyEval q x := by
  induction q with
  | nil => simp [polyScale, polyEval]
  | cons d ds ih =>
      simp only [polyScale, polyEval, ih]
      rw [Int.mul_add, ← Int.mul_assoc a x (polyEval ds x), Int.mul_comm a x, Int.mul_assoc]

theorem polyEval_add (p q : IntPoly) (x : Int) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil => simp [polyAdd, polyEval]
  | cons c cs ih =>
      cases q with
      | nil => simp [polyAdd, polyEval]
      | cons d ds =>
          simp only [polyAdd, polyEval, ih ds]
          rw [Int.mul_add]
          omega

theorem polyEval_mul (p q : IntPoly) (x : Int) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil => simp [polyMul, polyEval]
  | cons c cs ih =>
      simp only [polyMul, polyEval, polyEval_add, polyEval_scale, ih]
      rw [Int.add_mul, Int.zero_add, Int.mul_assoc]

theorem polyEval_sq (p : IntPoly) (x : Int) :
    polyEval (polySq p) x = polyEval p x * polyEval p x :=
  polyEval_mul p p x

/-- Symmetric Rademacher probability measure `μ = (δ_{-1} + δ_1)/2` moment sequence:
    `m_{2r} = 1` and `m_{2r+1} = 0`. -/
def rademacherMoments (n : Nat) : Int :=
  if n % 2 == 0 then 1 else 0

private theorem rademacher_aux (p : IntPoly) (idx : Nat) :
    2 * momentEvalAux rademacherMoments idx p =
      (if idx % 2 == 0 then 1 else 1) * polyEval p 1 +
      (if idx % 2 == 0 then 1 else -1) * polyEval p (-1) := by
  induction p generalizing idx with
  | nil => simp [momentEvalAux, polyEval]
  | cons c cs ih =>
      simp only [momentEvalAux, polyEval]
      rw [Int.mul_add, ih (idx + 1)]
      have hpar : (idx + 1) % 2 = (1 - idx % 2) := by omega
      by_cases he : idx % 2 = 0
      · have ho : (idx + 1) % 2 = 1 := by omega
        simp [rademacherMoments, he, ho]
        omega
      · have h1 : idx % 2 = 1 := by omega
        have he2 : (idx + 1) % 2 = 0 := by omega
        simp [rademacherMoments, h1, he2]
        omega

/-- Exact expectation identity for every polynomial `p ∈ ℤ[x]` under Rademacher moments:
    `2 ⟨m_μ, p⟩ = p(1) + p(-1)`. -/
theorem momentEval_rademacher (p : IntPoly) :
    2 * momentEval rademacherMoments p = polyEval p 1 + polyEval p (-1) := by
  unfold momentEval
  have h := rademacher_aux p 0
  simpa using h

private theorem int_mul_self_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hprod : (-z) * (-z) = z * z := by
      rw [Int.neg_mul_neg]
    rw [← hprod]
    exact Int.mul_nonneg hneg hneg

/-- Constructive universal positivity certificate: `rademacherMoments` is a bona fide positive
    moment sequence (`0 ≤ 2 ⟨m_μ, p(x)^2⟩` for ALL polynomials `p ∈ ℤ[x]`). -/
theorem rademacher_universal_positivity (p : IntPoly) :
    0 ≤ 2 * momentEval rademacherMoments (polySq p) := by
  rw [momentEval_rademacher, polyEval_sq, polyEval_sq]
  exact Int.add_nonneg (int_mul_self_nonneg (polyEval p 1)) (int_mul_self_nonneg (polyEval p (-1)))

end Conjecture00000004751
