import Init.Data.Int.Order
import Init.Data.Int.Lemmas
import Lean

namespace Conjecture00000007607

/-!
# Base Commutative Ring Typeclass & Reflective `comm_ring` Tactic

Defines `CommRing R`, proves soundness of sorted-monomial polynomial normalization (`Poly`),
and exports the `comm_ring` tactic for all downstream modules.
-/

class CommRing (R : Type) extends Add R, Sub R, Neg R, Mul R where
  zero : R
  one : R
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, zero + a = a
  add_zero : ∀ a : R, a + zero = a
  add_left_neg : ∀ a : R, -a + a = zero
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, one * a = a
  mul_one : ∀ a : R, a * one = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance (priority := 100) {R : Type} [CommRing R] : OfNat R 0 := ⟨CommRing.zero⟩
instance (priority := 100) {R : Type} [CommRing R] : OfNat R 1 := ⟨CommRing.one⟩

namespace CommRing

section Basic
variable {R : Type} [CommRing R]

theorem zero_def : (0 : R) = CommRing.zero := rfl
theorem one_def : (1 : R) = CommRing.one := rfl

theorem zero_add' (a : R) : 0 + a = a := zero_add a
theorem add_zero' (a : R) : a + 0 = a := add_zero a
theorem add_left_neg' (a : R) : -a + a = 0 := add_left_neg a
theorem one_mul' (a : R) : 1 * a = a := one_mul a
theorem mul_one' (a : R) : a * 1 = a := mul_one a

theorem add_right_neg (a : R) : a + -a = 0 := by
  rw [add_comm, add_left_neg']

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rw [← add_assoc, ← add_assoc, add_left_neg', zero_add', zero_add'] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

theorem zero_mul (a : R) : (0 : R) * a = 0 := by
  apply add_left_cancel (a := (0 : R) * a)
  rw [← right_distrib, zero_add', add_zero']

theorem mul_zero (a : R) : a * (0 : R) = 0 := by
  rw [mul_comm, zero_mul]

theorem neg_zero : -(0 : R) = 0 := by
  apply add_left_cancel (a := (0 : R))
  rw [add_right_neg, add_zero']

theorem neg_neg (a : R) : - -a = a := by
  apply add_left_cancel (a := -a)
  rw [add_right_neg, add_left_neg']

theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg]
  symm
  calc
    a + b + (-a + -b) = a + (b + (-b + -a)) := by
      rw [add_comm (-a) (-b), add_assoc]
    _ = a + (0 + -a) := by rw [← add_assoc b (-b) (-a), add_right_neg]
    _ = a + -a := by rw [zero_add']
    _ = 0 := add_right_neg a

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  apply add_left_cancel (a := a * b)
  rw [← right_distrib, add_right_neg, zero_mul]
  exact (add_right_neg (a * b)).symm

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

theorem sub_eq_zero_iff {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : a - b + b = (0 : R) + b := congrArg (fun x => x + b) h
    rw [sub_eq_add_neg, add_assoc, add_left_neg', add_zero', zero_add'] at h1
    exact h1
  · intro h
    rw [h, sub_self]

/-- Canonical integer scalar map `ℤ → R`. -/
def ofNatCast : Nat → R
  | 0 => 0
  | n + 1 => ofNatCast n + 1

def ofIntCast : Int → R
  | Int.ofNat n => ofNatCast n
  | Int.negSucc n => -ofNatCast (n + 1)

theorem ofNatCast_add (m n : Nat) :
    (ofNatCast (m + n) : R) = ofNatCast m + ofNatCast n := by
  induction n with
  | zero =>
    change ofNatCast m = ofNatCast m + 0
    rw [add_zero']
  | succ k ih =>
    change ofNatCast (m + k) + 1 = ofNatCast m + (ofNatCast k + 1)
    rw [ih, add_assoc]

theorem ofIntCast_subNatNat (m n : Nat) :
    (ofIntCast (Int.subNatNat m n) : R) = ofNatCast m + -ofNatCast n := by
  unfold Int.subNatNat
  cases h : n - m with
  | zero =>
    have hm : m = (m - n) + n := by omega
    change (ofNatCast (m - n) : R) = ofNatCast m + -ofNatCast n
    conv => rhs; rw [hm]
    rw [ofNatCast_add, add_assoc, add_right_neg, add_zero']
  | succ k =>
    have hn : n = m + (k + 1) := by omega
    change -(ofNatCast (k + 1) : R) = ofNatCast m + -ofNatCast n
    conv => rhs; rw [hn]
    rw [ofNatCast_add m (k + 1), neg_add, ← add_assoc, add_right_neg, zero_add']

theorem ofIntCast_zero : (ofIntCast 0 : R) = 0 := rfl

theorem ofIntCast_one : (ofIntCast 1 : R) = 1 := by
  change (0 : R) + 1 = 1
  exact zero_add' 1

theorem ofIntCast_neg (z : Int) : (ofIntCast (-z) : R) = -ofIntCast z := by
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      change (0 : R) = -0
      exact neg_zero.symm
    | succ k => rfl
  | negSucc k =>
    change ofNatCast (k + 1) = - -ofNatCast (k + 1)
    exact (neg_neg _).symm

theorem ofIntCast_add (x y : Int) :
    (ofIntCast (x + y) : R) = ofIntCast x + ofIntCast y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact ofNatCast_add m n
    | negSucc n => exact ofIntCast_subNatNat m (n + 1)
  | negSucc m =>
    cases y with
    | ofNat n =>
      change ofIntCast (Int.subNatNat n (m + 1)) = -ofNatCast (m + 1) + ofNatCast n
      rw [ofIntCast_subNatNat, add_comm]
    | negSucc n =>
      have h : Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := rfl
      have h2 : m + n + 1 + 1 = (m + 1) + (n + 1) := by omega
      rw [h]
      change -(ofNatCast (m + n + 1 + 1) : R) = -ofNatCast (m + 1) + -ofNatCast (n + 1)
      rw [h2, ofNatCast_add, neg_add]

theorem ofNatCast_mul (m n : Nat) :
    (ofNatCast (m * n) : R) = ofNatCast m * ofNatCast n := by
  induction n with
  | zero =>
    change (0 : R) = ofNatCast m * 0
    rw [mul_zero]
  | succ k ih =>
    have hmul : m * (k + 1) = m * k + m := Nat.mul_succ m k
    change ofNatCast (m * (k + 1)) = ofNatCast m * (ofNatCast k + 1)
    rw [hmul, ofNatCast_add, ih, left_distrib, mul_one']

theorem ofIntCast_mul (x y : Int) :
    (ofIntCast (x * y) : R) = ofIntCast x * ofIntCast y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact ofNatCast_mul m n
    | negSucc n =>
      have h : (Int.ofNat m) * (Int.negSucc n) = -Int.ofNat (m * (n + 1)) := rfl
      rw [h, ofIntCast_neg]
      change -(ofNatCast (m * (n + 1))) = ofNatCast m * (-ofNatCast (n + 1))
      rw [ofNatCast_mul, mul_neg]
  | negSucc m =>
    cases y with
    | ofNat n =>
      have h : (Int.negSucc m) * (Int.ofNat n) = -Int.ofNat ((m + 1) * n) := rfl
      rw [h, ofIntCast_neg]
      change -(ofNatCast ((m + 1) * n)) = (-ofNatCast (m + 1)) * ofNatCast n
      rw [ofNatCast_mul, neg_mul]
    | negSucc n =>
      have h : (Int.negSucc m) * (Int.negSucc n) = Int.ofNat ((m + 1) * (n + 1)) := rfl
      rw [h]
      change ofNatCast ((m + 1) * (n + 1)) = (-ofNatCast (m + 1)) * (-ofNatCast (n + 1))
      rw [ofNatCast_mul, neg_mul, mul_neg, neg_neg]

end Basic

/-! ## Reflective Multivariate Polynomial Normalizer -/

abbrev Monom := List Nat
abbrev Poly := List (Int × Monom)

inductive RingExpr where
  | zero
  | one
  | var (i : Nat)
  | add (a b : RingExpr)
  | sub (a b : RingExpr)
  | neg (a : RingExpr)
  | mul (a b : RingExpr)

def insertVar (v : Nat) : Monom → Monom
  | [] => [v]
  | w :: ws => if v ≤ w then v :: w :: ws else w :: insertVar v ws

def mulMonom : Monom → Monom → Monom
  | [], m2 => m2
  | v :: vs, m2 => insertVar v (mulMonom vs m2)

def cmpMonom : Monom → Monom → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | v :: vs, w :: ws =>
    if v < w then .lt
    else if w < v then .gt
    else cmpMonom vs ws

theorem eq_of_cmpMonom_eq : ∀ {m1 m2 : Monom}, cmpMonom m1 m2 = .eq → m1 = m2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | v :: vs, w :: ws, h => by
    unfold cmpMonom at h
    split at h
    · nomatch h
    · split at h
      · nomatch h
      · have hvw : v = w := by omega
        rw [hvw, eq_of_cmpMonom_eq h]

def addTerm (c : Int) (m : Monom) : Poly → Poly
  | [] => if c == 0 then [] else [(c, m)]
  | (c', m') :: rest =>
    match cmpMonom m m' with
    | .lt => if c == 0 then (c', m') :: rest else (c, m) :: (c', m') :: rest
    | .eq =>
      let s := c + c'
      if s == 0 then rest else (s, m') :: rest
    | .gt => (c', m') :: addTerm c m rest

def addPoly : Poly → Poly → Poly
  | [], p2 => p2
  | (c, m) :: rest, p2 => addTerm c m (addPoly rest p2)

def negPoly : Poly → Poly
  | [] => []
  | (c, m) :: rest => (-c, m) :: negPoly rest

def mulTermPoly (c : Int) (m : Monom) : Poly → Poly
  | [] => []
  | (c', m') :: rest => addTerm (c * c') (mulMonom m m') (mulTermPoly c m rest)

def mulPoly : Poly → Poly → Poly
  | [], _ => []
  | (c, m) :: rest, p2 => addPoly (mulTermPoly c m p2) (mulPoly rest p2)

def toPoly : RingExpr → Poly
  | .zero => []
  | .one => [(1, [])]
  | .var i => [(1, [i])]
  | .add a b => addPoly (toPoly a) (toPoly b)
  | .sub a b => addPoly (toPoly a) (negPoly (toPoly b))
  | .neg a => negPoly (toPoly a)
  | .mul a b => mulPoly (toPoly a) (toPoly b)

section Eval
variable {R : Type} [CommRing R]

def evalExpr (env : Nat → R) : RingExpr → R
  | .zero => 0
  | .one => 1
  | .var i => env i
  | .add a b => evalExpr env a + evalExpr env b
  | .sub a b => evalExpr env a - evalExpr env b
  | .neg a => -evalExpr env a
  | .mul a b => evalExpr env a * evalExpr env b

def evalMonom (env : Nat → R) : Monom → R
  | [] => 1
  | v :: vs => env v * evalMonom env vs

def evalPoly (env : Nat → R) : Poly → R
  | [] => 0
  | (c, m) :: rest => ofIntCast c * evalMonom env m + evalPoly env rest

theorem eval_insertVar (env : Nat → R) (v : Nat) (m : Monom) :
    evalMonom env (insertVar v m) = env v * evalMonom env m := by
  induction m with
  | nil => rfl
  | cons w ws ih =>
    unfold insertVar
    split
    · rfl
    · simp only [evalMonom, ih]
      rw [← mul_assoc, mul_comm (env w) (env v), mul_assoc]

theorem eval_mulMonom (env : Nat → R) (m1 m2 : Monom) :
    evalMonom env (mulMonom m1 m2) = evalMonom env m1 * evalMonom env m2 := by
  induction m1 with
  | nil =>
    simp only [mulMonom, evalMonom, one_mul']
  | cons v vs ih =>
    simp only [mulMonom, eval_insertVar, ih, evalMonom, mul_assoc]

theorem eval_addTerm (env : Nat → R) (c : Int) (m : Monom) (p : Poly) :
    evalPoly env (addTerm c m p) = ofIntCast c * evalMonom env m + evalPoly env p := by
  induction p with
  | nil =>
    unfold addTerm
    split
    · rename_i h
      have hc : c = 0 := beq_iff_eq.mp h
      rw [hc, ofIntCast_zero, zero_mul, evalPoly, zero_add']
    · simp only [evalPoly, add_zero']
  | cons hd rest ih =>
    obtain ⟨c', m'⟩ := hd
    unfold addTerm
    cases hcmp : cmpMonom m m' with
    | lt =>
      simp only []
      split
      · rename_i hz
        have hc : c = 0 := beq_iff_eq.mp hz
        rw [hc, ofIntCast_zero, zero_mul, zero_add']
      · simp only [evalPoly, add_assoc]
    | eq =>
      have hm : m = m' := eq_of_cmpMonom_eq hcmp
      subst hm
      simp only []
      split
      · rename_i hz
        have hs : c + c' = 0 := beq_iff_eq.mp hz
        have hcast : (ofIntCast c : R) + ofIntCast c' = 0 := by
          rw [← ofIntCast_add, hs, ofIntCast_zero]
        simp only [evalPoly]
        rw [← add_assoc, ← right_distrib, hcast, zero_mul, zero_add']
      · simp only [evalPoly]
        rw [ofIntCast_add, right_distrib, add_assoc]
    | gt =>
      simp only [evalPoly, ih]
      rw [← add_assoc, add_comm (ofIntCast c' * evalMonom env m') _, add_assoc]

theorem eval_addPoly (env : Nat → R) (p1 p2 : Poly) :
    evalPoly env (addPoly p1 p2) = evalPoly env p1 + evalPoly env p2 := by
  induction p1 with
  | nil => simp only [addPoly, evalPoly, zero_add']
  | cons hd rest ih =>
    obtain ⟨c, m⟩ := hd
    simp only [addPoly, eval_addTerm, ih, evalPoly, add_assoc]

theorem eval_negPoly (env : Nat → R) (p : Poly) :
    evalPoly env (negPoly p) = -evalPoly env p := by
  induction p with
  | nil =>
    simp only [negPoly, evalPoly]
    exact neg_zero.symm
  | cons hd rest ih =>
    obtain ⟨c, m⟩ := hd
    simp only [negPoly, evalPoly, ih, ofIntCast_neg, neg_mul, neg_add]

theorem eval_mulTermPoly (env : Nat → R) (c : Int) (m : Monom) (p : Poly) :
    evalPoly env (mulTermPoly c m p) = (ofIntCast c * evalMonom env m) * evalPoly env p := by
  induction p with
  | nil =>
    simp only [mulTermPoly, evalPoly, mul_zero]
  | cons hd rest ih =>
    obtain ⟨c', m'⟩ := hd
    simp only [mulTermPoly, eval_addTerm, ih, evalPoly, ofIntCast_mul, eval_mulMonom]
    rw [left_distrib]
    congr 1
    calc
      (ofIntCast c * ofIntCast c') * (evalMonom env m * evalMonom env m')
        = ofIntCast c * (ofIntCast c' * (evalMonom env m * evalMonom env m')) := by rw [mul_assoc]
      _ = ofIntCast c * (evalMonom env m * (ofIntCast c' * evalMonom env m')) := by
          rw [← mul_assoc (ofIntCast c'), mul_comm (ofIntCast c') (evalMonom env m), mul_assoc]
      _ = (ofIntCast c * evalMonom env m) * (ofIntCast c' * evalMonom env m') := by rw [← mul_assoc]

theorem eval_mulPoly (env : Nat → R) (p1 p2 : Poly) :
    evalPoly env (mulPoly p1 p2) = evalPoly env p1 * evalPoly env p2 := by
  induction p1 with
  | nil => simp only [mulPoly, evalPoly, zero_mul]
  | cons hd rest ih =>
    obtain ⟨c, m⟩ := hd
    simp only [mulPoly, eval_addPoly, eval_mulTermPoly, ih, evalPoly, right_distrib]

theorem eval_toPoly (env : Nat → R) (e : RingExpr) :
    evalPoly env (toPoly e) = evalExpr env e := by
  induction e with
  | zero => rfl
  | one =>
    simp only [toPoly, evalPoly, evalMonom, ofIntCast_one, mul_one', add_zero', evalExpr]
  | var i =>
    simp only [toPoly, evalPoly, evalMonom, ofIntCast_one, one_mul', mul_one', add_zero', evalExpr]
  | add a b iha ihb =>
    simp only [toPoly, eval_addPoly, iha, ihb, evalExpr]
  | sub a b iha ihb =>
    simp only [toPoly, eval_addPoly, eval_negPoly, iha, ihb, evalExpr, sub_eq_add_neg]
  | neg a iha =>
    simp only [toPoly, eval_negPoly, iha, evalExpr]
  | mul a b iha ihb =>
    simp only [toPoly, eval_mulPoly, iha, ihb, evalExpr]

theorem eq_of_toPoly_eq (env : Nat → R) (e1 e2 : RingExpr)
    (h : toPoly e1 = toPoly e2) : evalExpr env e1 = evalExpr env e2 := by
  rw [← eval_toPoly env e1, ← eval_toPoly env e2, h]

end Eval

/-! ## The `comm_ring` Tactic -/

section Tactic
open Lean Meta Elab Tactic

private partial def reifyRing (ringTy : Expr) (atoms : IO.Ref (Array Expr)) (e : Expr) :
    MetaM Expr := do
  let eClean := e.consumeMData
  if eClean.isAppOfArity ``HAdd.hAdd 6 then
    let a ← reifyRing ringTy atoms (eClean.getArg! 4)
    let b ← reifyRing ringTy atoms (eClean.getArg! 5)
    return mkApp2 (mkConst ``RingExpr.add) a b
  if eClean.isAppOfArity ``HSub.hSub 6 then
    let a ← reifyRing ringTy atoms (eClean.getArg! 4)
    let b ← reifyRing ringTy atoms (eClean.getArg! 5)
    return mkApp2 (mkConst ``RingExpr.sub) a b
  if eClean.isAppOfArity ``HMul.hMul 6 then
    let a ← reifyRing ringTy atoms (eClean.getArg! 4)
    let b ← reifyRing ringTy atoms (eClean.getArg! 5)
    return mkApp2 (mkConst ``RingExpr.mul) a b
  if eClean.isAppOfArity ``Neg.neg 3 then
    let a ← reifyRing ringTy atoms (eClean.getArg! 2)
    return mkApp (mkConst ``RingExpr.neg) a
  if eClean.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (eClean.getArg! 1).rawNatLit? then
      if n == 0 then
        return mkConst ``RingExpr.zero
      if n == 1 then
        return mkConst ``RingExpr.one
  let arr ← atoms.get
  let mut idx? : Option Nat := none
  for i in [:arr.size] do
    if ← isDefEq arr[i]! eClean then
      idx? := some i
      break
  match idx? with
  | some idx => return mkApp (mkConst ``RingExpr.var) (toExpr idx)
  | none =>
    let idx := arr.size
    atoms.set (arr.push eClean)
    return mkApp (mkConst ``RingExpr.var) (toExpr idx)

def lookupList {R : Type} (defaultVal : R) : List R → Nat → R
  | [], _ => defaultVal
  | x :: _, 0 => x
  | _ :: xs, n + 1 => lookupList defaultVal xs n

elab "comm_ring" : tactic => withMainContext do
  let goal ← getMainTarget
  let goal := (← instantiateMVars goal).consumeMData
  let some (ringTy, lhs, rhs) := goal.eq?
    | throwError "comm_ring: target is not an equality"
  let instTy ← mkAppM ``CommRing #[ringTy]
  let inst ← synthInstance instTy
  let atoms ← IO.mkRef (#[] : Array Expr)
  let e1 ← reifyRing ringTy atoms lhs
  let e2 ← reifyRing ringTy atoms rhs
  let atomArr ← atoms.get
  let zeroExpr ← mkAppOptM ``CommRing.zero #[ringTy, some inst]
  let mut listExpr ← mkAppOptM ``List.nil #[ringTy]
  for i in [:atomArr.size] do
    let elem := atomArr[atomArr.size - 1 - i]!
    listExpr ← mkAppOptM ``List.cons #[ringTy, some elem, some listExpr]
  let envExpr ← mkAppOptM ``lookupList #[ringTy, some zeroExpr, some listExpr]
  let p1 := mkApp (mkConst ``toPoly) e1
  let p2 := mkApp (mkConst ``toPoly) e2
  unless (← isDefEq p1 p2) do
    throwError "comm_ring: normalized polynomials are not definitionally equal"
  let rflProof ← mkEqRefl p1
  let proof ← mkAppOptM ``eq_of_toPoly_eq #[ringTy, inst, envExpr, e1, e2, rflProof]
  closeMainGoal `comm_ring proof

end Tactic

end CommRing

end Conjecture00000007607
