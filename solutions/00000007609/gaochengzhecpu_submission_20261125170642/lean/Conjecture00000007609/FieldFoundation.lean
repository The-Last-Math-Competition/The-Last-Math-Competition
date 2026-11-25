/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Algebraic foundation for Conjecture 00000007609:
  1. CommRingOps and pure-Bool reflective multivariate polynomial normalizer (`RExpr`),
  2. FormallyRealField F (satisfied by ℝ and ℚ),
  3. Constructive rational instance `QField` witnessing non-vacuity in Core Lean 4,
     including proof that `2` has no rational square root (`∀ x : QField, x * x ≠ twoF QField`).
-/

namespace Conjecture00000007609

class HasZero (R : Type) where
  zero : R

class HasOne (R : Type) where
  one : R

instance (priority := 100) [HasZero R] : OfNat R 0 where
  ofNat := HasZero.zero

instance (priority := 100) [HasOne R] : OfNat R 1 where
  ofNat := HasOne.one

/-- A commutative ring carrier for reflective polynomial normalization. -/
class CommRingOps (R : Type) extends Add R, Sub R, Mul R, Neg R, HasZero R, HasOne R where
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, (-a) + a = 0
  sub_eq_add_neg : ∀ a b : R, a - b = a + (-b)
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

section CommRingLemmas

variable {R : Type} [CommRingOps R]

theorem cr_add_zero (a : R) : a + 0 = a := by
  rw [CommRingOps.add_comm, CommRingOps.zero_add]

theorem cr_add_neg_cancel (a : R) : a + (-a) = 0 := by
  rw [CommRingOps.add_comm, CommRingOps.neg_add_cancel]

theorem cr_mul_one (a : R) : a * 1 = a := by
  rw [CommRingOps.mul_comm, CommRingOps.one_mul]

theorem cr_right_distrib (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [CommRingOps.mul_comm, CommRingOps.left_distrib,
      CommRingOps.mul_comm a c, CommRingOps.mul_comm b c]

theorem cr_add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← CommRingOps.add_assoc, ← CommRingOps.add_assoc,
      CommRingOps.neg_add_cancel, CommRingOps.zero_add,
      CommRingOps.zero_add] at h1
  exact h1

theorem cr_mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← CommRingOps.left_distrib, cr_add_zero, cr_add_zero]
  exact cr_add_left_cancel h

theorem cr_zero_mul (a : R) : 0 * a = 0 := by
  rw [CommRingOps.mul_comm, cr_mul_zero]

theorem cr_neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply cr_add_left_cancel (a := a)
  rw [cr_add_neg_cancel, h]

theorem cr_neg_zero : -(0 : R) = 0 :=
  cr_neg_eq_of_add_eq_zero (cr_add_zero 0)

theorem cr_neg_neg (a : R) : -(-a) = a :=
  cr_neg_eq_of_add_eq_zero (CommRingOps.neg_add_cancel a)

theorem cr_neg_add_distrib (a b : R) : -(a + b) = (-a) + (-b) := by
  apply cr_neg_eq_of_add_eq_zero
  calc
    (a + b) + ((-a) + (-b))
        = a + (b + ((-b) + (-a))) := by
          rw [CommRingOps.add_comm (-a) (-b), CommRingOps.add_assoc]
    _ = a + ((b + (-b)) + (-a)) := by rw [CommRingOps.add_assoc b (-b) (-a)]
    _ = a + (0 + (-a)) := by rw [cr_add_neg_cancel]
    _ = a + (-a) := by rw [CommRingOps.zero_add]
    _ = 0 := cr_add_neg_cancel a

theorem cr_mul_neg (a b : R) : a * (-b) = -(a * b) := by
  apply Eq.symm
  apply cr_neg_eq_of_add_eq_zero
  rw [← CommRingOps.left_distrib, cr_add_neg_cancel, cr_mul_zero]

theorem cr_neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [CommRingOps.mul_comm, cr_mul_neg, CommRingOps.mul_comm]

theorem cr_sub_self (a : R) : a - a = 0 := by
  rw [CommRingOps.sub_eq_add_neg, cr_add_neg_cancel]

theorem cr_eq_of_sub_eq_zero {a b : R} (h : a - b = 0) : a = b := by
  apply cr_add_left_cancel (a := -b)
  calc
    (-b) + a = a + (-b) := CommRingOps.add_comm _ _
    _ = a - b := (CommRingOps.sub_eq_add_neg a b).symm
    _ = 0 := h
    _ = (-b) + b := (CommRingOps.neg_add_cancel b).symm

theorem cr_add_left_comm (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← CommRingOps.add_assoc, CommRingOps.add_comm a b, CommRingOps.add_assoc]

theorem cr_mul_left_comm (a b c : R) : a * (b * c) = b * (a * c) := by
  rw [← CommRingOps.mul_assoc, CommRingOps.mul_comm a b, CommRingOps.mul_assoc]

def crOfNat (R : Type) [CommRingOps R] : Nat → R
  | 0 => 0
  | n + 1 => crOfNat R n + 1

def crOfInt (R : Type) [CommRingOps R] : Int → R
  | Int.ofNat n => crOfNat R n
  | Int.negSucc n => -(crOfNat R (n + 1))

theorem crOfNat_add (m n : Nat) : crOfNat R (m + n) = crOfNat R m + crOfNat R n := by
  induction n with
  | zero =>
    change crOfNat R m = crOfNat R m + 0
    rw [cr_add_zero]
  | succ n ih =>
    rw [Nat.add_succ, crOfNat, crOfNat, ih, CommRingOps.add_assoc]

theorem crOfInt_subNatNat (m n : Nat) :
    crOfInt R (Int.subNatNat m n) = crOfNat R m + -(crOfNat R n) := by
  unfold Int.subNatNat
  generalize hd : n - m = d
  cases d with
  | zero =>
    have hle : n ≤ m := Nat.le_of_sub_eq_zero hd
    have hm : m = (m - n) + n := (Nat.sub_add_cancel hle).symm
    change crOfNat R (m - n) = crOfNat R m + -(crOfNat R n)
    conv => rhs; rw [hm, crOfNat_add, CommRingOps.add_assoc, cr_add_neg_cancel, cr_add_zero]
  | succ k =>
    have hlt : m < n := Nat.lt_of_sub_eq_succ hd
    have hn : n = m + (k + 1) := by omega
    change -(crOfNat R (k + 1)) = crOfNat R m + -(crOfNat R n)
    conv => rhs; rw [hn, crOfNat_add, cr_neg_add_distrib, ← CommRingOps.add_assoc,
        cr_add_neg_cancel, CommRingOps.zero_add]

theorem crOfInt_neg (z : Int) : crOfInt R (-z) = -(crOfInt R z) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      change (0 : R) = -(0 : R)
      exact cr_neg_zero.symm
    | succ _ => rfl
  | negSucc k =>
    change crOfNat R (k + 1) = -(-(crOfNat R (k + 1)))
    rw [cr_neg_neg]

theorem crOfInt_add (x y : Int) : crOfInt R (x + y) = crOfInt R x + crOfInt R y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact crOfNat_add m n
    | negSucc n => exact crOfInt_subNatNat m (n + 1)
  | negSucc m =>
    cases y with
    | ofNat n =>
      change crOfInt R (Int.subNatNat n (m + 1)) = -(crOfNat R (m + 1)) + crOfNat R n
      rw [crOfInt_subNatNat, CommRingOps.add_comm]
    | negSucc n =>
      change -(crOfNat R (Nat.succ (m + n) + 1)) = -(crOfNat R (m + 1)) + -(crOfNat R (n + 1))
      have hmn : Nat.succ (m + n) + 1 = (m + 1) + (n + 1) := by omega
      rw [hmn, crOfNat_add, cr_neg_add_distrib]

theorem crOfNat_mul (m n : Nat) : crOfNat R (m * n) = crOfNat R m * crOfNat R n := by
  induction n with
  | zero =>
    change (0 : R) = crOfNat R m * 0
    rw [cr_mul_zero]
  | succ n ih =>
    rw [Nat.mul_succ, crOfNat_add, ih, crOfNat, CommRingOps.left_distrib, cr_mul_one]

theorem crOfInt_mul (x y : Int) : crOfInt R (x * y) = crOfInt R x * crOfInt R y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n => exact crOfNat_mul m n
    | negSucc n =>
      change crOfInt R (-(Int.ofNat (m * (n + 1)))) = crOfNat R m * -(crOfNat R (n + 1))
      rw [crOfInt_neg]
      change -(crOfNat R (m * (n + 1))) = crOfNat R m * -(crOfNat R (n + 1))
      rw [crOfNat_mul, cr_mul_neg]
  | negSucc m =>
    cases y with
    | ofNat n =>
      change crOfInt R (-(Int.ofNat ((m + 1) * n))) = -(crOfNat R (m + 1)) * crOfNat R n
      rw [crOfInt_neg]
      change -(crOfNat R ((m + 1) * n)) = -(crOfNat R (m + 1)) * crOfNat R n
      rw [crOfNat_mul, cr_neg_mul]
    | negSucc n =>
      change crOfNat R ((m + 1) * (n + 1)) = -(crOfNat R (m + 1)) * -(crOfNat R (n + 1))
      rw [crOfNat_mul, cr_neg_mul, cr_mul_neg, cr_neg_neg]

/-! ### Fast Pure-`Bool` Reflective Multivariate Polynomial Normalizer (`RPoly`) -/

inductive RExpr where
  | zero : RExpr
  | one : RExpr
  | var : Nat → RExpr
  | neg : RExpr → RExpr
  | add : RExpr → RExpr → RExpr
  | sub : RExpr → RExpr → RExpr
  | mul : RExpr → RExpr → RExpr

def RExpr.eval (env : Nat → R) : RExpr → R
  | .zero => 0
  | .one => 1
  | .var i => env i
  | .neg e => -(e.eval env)
  | .add e₁ e₂ => e₁.eval env + e₂.eval env
  | .sub e₁ e₂ => e₁.eval env - e₂.eval env
  | .mul e₁ e₂ => e₁.eval env * e₂.eval env

def natCmp : Nat → Nat → Ordering
  | 0, 0 => .eq
  | 0, _ + 1 => .lt
  | _ + 1, 0 => .gt
  | m + 1, n + 1 => natCmp m n

def monoCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | i :: is, j :: js =>
    match natCmp i j with
    | .lt => .lt
    | .gt => .gt
    | .eq => monoCmp is js

theorem natCmp_eq_iff (m n : Nat) : natCmp m n = .eq ↔ m = n := by
  induction m generalizing n with
  | zero => cases n <;> simp [natCmp]
  | succ m ih =>
    cases n with
    | zero => simp [natCmp]
    | succ n => simp [natCmp, ih]

theorem monoCmp_eq_iff (xs ys : List Nat) : monoCmp xs ys = .eq ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [monoCmp]
  | cons x xs ih =>
    cases ys with
    | nil => simp [monoCmp]
    | cons y ys =>
      unfold monoCmp
      cases hxy : natCmp x y with
      | lt =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨rfl, _⟩
        rw [(natCmp_eq_iff x x).mpr rfl] at hxy
        contradiction
      | gt =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨rfl, _⟩
        rw [(natCmp_eq_iff x x).mpr rfl] at hxy
        contradiction
      | eq =>
        have heq : x = y := (natCmp_eq_iff x y).mp hxy
        subst heq
        simp [ih]

def intIsZero : Int → Bool
  | Int.ofNat 0 => true
  | _ => false

theorem intIsZero_eq_true_iff (z : Int) : intIsZero z = true ↔ z = 0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => simp [intIsZero]
    | succ k =>
      change false = true ↔ Int.ofNat (k + 1) = Int.ofNat 0
      constructor
      · intro h; nomatch h
      · intro h; nomatch h
  | negSucc _ => simp [intIsZero]

def insertVar (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js =>
    match natCmp i j with
    | .gt => j :: insertVar i js
    | _ => i :: j :: js

def mergeVars : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => insertVar x (mergeVars xs ys)

abbrev RPoly := List (Int × List Nat)

def evalVars (env : Nat → R) : List Nat → R
  | [] => 1
  | i :: is => env i * evalVars env is

def evalPoly (env : Nat → R) : RPoly → R
  | [] => 0
  | (c, vs) :: rest => crOfInt R c * evalVars env vs + evalPoly env rest

theorem evalVars_insertVar (env : Nat → R) (i : Nat) (vs : List Nat) :
    evalVars env (insertVar i vs) = env i * evalVars env vs := by
  induction vs with
  | nil => rfl
  | cons j js ih =>
    unfold insertVar
    cases natCmp i j with
    | lt => rfl
    | eq => rfl
    | gt => simp only [evalVars, ih, cr_mul_left_comm]

theorem evalVars_mergeVars (env : Nat → R) (xs ys : List Nat) :
    evalVars env (mergeVars xs ys) = evalVars env xs * evalVars env ys := by
  induction xs with
  | nil =>
    change evalVars env ys = 1 * evalVars env ys
    exact (CommRingOps.one_mul _).symm
  | cons x xs ih =>
    simp only [mergeVars, evalVars, evalVars_insertVar, ih, CommRingOps.mul_assoc]

def addTermAux (c : Int) (vs : List Nat) : RPoly → RPoly
  | [] => [(c, vs)]
  | (c', vs') :: rest =>
    match monoCmp vs vs' with
    | .eq =>
      let s := c + c'
      match intIsZero s with
      | true => rest
      | false => (s, vs') :: rest
    | .lt => (c, vs) :: (c', vs') :: rest
    | .gt => (c', vs') :: addTermAux c vs rest

def addTerm (c : Int) (vs : List Nat) (p : RPoly) : RPoly :=
  match intIsZero c with
  | true => p
  | false => addTermAux c vs p

theorem evalPoly_addTermAux (env : Nat → R) (c : Int) (vs : List Nat) (p : RPoly) :
    evalPoly env (addTermAux c vs p) = crOfInt R c * evalVars env vs + evalPoly env p := by
  induction p with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨c', vs'⟩ := hd
    unfold addTermAux
    cases hcmp : monoCmp vs vs' with
    | eq =>
      have hvseq : vs = vs' := (monoCmp_eq_iff vs vs').mp hcmp
      subst hvseq
      dsimp only
      cases hz : intIsZero (c + c') with
      | true =>
        have hseq : c + c' = 0 := (intIsZero_eq_true_iff _).mp hz
        dsimp only [evalPoly]
        rw [← CommRingOps.add_assoc, ← cr_right_distrib, ← crOfInt_add, hseq]
        change evalPoly env rest = 0 * evalVars env vs + evalPoly env rest
        rw [cr_zero_mul, CommRingOps.zero_add]
      | false =>
        dsimp only [evalPoly]
        rw [crOfInt_add, cr_right_distrib, CommRingOps.add_assoc]
    | lt => rfl
    | gt =>
      dsimp only [evalPoly]
      rw [ih, cr_add_left_comm]

theorem evalPoly_addTerm (env : Nat → R) (c : Int) (vs : List Nat) (p : RPoly) :
    evalPoly env (addTerm c vs p) = crOfInt R c * evalVars env vs + evalPoly env p := by
  unfold addTerm
  cases hz : intIsZero c with
  | true =>
    have hc0 : c = 0 := (intIsZero_eq_true_iff c).mp hz
    subst hc0
    change evalPoly env p = 0 * evalVars env vs + evalPoly env p
    rw [cr_zero_mul, CommRingOps.zero_add]
  | false => exact evalPoly_addTermAux env c vs p

def addPoly : RPoly → RPoly → RPoly
  | [], q => q
  | (c, vs) :: rest, q => addTerm c vs (addPoly rest q)

theorem evalPoly_addPoly (env : Nat → R) (p q : RPoly) :
    evalPoly env (addPoly p q) = evalPoly env p + evalPoly env q := by
  induction p with
  | nil =>
    change evalPoly env q = 0 + evalPoly env q
    exact (CommRingOps.zero_add _).symm
  | cons hd rest ih =>
    obtain ⟨c, vs⟩ := hd
    simp only [addPoly, evalPoly, evalPoly_addTerm, ih, CommRingOps.add_assoc]

def negPoly : RPoly → RPoly
  | [] => []
  | (c, vs) :: rest => (-c, vs) :: negPoly rest

theorem evalPoly_negPoly (env : Nat → R) (p : RPoly) :
    evalPoly env (negPoly p) = -(evalPoly env p) := by
  induction p with
  | nil =>
    change (0 : R) = -(0 : R)
    exact cr_neg_zero.symm
  | cons hd rest ih =>
    obtain ⟨c, vs⟩ := hd
    simp only [negPoly, evalPoly, ih, crOfInt_neg, cr_neg_mul, cr_neg_add_distrib]

def mulTermPoly (c : Int) (vs : List Nat) : RPoly → RPoly
  | [] => []
  | (c', vs') :: rest => addTerm (c * c') (mergeVars vs vs') (mulTermPoly c vs rest)

theorem evalPoly_mulTermPoly (env : Nat → R) (c : Int) (vs : List Nat) (p : RPoly) :
    evalPoly env (mulTermPoly c vs p) =
      (crOfInt R c * evalVars env vs) * evalPoly env p := by
  induction p with
  | nil =>
    change (0 : R) = (crOfInt R c * evalVars env vs) * 0
    exact (cr_mul_zero _).symm
  | cons hd rest ih =>
    obtain ⟨c', vs'⟩ := hd
    simp only [mulTermPoly, evalPoly, evalPoly_addTerm, ih,
      CommRingOps.left_distrib, crOfInt_mul, evalVars_mergeVars]
    congr 1
    calc
      (crOfInt R c * crOfInt R c') * (evalVars env vs * evalVars env vs')
          = crOfInt R c * (crOfInt R c' * (evalVars env vs * evalVars env vs')) :=
            CommRingOps.mul_assoc _ _ _
      _ = crOfInt R c * (evalVars env vs * (crOfInt R c' * evalVars env vs')) := by
            rw [cr_mul_left_comm (crOfInt R c') (evalVars env vs)]
      _ = (crOfInt R c * evalVars env vs) * (crOfInt R c' * evalVars env vs') :=
            (CommRingOps.mul_assoc _ _ _).symm

def mulPoly : RPoly → RPoly → RPoly
  | [], _ => []
  | (c, vs) :: rest, q => addPoly (mulTermPoly c vs q) (mulPoly rest q)

theorem evalPoly_mulPoly (env : Nat → R) (p q : RPoly) :
    evalPoly env (mulPoly p q) = evalPoly env p * evalPoly env q := by
  induction p with
  | nil =>
    change (0 : R) = 0 * evalPoly env q
    exact (cr_zero_mul _).symm
  | cons hd rest ih =>
    obtain ⟨c, vs⟩ := hd
    simp only [mulPoly, evalPoly, evalPoly_addPoly, evalPoly_mulTermPoly, ih,
      cr_right_distrib]

def RExpr.norm : RExpr → RPoly
  | .zero => []
  | .one => [(1, [])]
  | .var i => [(1, [i])]
  | .neg e => negPoly e.norm
  | .add e₁ e₂ => addPoly e₁.norm e₂.norm
  | .sub e₁ e₂ => addPoly e₁.norm (negPoly e₂.norm)
  | .mul e₁ e₂ => mulPoly e₁.norm e₂.norm

theorem RExpr.eval_norm (env : Nat → R) (e : RExpr) :
    evalPoly env e.norm = e.eval env := by
  induction e with
  | zero => rfl
  | one =>
    change ((0 : R) + 1) * 1 + 0 = 1
    rw [CommRingOps.zero_add, cr_mul_one, cr_add_zero]
  | var i =>
    change ((0 : R) + 1) * (env i * 1) + 0 = env i
    rw [CommRingOps.zero_add, cr_mul_one, CommRingOps.one_mul, cr_add_zero]
  | neg e ih => simp [RExpr.norm, RExpr.eval, evalPoly_negPoly, ih]
  | add e₁ e₂ ih₁ ih₂ => simp [RExpr.norm, RExpr.eval, evalPoly_addPoly, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp [RExpr.norm, RExpr.eval, evalPoly_addPoly, evalPoly_negPoly, ih₁, ih₂,
      CommRingOps.sub_eq_add_neg]
  | mul e₁ e₂ ih₁ ih₂ => simp [RExpr.norm, RExpr.eval, evalPoly_mulPoly, ih₁, ih₂]

theorem RExpr.eq_of_norm_eq (env : Nat → R) {e₁ e₂ : RExpr} (h : e₁.norm = e₂.norm) :
    e₁.eval env = e₂.eval env := by
  rw [← RExpr.eval_norm env e₁, ← RExpr.eval_norm env e₂, h]

end CommRingLemmas

instance : CommRingOps Int where
  zero := 0
  one := 1
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

class HasInv (F : Type) where
  inv : F → F

postfix:max "⁻¹" => HasInv.inv

/-- A commutative field `F` that is formally real (hence characteristic zero and sum-of-squares
    anisotropic): a sum of four squares vanishes only when all four terms vanish. Both `ℝ` and `ℚ`
    are canonical instances. -/
class FormallyRealField (F : Type) extends CommRingOps F, HasInv F where
  zero_ne_one : (0 : F) ≠ 1
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : F)⁻¹ = 0
  char_zero : ∀ n : Nat, crOfNat F (n + 1) ≠ 0
  sum_four_sq_eq_zero :
    ∀ a b c d : F, a * a + b * b + c * c + d * d = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

section FieldLemmas

variable {F : Type} [FormallyRealField F]

theorem one_ne_zeroF : (1 : F) ≠ 0 :=
  fun h => FormallyRealField.zero_ne_one h.symm

theorem neg_one_ne_oneF : -(1 : F) ≠ 1 := by
  intro h
  have h2 : (1 : F) + 1 = 0 := by
    calc
      (1 : F) + 1 = -(1 : F) + 1 := by rw [h]
      _ = 0 := CommRingOps.neg_add_cancel 1
  have hsq : (1 : F) * 1 + 1 * 1 + 0 * 0 + 0 * 0 = 0 := by
    rw [cr_mul_one, cr_mul_zero, cr_add_zero, cr_add_zero]
    exact h2
  exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero 1 1 0 0 hsq).1

theorem inv_mul_cancelF {a : F} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommRingOps.mul_comm, FormallyRealField.mul_inv_cancel a h]

theorem mul_eq_zeroF {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    calc
      b = 1 * b := (CommRingOps.one_mul b).symm
      _ = (a⁻¹ * a) * b := by rw [inv_mul_cancelF ha]
      _ = a⁻¹ * (a * b) := CommRingOps.mul_assoc a⁻¹ a b
      _ = a⁻¹ * 0 := by rw [h]
      _ = 0 := cr_mul_zero a⁻¹

theorem crOfNat_injF {m n : Nat} (h : crOfNat F m = crOfNat F n) : m = n := by
  by_cases hlt : m < n
  · have hn : n = m + ((n - m - 1) + 1) := by omega
    rw [hn, crOfNat_add] at h
    have h0 : (0 : F) = crOfNat F ((n - m - 1) + 1) := by
      apply cr_add_left_cancel (a := crOfNat F m)
      rw [cr_add_zero]
      exact h
    exact False.elim (FormallyRealField.char_zero (n - m - 1) h0.symm)
  · by_cases hgt : n < m
    · have hm : m = n + ((m - n - 1) + 1) := by omega
      rw [hm, crOfNat_add] at h
      have h0 : crOfNat F ((m - n - 1) + 1) = 0 := by
        apply cr_add_left_cancel (a := crOfNat F n)
        rw [cr_add_zero]
        exact h
      exact False.elim (FormallyRealField.char_zero (m - n - 1) h0)
    · omega

def twoF (F : Type) [FormallyRealField F] : F := (1 : F) + 1

theorem two_ne_zeroF : twoF F ≠ 0 := by
  intro h
  have hsq : (1 : F) * 1 + 1 * 1 + 0 * 0 + 0 * 0 = 0 := by
    rw [cr_mul_one, cr_mul_zero, cr_add_zero, cr_add_zero]
    exact h
  exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero 1 1 0 0 hsq).1

def halfF (F : Type) [FormallyRealField F] : F := (twoF F)⁻¹

theorem two_mul_halfF : twoF F * halfF F = 1 :=
  FormallyRealField.mul_inv_cancel (twoF F) two_ne_zeroF

theorem half_mul_twoF : halfF F * twoF F = 1 :=
  inv_mul_cancelF two_ne_zeroF

theorem sq_add_one_ne_zeroF (x : F) : x * x + 1 ≠ 0 := by
  intro h
  have hsq : x * x + (1 : F) * 1 + 0 * 0 + 0 * 0 = 0 := by
    rw [cr_mul_one, cr_mul_zero, cr_add_zero, cr_add_zero]
    exact h
  exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero x 1 0 0 hsq).2.1

theorem one_add_sq_ne_zeroF (x : F) : 1 + x * x ≠ 0 := by
  rw [CommRingOps.add_comm]
  exact sq_add_one_ne_zeroF x

theorem sq_add_two_ne_zeroF (x : F) : x * x + twoF F ≠ 0 := by
  intro h
  have hsq : x * x + (1 : F) * 1 + 1 * 1 + 0 * 0 = 0 := by
    unfold twoF at h
    rw [cr_mul_one, cr_mul_zero, cr_add_zero, CommRingOps.add_assoc]
    exact h
  exact one_ne_zeroF (FormallyRealField.sum_four_sq_eq_zero x 1 1 0 hsq).2.1

theorem sum_two_sq_eq_zeroF {a b : F} (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  have h4 : a * a + b * b + (0 : F) * 0 + 0 * 0 = 0 := by
    rw [cr_mul_zero, cr_add_zero, cr_add_zero]
    exact h
  have hres := FormallyRealField.sum_four_sq_eq_zero a b 0 0 h4
  exact ⟨hres.1, hres.2.1⟩

def signPow (F : Type) [FormallyRealField F] : Nat → F
  | 0 => 1
  | k + 1 => -(signPow F k)

theorem signPow_cases (k : Nat) :
    (k % 2 = 0 ∧ signPow F k = 1) ∨ (k % 2 = 1 ∧ signPow F k = -(1 : F)) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
    cases ih with
    | inl h =>
      right
      refine ⟨by omega, ?_⟩
      simp [signPow, h.2]
    | inr h =>
      left
      refine ⟨by omega, ?_⟩
      simp [signPow, h.2, cr_neg_neg]

theorem signPow_even_iff (k : Nat) : signPow F k = 1 ↔ k % 2 = 0 := by
  cases signPow_cases (F := F) k with
  | inl h =>
    constructor
    · intro _; exact h.1
    · intro _; exact h.2
  | inr h =>
    constructor
    · intro heq
      rw [h.2] at heq
      exact False.elim (neg_one_ne_oneF heq)
    · intro hmod; omega

theorem signPow_odd_iff (k : Nat) : signPow F k = -(1 : F) ↔ k % 2 = 1 := by
  cases signPow_cases (F := F) k with
  | inl h =>
    constructor
    · intro heq
      rw [h.2] at heq
      exact False.elim (neg_one_ne_oneF heq.symm)
    · intro hmod; omega
  | inr h =>
    constructor
    · intro _; exact h.1
    · intro _; exact h.2

def envGet {α : Type} (default : α) : List α → Nat → α
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, n + 1 => envGet default xs n

end FieldLemmas

/-! ## Constructive Rational Instance `QField` (Non-Vacuity Witness) -/

structure FracPair where
  num : Int
  den : Int
  den_pos : 0 < den

def FracRel (p q : FracPair) : Prop :=
  p.num * q.den = q.num * p.den

theorem fracRel_refl (p : FracPair) : FracRel p p := rfl

theorem fracRel_symm {p q : FracPair} (h : FracRel p q) : FracRel q p := h.symm

theorem int_mul_cancel_pos {a b c : Int} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hdiff : (a - b) * c = 0 := by
    have hr :
        RExpr.eval (envGet (0 : Int) [a, b, c])
          (.mul (.sub (.var 0) (.var 1)) (.var 2)) =
        RExpr.eval (envGet (0 : Int) [a, b, c])
          (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) :=
      RExpr.eq_of_norm_eq _ rfl
    change (a - b) * c = a * c - b * c at hr
    rw [hr, h, Int.sub_self]
  cases Int.mul_eq_zero.mp hdiff with
  | inl hab => omega
  | inr hc0 => omega

theorem fracRel_trans {p q r : FracPair} (hpq : FracRel p q) (hqr : FracRel q r) :
    FracRel p r := by
  unfold FracRel at *
  apply int_mul_cancel_pos q.den_pos
  calc
    (p.num * r.den) * q.den = (p.num * q.den) * r.den :=
      RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, q.den, r.den])
        (e₁ := .mul (.mul (.var 0) (.var 2)) (.var 1))
        (e₂ := .mul (.mul (.var 0) (.var 1)) (.var 2)) rfl
    _ = (q.num * p.den) * r.den := by rw [hpq]
    _ = (q.num * r.den) * p.den :=
      RExpr.eq_of_norm_eq (envGet (0 : Int) [q.num, p.den, r.den])
        (e₁ := .mul (.mul (.var 0) (.var 1)) (.var 2))
        (e₂ := .mul (.mul (.var 0) (.var 2)) (.var 1)) rfl
    _ = (r.num * q.den) * p.den := by rw [hqr]
    _ = (r.num * p.den) * q.den :=
      RExpr.eq_of_norm_eq (envGet (0 : Int) [r.num, q.den, p.den])
        (e₁ := .mul (.mul (.var 0) (.var 1)) (.var 2))
        (e₂ := .mul (.mul (.var 0) (.var 2)) (.var 1)) rfl

def QSetoid : Setoid FracPair where
  r := FracRel
  iseqv := ⟨fracRel_refl, fracRel_symm, fracRel_trans⟩

def QField : Type := Quotient QSetoid

namespace QField

def mk (n d : Int) (hd : 0 < d) : QField :=
  Quotient.mk QSetoid ⟨n, d, hd⟩

def addPair (p q : FracPair) : FracPair :=
  ⟨p.num * q.den + q.num * p.den, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩

def negPair (p : FracPair) : FracPair :=
  ⟨-p.num, p.den, p.den_pos⟩

def mulPair (p q : FracPair) : FracPair :=
  ⟨p.num * q.num, p.den * q.den, Int.mul_pos p.den_pos q.den_pos⟩

def invPair (p : FracPair) : FracPair :=
  if hpos : 0 < p.num then
    ⟨p.den, p.num, hpos⟩
  else if _ : p.num < 0 then
    ⟨-p.den, -p.num, by omega⟩
  else
    ⟨0, 1, by omega⟩

theorem addPair_wd {p₁ p₂ q₁ q₂ : FracPair} (hp : FracRel p₁ p₂) (hq : FracRel q₁ q₂) :
    FracRel (addPair p₁ q₁) (addPair p₂ q₂) := by
  unfold FracRel addPair at *
  dsimp only
  calc
    (p₁.num * q₁.den + q₁.num * p₁.den) * (p₂.den * q₂.den)
        = (p₁.num * p₂.den) * (q₁.den * q₂.den) + (q₁.num * q₂.den) * (p₁.den * p₂.den) :=
          RExpr.eq_of_norm_eq
            (envGet (0 : Int) [p₁.num, p₁.den, p₂.den, q₁.num, q₁.den, q₂.den])
            (e₁ := .mul (.add (.mul (.var 0) (.var 4)) (.mul (.var 3) (.var 1)))
                        (.mul (.var 2) (.var 5)))
            (e₂ := .add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 4) (.var 5)))
                        (.mul (.mul (.var 3) (.var 5)) (.mul (.var 1) (.var 2)))) rfl
    _ = (p₂.num * p₁.den) * (q₁.den * q₂.den) + (q₂.num * q₁.den) * (p₁.den * p₂.den) := by
          rw [hp, hq]
    _ = (p₂.num * q₂.den + q₂.num * p₂.den) * (p₁.den * q₁.den) :=
          RExpr.eq_of_norm_eq
            (envGet (0 : Int) [p₂.num, p₁.den, p₂.den, q₂.num, q₁.den, q₂.den])
            (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.var 5)))
                        (.mul (.mul (.var 3) (.var 4)) (.mul (.var 1) (.var 2))))
            (e₂ := .mul (.add (.mul (.var 0) (.var 5)) (.mul (.var 3) (.var 2)))
                        (.mul (.var 1) (.var 4))) rfl

theorem negPair_wd {p₁ p₂ : FracPair} (hp : FracRel p₁ p₂) :
    FracRel (negPair p₁) (negPair p₂) := by
  unfold FracRel negPair at *
  dsimp only
  rw [Int.neg_mul, Int.neg_mul, hp]

theorem mulPair_wd {p₁ p₂ q₁ q₂ : FracPair} (hp : FracRel p₁ p₂) (hq : FracRel q₁ q₂) :
    FracRel (mulPair p₁ q₁) (mulPair p₂ q₂) := by
  unfold FracRel mulPair at *
  dsimp only
  calc
    (p₁.num * q₁.num) * (p₂.den * q₂.den)
        = (p₁.num * p₂.den) * (q₁.num * q₂.den) :=
          RExpr.eq_of_norm_eq (envGet (0 : Int) [p₁.num, q₁.num, p₂.den, q₂.den])
            (e₁ := .mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (e₂ := .mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) rfl
    _ = (p₂.num * p₁.den) * (q₂.num * q₁.den) := by rw [hp, hq]
    _ = (p₂.num * q₂.num) * (p₁.den * q₁.den) :=
          RExpr.eq_of_norm_eq (envGet (0 : Int) [p₂.num, q₂.num, p₁.den, q₁.den])
            (e₁ := .mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
            (e₂ := .mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) rfl

theorem invPair_wd {p₁ p₂ : FracPair} (hp : FracRel p₁ p₂) :
    FracRel (invPair p₁) (invPair p₂) := by
  unfold FracRel invPair at *
  have hp1d : 0 < p₁.den := p₁.den_pos
  have hp2d : 0 < p₂.den := p₂.den_pos
  by_cases h1pos : 0 < p₁.num
  · have h2pos : 0 < p₂.num := by
      have hprod : 0 < p₁.num * p₂.den := Int.mul_pos h1pos hp2d
      rw [hp] at hprod
      by_cases h2 : 0 < p₂.num
      · exact h2
      · have hle : p₂.num * p₁.den ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
        omega
    simp only [h1pos, h2pos, ↓reduceDIte]
    calc
      p₁.den * p₂.num = p₂.num * p₁.den := Int.mul_comm _ _
      _ = p₁.num * p₂.den := hp.symm
      _ = p₂.den * p₁.num := Int.mul_comm _ _
  · by_cases h1neg : p₁.num < 0
    · have h2neg : p₂.num < 0 := by
        have hprod : p₁.num * p₂.den < 0 := Int.mul_neg_of_neg_of_pos h1neg hp2d
        rw [hp] at hprod
        by_cases h2 : p₂.num < 0
        · exact h2
        · have hge : 0 ≤ p₂.num * p₁.den := Int.mul_nonneg (by omega) (by omega)
          omega
      have h2npos : ¬ (0 < p₂.num) := by omega
      simp only [h1pos, h1neg, h2npos, h2neg, ↓reduceDIte]
      calc
        (-p₁.den) * (-p₂.num) = p₂.num * p₁.den :=
          RExpr.eq_of_norm_eq (envGet (0 : Int) [p₁.den, p₂.num])
            (e₁ := .mul (.neg (.var 0)) (.neg (.var 1)))
            (e₂ := .mul (.var 1) (.var 0)) rfl
        _ = p₁.num * p₂.den := hp.symm
        _ = (-p₂.den) * (-p₁.num) :=
          RExpr.eq_of_norm_eq (envGet (0 : Int) [p₂.den, p₁.num])
            (e₁ := .mul (.var 1) (.var 0))
            (e₂ := .mul (.neg (.var 0)) (.neg (.var 1))) rfl
    · have h1zero : p₁.num = 0 := by omega
      have h2zero : p₂.num = 0 := by
        rw [h1zero, Int.zero_mul] at hp
        cases Int.mul_eq_zero.mp hp.symm with
        | inl h => exact h
        | inr h => omega
      have h2npos : ¬ (0 < p₂.num) := by omega
      have h2nneg : ¬ (p₂.num < 0) := by omega
      simp only [h1pos, h1neg, h2npos, h2nneg, ↓reduceDIte]

def add : QField → QField → QField :=
  Quotient.lift₂ (fun p q => Quotient.mk QSetoid (addPair p q))
    (fun _ _ _ _ hp hq => Quotient.sound (addPair_wd hp hq))

def neg : QField → QField :=
  Quotient.lift (fun p => Quotient.mk QSetoid (negPair p))
    (fun _ _ hp => Quotient.sound (negPair_wd hp))

def mul : QField → QField → QField :=
  Quotient.lift₂ (fun p q => Quotient.mk QSetoid (mulPair p q))
    (fun _ _ _ _ hp hq => Quotient.sound (mulPair_wd hp hq))

def inv : QField → QField :=
  Quotient.lift (fun p => Quotient.mk QSetoid (invPair p))
    (fun _ _ hp => Quotient.sound (invPair_wd hp))

def zero : QField := mk 0 1 (by omega)
def one : QField := mk 1 1 (by omega)

theorem addPair_nonneg_eq_zero {p q : FracPair}
    (hp : 0 ≤ p.num) (hq : 0 ≤ q.num) (h : (addPair p q).num = 0) :
    p.num = 0 ∧ q.num = 0 := by
  unfold addPair at h
  dsimp only at h
  have hpd : 0 < p.den := p.den_pos
  have hqd : 0 < q.den := q.den_pos
  have hpq : 0 ≤ p.num * q.den := Int.mul_nonneg hp (by omega)
  have hqp : 0 ≤ q.num * p.den := Int.mul_nonneg hq (by omega)
  have h1 : p.num * q.den = 0 := by omega
  have h2 : q.num * p.den = 0 := by omega
  have hp0 : p.num = 0 := by
    cases Int.mul_eq_zero.mp h1 with
    | inl hz => exact hz
    | inr hz => omega
  have hq0 : q.num = 0 := by
    cases Int.mul_eq_zero.mp h2 with
    | inl hz => exact hz
    | inr hz => omega
  exact ⟨hp0, hq0⟩

theorem mulPair_self_nonneg (p : FracPair) : 0 ≤ (mulPair p p).num := by
  unfold mulPair
  dsimp only
  by_cases h : 0 ≤ p.num
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -p.num := by omega
    have heq : p.num * p.num = (-p.num) * (-p.num) :=
      RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num])
        (e₁ := .mul (.var 0) (.var 0))
        (e₂ := .mul (.neg (.var 0)) (.neg (.var 0))) rfl
    rw [heq]
    exact Int.mul_nonneg hn hn

instance commRingOps : CommRingOps QField where
  add := add
  sub a b := add a (neg b)
  mul := mul
  neg := neg
  zero := zero
  one := one
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    change FracRel (addPair (addPair p q) r) (addPair p (addPair q r))
    unfold FracRel addPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den, q.num, q.den, r.num, r.den])
      (e₁ := .mul (.add (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))) (.var 5))
                        (.mul (.var 4) (.mul (.var 1) (.var 3))))
                  (.mul (.var 1) (.mul (.var 3) (.var 5))))
      (e₂ := .mul (.add (.mul (.var 0) (.mul (.var 3) (.var 5)))
                        (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))) (.var 1)))
                  (.mul (.mul (.var 1) (.var 3)) (.var 5))) rfl
  add_comm a b := by
    refine Quotient.inductionOn₂ a b (fun p q => Quotient.sound ?_)
    change FracRel (addPair p q) (addPair q p)
    unfold FracRel addPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den, q.num, q.den])
      (e₁ := .mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))) (.mul (.var 3) (.var 1)))
      (e₂ := .mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 3))) rfl
  zero_add a := by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    change FracRel (addPair ⟨0, 1, _⟩ p) p
    unfold FracRel addPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den])
      (e₁ := .mul (.add (.mul .zero (.var 1)) (.mul (.var 0) .one)) (.var 1))
      (e₂ := .mul (.var 0) (.mul .one (.var 1))) rfl
  neg_add_cancel a := by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    change FracRel (addPair (negPair p) p) ⟨0, 1, _⟩
    unfold FracRel addPair negPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den])
      (e₁ := .mul (.add (.mul (.neg (.var 0)) (.var 1)) (.mul (.var 0) (.var 1))) .one)
      (e₂ := .mul .zero (.mul (.var 1) (.var 1))) rfl
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    change FracRel (mulPair (mulPair p q) r) (mulPair p (mulPair q r))
    unfold FracRel mulPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den, q.num, q.den, r.num, r.den])
      (e₁ := .mul (.mul (.mul (.var 0) (.var 2)) (.var 4))
                  (.mul (.var 1) (.mul (.var 3) (.var 5))))
      (e₂ := .mul (.mul (.var 0) (.mul (.var 2) (.var 4)))
                  (.mul (.mul (.var 1) (.var 3)) (.var 5))) rfl
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b (fun p q => Quotient.sound ?_)
    change FracRel (mulPair p q) (mulPair q p)
    unfold FracRel mulPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den, q.num, q.den])
      (e₁ := .mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 1)))
      (e₂ := .mul (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 3))) rfl
  one_mul a := by
    refine Quotient.inductionOn a (fun p => Quotient.sound ?_)
    change FracRel (mulPair ⟨1, 1, _⟩ p) p
    unfold FracRel mulPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den])
      (e₁ := .mul (.mul .one (.var 0)) (.var 1))
      (e₂ := .mul (.var 0) (.mul .one (.var 1))) rfl
  left_distrib a b c := by
    refine Quotient.inductionOn₃ a b c (fun p q r => Quotient.sound ?_)
    change FracRel (mulPair p (addPair q r)) (addPair (mulPair p q) (mulPair p r))
    unfold FracRel mulPair addPair; dsimp only
    exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den, q.num, q.den, r.num, r.den])
      (e₁ := .mul (.mul (.var 0) (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))))
                  (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 5))))
      (e₂ := .mul (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 5)))
                        (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))))
                  (.mul (.var 1) (.mul (.var 3) (.var 5)))) rfl

theorem crOfNat_eq_mk (n : Nat) : crOfNat QField n = mk (Int.ofNat n) 1 (by omega) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change add (crOfNat QField n) one = mk (Int.ofNat (n + 1)) 1 _
    rw [ih]
    apply Quotient.sound
    change FracRel (addPair ⟨Int.ofNat n, 1, _⟩ ⟨1, 1, _⟩) ⟨Int.ofNat (n + 1), 1, _⟩
    unfold FracRel addPair
    dsimp only
    simp [Int.ofNat_eq_coe]

instance : FormallyRealField QField where
  toCommRingOps := commRingOps
  inv := inv
  zero_ne_one h := by
    have hrel : FracRel ⟨0, 1, by omega⟩ ⟨1, 1, by omega⟩ := Quotient.exact h
    dsimp [FracRel] at hrel
    omega
  mul_inv_cancel a ha := by
    refine Quotient.inductionOn a (fun p => ?_) ha
    intro hp0
    apply Quotient.sound
    change FracRel (mulPair p (invPair p)) ⟨1, 1, _⟩
    unfold FracRel mulPair invPair
    by_cases hpos : 0 < p.num
    · simp only [hpos, ↓reduceDIte]
      exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den])
        (e₁ := .mul (.mul (.var 0) (.var 1)) .one)
        (e₂ := .mul .one (.mul (.var 1) (.var 0))) rfl
    · by_cases hneg : p.num < 0
      · simp only [hpos, hneg, ↓reduceDIte]
        exact RExpr.eq_of_norm_eq (envGet (0 : Int) [p.num, p.den])
          (e₁ := .mul (.mul (.var 0) (.neg (.var 1))) .one)
          (e₂ := .mul .one (.mul (.var 1) (.neg (.var 0)))) rfl
      · exfalso
        apply hp0
        apply Quotient.sound
        change FracRel p ⟨0, 1, _⟩
        unfold FracRel
        dsimp only
        omega
  inv_zero := by
    apply Quotient.sound
    change FracRel (invPair ⟨0, 1, _⟩) ⟨0, 1, _⟩
    unfold FracRel invPair
    simp
  char_zero n h := by
    rw [crOfNat_eq_mk] at h
    have hrel : FracRel ⟨Int.ofNat (n + 1), 1, by omega⟩ ⟨0, 1, by omega⟩ := Quotient.exact h
    dsimp [FracRel] at hrel
    omega
  sum_four_sq_eq_zero a b c d h := by
    revert h
    refine Quotient.inductionOn₂ a b (fun pa pb => ?_)
    refine Quotient.inductionOn₂ c d (fun pc pd h => ?_)
    have hrel : FracRel
        (addPair (addPair (addPair (mulPair pa pa) (mulPair pb pb)) (mulPair pc pc)) (mulPair pd pd))
        ⟨0, 1, by omega⟩ := Quotient.exact h
    unfold FracRel at hrel
    dsimp only at hrel
    rw [Int.mul_one, Int.zero_mul] at hrel
    have hna := mulPair_self_nonneg pa
    have hnb := mulPair_self_nonneg pb
    have hnc := mulPair_self_nonneg pc
    have hnd := mulPair_self_nonneg pd
    have hab : 0 ≤ (addPair (mulPair pa pa) (mulPair pb pb)).num :=
      Int.add_nonneg (Int.mul_nonneg hna (Int.le_of_lt (mulPair pb pb).den_pos))
                     (Int.mul_nonneg hnb (Int.le_of_lt (mulPair pa pa).den_pos))
    have habc : 0 ≤ (addPair (addPair (mulPair pa pa) (mulPair pb pb)) (mulPair pc pc)).num :=
      Int.add_nonneg (Int.mul_nonneg hab (Int.le_of_lt (mulPair pc pc).den_pos))
                     (Int.mul_nonneg hnc (Int.le_of_lt (addPair (mulPair pa pa) (mulPair pb pb)).den_pos))
    obtain ⟨h123, h4⟩ := addPair_nonneg_eq_zero habc hnd hrel
    obtain ⟨h12, h3⟩ := addPair_nonneg_eq_zero hab hnc h123
    obtain ⟨h1, h2⟩ := addPair_nonneg_eq_zero hna hnb h12
    have sq0 : ∀ p : FracPair, (mulPair p p).num = 0 → Quotient.mk QSetoid p = zero := by
      intro p hp
      apply Quotient.sound
      change FracRel p ⟨0, 1, _⟩
      unfold FracRel; dsimp only
      unfold mulPair at hp; dsimp only at hp
      cases Int.mul_eq_zero.mp hp with
      | inl hz => omega
      | inr hz => omega
    exact ⟨sq0 pa h1, sq0 pb h2, sq0 pc h3, sq0 pd h4⟩

/-- Elementary parity lemma on `Nat`: if `n * n` is even, then `n` is even. -/
theorem nat_even_of_sq_even {n k : Nat} (h : n * n = 2 * k) : ∃ m : Nat, n = 2 * m := by
  by_cases hpar : n % 2 = 0
  · exact ⟨n / 2, by omega⟩
  · exfalso
    have hodd : n = 2 * (n / 2) + 1 := by omega
    let q := n / 2
    have hsq : (2 * q + 1) * (2 * q + 1) = 2 * (2 * (q * q) + 2 * q) + 1 := by
      calc
        (2 * q + 1) * (2 * q + 1) = (2 * q + 1) * (2 * q) + (2 * q + 1) * 1 :=
          Nat.left_distrib _ _ _
        _ = (2 * q) * (2 * q) + 1 * (2 * q) + (2 * q + 1) := by
          rw [Nat.right_distrib, Nat.mul_one]
        _ = 2 * (2 * (q * q) + 2 * q) + 1 := by
          have h4 : (2 * q) * (2 * q) = 2 * (2 * (q * q)) := by
            calc
              (2 * q) * (2 * q) = 2 * (q * (2 * q)) := Nat.mul_assoc 2 q (2 * q)
              _ = 2 * ((2 * q) * q) := by rw [Nat.mul_comm q (2 * q)]
              _ = 2 * (2 * (q * q)) := by rw [Nat.mul_assoc 2 q q]
          rw [h4]
          omega
    change (n * n = 2 * k) at h
    rw [hodd] at h
    change (2 * q + 1) * (2 * q + 1) = 2 * k at h
    omega

/-- Infinite descent: `a^2 ≠ 2 b^2` for all `a, b : Nat` with `b > 0`. -/
theorem nat_sq_ne_two_mul_sq : ∀ b : Nat, 0 < b → ∀ a : Nat, a * a ≠ 2 * (b * b) := by
  intro b
  refine Nat.strongRecOn b (fun b ih hb a h => ?_)
  obtain ⟨a', ha'⟩ := nat_even_of_sq_even h
  have hb2 : b * b = 2 * (a' * a') := by
    rw [ha'] at h
    have h4 : (2 * a') * (2 * a') = 2 * (2 * (a' * a')) := by
      calc
        (2 * a') * (2 * a') = 2 * (a' * (2 * a')) := Nat.mul_assoc 2 a' (2 * a')
        _ = 2 * ((2 * a') * a') := by rw [Nat.mul_comm a' (2 * a')]
        _ = 2 * (2 * (a' * a')) := by rw [Nat.mul_assoc 2 a' a']
    rw [h4] at h
    omega
  obtain ⟨b', hb'⟩ := nat_even_of_sq_even hb2
  have hb'pos : 0 < b' := by omega
  have hb'lt : b' < b := by omega
  have ha'2 : a' * a' = 2 * (b' * b') := by
    rw [hb'] at hb2
    have h4 : (2 * b') * (2 * b') = 2 * (2 * (b' * b')) := by
      calc
        (2 * b') * (2 * b') = 2 * (b' * (2 * b')) := Nat.mul_assoc 2 b' (2 * b')
        _ = 2 * ((2 * b') * b') := by rw [Nat.mul_comm b' (2 * b')]
        _ = 2 * (2 * (b' * b')) := by rw [Nat.mul_assoc 2 b' b']
    rw [h4] at hb2
    omega
  exact ih b' hb'lt hb'pos a' ha'2

/-- `2` has no square root in `QField` (`ℚ`). -/
theorem no_sqrt_two (x : QField) : x * x ≠ twoF QField := by
  refine Quotient.inductionOn x (fun p h => ?_)
  have htwo : twoF QField = mk 2 1 (by omega) := by
    change add one one = mk 2 1 _
    apply Quotient.sound
    rfl
  rw [htwo] at h
  have hrel : FracRel (mulPair p p) ⟨2, 1, by omega⟩ := Quotient.exact h
  unfold FracRel mulPair at hrel
  dsimp only at hrel
  rw [Int.mul_one] at hrel
  have hpd : 0 < p.den := p.den_pos
  cases hden : p.den with
  | negSucc _ =>
    rw [hden] at hpd
    omega
  | ofNat b =>
    cases b with
    | zero =>
      rw [hden] at hpd
      nomatch hpd
    | succ b' =>
      let bp := b' + 1
      have hbpos : 0 < bp := Nat.zero_lt_succ b'
      rw [hden] at hrel
      cases hnum : p.num with
      | ofNat a =>
        rw [hnum] at hrel
        change Int.ofNat (a * a) = Int.ofNat (2 * (bp * bp)) at hrel
        have hnat : a * a = 2 * (bp * bp) := Int.ofNat.inj hrel
        exact nat_sq_ne_two_mul_sq bp hbpos a hnat
      | negSucc a' =>
        rw [hnum] at hrel
        have hpossq : Int.negSucc a' * Int.negSucc a' = Int.ofNat ((a' + 1) * (a' + 1)) := rfl
        rw [hpossq] at hrel
        change Int.ofNat ((a' + 1) * (a' + 1)) = Int.ofNat (2 * (bp * bp)) at hrel
        have hnat : (a' + 1) * (a' + 1) = 2 * (bp * bp) := Int.ofNat.inj hrel
        exact nat_sq_ne_two_mul_sq bp hbpos (a' + 1) hnat

end QField

end Conjecture00000007609
