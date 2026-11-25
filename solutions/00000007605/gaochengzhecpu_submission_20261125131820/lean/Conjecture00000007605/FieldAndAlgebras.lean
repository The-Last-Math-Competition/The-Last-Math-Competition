/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Formalization for Conjecture 00000007605:
  1. FormallyRealField F (satisfied by ℝ and ℚ) + fast pure-Bool reflective polynomial normalizer,
  2. Constructive rational instance QField witnessing non-vacuity in Core Lean 4,
  3. Unital associative F-algebras, homomorphisms, isomorphisms, centers, and division algebras,
  4. The three Frobenius division algebras over F: realAlg F, ComplexOver F, and QuatOver F,
     and proof that they are pairwise non-isomorphic division F-algebras.
-/

namespace Conjecture00000007605

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
    | succ k =>
      rfl
  | negSucc k =>
    change crOfNat R (k + 1) = -(-(crOfNat R (k + 1)))
    rw [cr_neg_neg]

theorem crOfInt_add (x y : Int) : crOfInt R (x + y) = crOfInt R x + crOfInt R y := by
  cases x with
  | ofNat m =>
    cases y with
    | ofNat n =>
      change crOfNat R (m + n) = crOfNat R m + crOfNat R n
      exact crOfNat_add m n
    | negSucc n =>
      change crOfInt R (Int.subNatNat m (n + 1)) = crOfNat R m + -(crOfNat R (n + 1))
      exact crOfInt_subNatNat m (n + 1)
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
    | ofNat n =>
      change crOfNat R (m * n) = crOfNat R m * crOfNat R n
      exact crOfNat_mul m n
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

/-- Pure `Bool` three-way comparison on `Nat` (avoids `Decidable` proof terms in kernel WHNF). -/
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
  | zero =>
    cases n <;> simp [natCmp]
  | succ m ih =>
    cases n with
    | zero => simp [natCmp]
    | succ n => simp [natCmp, ih]

theorem monoCmp_eq_iff (xs ys : List Nat) : monoCmp xs ys = .eq ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [monoCmp]
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
  | negSucc n =>
    simp [intIsZero]

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
  | false =>
    exact evalPoly_addTermAux env c vs p

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
  | neg e ih =>
    simp [RExpr.norm, RExpr.eval, evalPoly_negPoly, ih]
  | add e₁ e₂ ih₁ ih₂ =>
    simp [RExpr.norm, RExpr.eval, evalPoly_addPoly, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp [RExpr.norm, RExpr.eval, evalPoly_addPoly, evalPoly_negPoly, ih₁, ih₂,
      CommRingOps.sub_eq_add_neg]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp [RExpr.norm, RExpr.eval, evalPoly_mulPoly, ih₁, ih₂]

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

theorem crOfInt_ne_zeroF {z : Int} (hz : z ≠ 0) : crOfInt F z ≠ 0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact False.elim (hz rfl)
    | succ k => exact FormallyRealField.char_zero k
  | negSucc k =>
    intro h
    change -(crOfNat F (k + 1)) = 0 at h
    have h2 : crOfNat F (k + 1) = 0 := by
      rw [← cr_neg_neg (crOfNat F (k + 1)), h, cr_neg_zero]
    exact FormallyRealField.char_zero k h2

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

theorem sum_two_sq_eq_zeroF {a b : F} (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  have h4 : a * a + b * b + (0 : F) * 0 + 0 * 0 = 0 := by
    rw [cr_mul_zero, cr_add_zero, cr_add_zero]
    exact h
  have hres := FormallyRealField.sum_four_sq_eq_zero a b 0 0 h4
  exact ⟨hres.1, hres.2.1⟩

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
      · have hle : p₂.num * p₁.den ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
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

end QField

/-! ## Unital Associative F-Algebras, Homomorphisms, Isomorphisms, Centers, Division Algebras -/

structure Alg (F : Type) [FormallyRealField F] (A : Type) where
  zero : A
  one : A
  add : A → A → A
  neg : A → A
  mul : A → A → A
  smul : F → A → A
  add_assoc : ∀ x y z : A, add (add x y) z = add x (add y z)
  add_comm : ∀ x y : A, add x y = add y x
  zero_add : ∀ x : A, add zero x = x
  neg_add_cancel : ∀ x : A, add (neg x) x = zero
  mul_assoc : ∀ x y z : A, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x : A, mul one x = x
  mul_one : ∀ x : A, mul x one = x
  left_distrib : ∀ x y z : A, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib : ∀ x y z : A, mul (add x y) z = add (mul x z) (mul y z)
  one_smul : ∀ x : A, smul 1 x = x
  mul_smul : ∀ c d : F, ∀ x : A, smul (c * d) x = smul c (smul d x)
  smul_add : ∀ c : F, ∀ x y : A, smul c (add x y) = add (smul c x) (smul c y)
  add_smul : ∀ c d : F, ∀ x : A, smul (c + d) x = add (smul c x) (smul d x)
  smul_mul_left : ∀ c : F, ∀ x y : A, mul (smul c x) y = smul c (mul x y)
  smul_mul_right : ∀ c : F, ∀ x y : A, mul x (smul c y) = smul c (mul x y)

section AlgBasic

variable {F : Type} [FormallyRealField F]

theorem alg_add_zero {A : Type} (alg : Alg F A) (x : A) : alg.add x alg.zero = x := by
  rw [alg.add_comm, alg.zero_add]

theorem alg_add_neg_cancel {A : Type} (alg : Alg F A) (x : A) : alg.add x (alg.neg x) = alg.zero := by
  rw [alg.add_comm, alg.neg_add_cancel]

theorem alg_add_left_cancel {A : Type} (alg : Alg F A) {x y z : A}
    (h : alg.add x y = alg.add x z) : y = z := by
  have h1 := congrArg (alg.add (alg.neg x)) h
  rw [← alg.add_assoc, ← alg.add_assoc, alg.neg_add_cancel, alg.zero_add, alg.zero_add] at h1
  exact h1

theorem alg_zero_smul {A : Type} (alg : Alg F A) (x : A) : alg.smul 0 x = alg.zero := by
  apply alg_add_left_cancel alg (x := alg.smul 0 x)
  rw [← alg.add_smul, cr_add_zero, alg_add_zero]

theorem alg_neg_one_smul {A : Type} (alg : Alg F A) (x : A) :
    alg.smul (-(1 : F)) x = alg.neg x := by
  apply alg_add_left_cancel alg (x := x)
  calc
    alg.add x (alg.smul (-(1 : F)) x)
        = alg.add (alg.smul 1 x) (alg.smul (-(1 : F)) x) := by rw [alg.one_smul]
    _ = alg.smul ((1 : F) + -(1 : F)) x := (alg.add_smul 1 (-(1 : F)) x).symm
    _ = alg.smul 0 x := by rw [cr_add_neg_cancel]
    _ = alg.zero := alg_zero_smul alg x
    _ = alg.add x (alg.neg x) := (alg_add_neg_cancel alg x).symm

/-- Unital `F`-algebra homomorphism. -/
structure AlgHom (F : Type) [FormallyRealField F] {A B : Type}
    (algA : Alg F A) (algB : Alg F B) where
  toFun : A → B
  map_one : toFun algA.one = algB.one
  map_add : ∀ x y : A, toFun (algA.add x y) = algB.add (toFun x) (toFun y)
  map_mul : ∀ x y : A, toFun (algA.mul x y) = algB.mul (toFun x) (toFun y)
  map_smul : ∀ c : F, ∀ x : A, toFun (algA.smul c x) = algB.smul c (toFun x)

theorem algHom_map_zero {A B : Type} {algA : Alg F A} {algB : Alg F B}
    (f : AlgHom F algA algB) : f.toFun algA.zero = algB.zero := by
  rw [← alg_zero_smul algA algA.zero, f.map_smul, alg_zero_smul]

theorem algHom_map_neg {A B : Type} {algA : Alg F A} {algB : Alg F B}
    (f : AlgHom F algA algB) (x : A) : f.toFun (algA.neg x) = algB.neg (f.toFun x) := by
  rw [← alg_neg_one_smul algA x, f.map_smul, alg_neg_one_smul]

/-- Unital `F`-algebra isomorphism. -/
structure AlgIso (F : Type) [FormallyRealField F] {A B : Type}
    (algA : Alg F A) (algB : Alg F B) extends AlgHom F algA algB where
  invFun : B → A
  left_inv : ∀ x : A, invFun (toFun x) = x
  right_inv : ∀ y : B, toFun (invFun y) = y

def AlgIso.refl {A : Type} (algA : Alg F A) : AlgIso F algA algA where
  toFun := id
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_smul _ _ := rfl
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

def AlgIso.symm {A B : Type} {algA : Alg F A} {algB : Alg F B}
    (e : AlgIso F algA algB) : AlgIso F algB algA where
  toFun := e.invFun
  map_one := by
    apply (congrArg e.invFun e.map_one).symm.trans
    exact e.left_inv algA.one
  map_add x y := by
    have h : e.toFun (e.invFun (algB.add x y)) = e.toFun (algA.add (e.invFun x) (e.invFun y)) := by
      rw [e.right_inv, e.map_add, e.right_inv, e.right_inv]
    have h2 := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h2
    exact h2
  map_mul x y := by
    have h : e.toFun (e.invFun (algB.mul x y)) = e.toFun (algA.mul (e.invFun x) (e.invFun y)) := by
      rw [e.right_inv, e.map_mul, e.right_inv, e.right_inv]
    have h2 := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h2
    exact h2
  map_smul c x := by
    have h : e.toFun (e.invFun (algB.smul c x)) = e.toFun (algA.smul c (e.invFun x)) := by
      rw [e.right_inv, e.map_smul, e.right_inv]
    have h2 := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h2
    exact h2
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

def AlgIso.trans {A B C : Type} {algA : Alg F A} {algB : Alg F B} {algC : Alg F C}
    (e₁ : AlgIso F algA algB) (e₂ : AlgIso F algB algC) : AlgIso F algA algC where
  toFun x := e₂.toFun (e₁.toFun x)
  map_one := by rw [e₁.map_one, e₂.map_one]
  map_add x y := by rw [e₁.map_add, e₂.map_add]
  map_mul x y := by rw [e₁.map_mul, e₂.map_mul]
  map_smul c x := by rw [e₁.map_smul, e₂.map_smul]
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]

def IsCommAlg {A : Type} (alg : Alg F A) : Prop :=
  ∀ x y : A, alg.mul x y = alg.mul y x

def IsDivisionAlg {A : Type} (alg : Alg F A) : Prop :=
  alg.one ≠ alg.zero ∧ ∀ x : A, x ≠ alg.zero → ∃ y : A, alg.mul x y = alg.one ∧ alg.mul y x = alg.one

def InCenter {A : Type} (alg : Alg F A) (z : A) : Prop :=
  ∀ x : A, alg.mul z x = alg.mul x z

theorem isCommAlg_of_algIso {A B : Type} {algA : Alg F A} {algB : Alg F B}
    (e : AlgIso F algA algB) (hA : IsCommAlg algA) : IsCommAlg algB := by
  intro x y
  calc
    algB.mul x y = algB.mul (e.toFun (e.invFun x)) (e.toFun (e.invFun y)) := by
      rw [e.right_inv, e.right_inv]
    _ = e.toFun (algA.mul (e.invFun x) (e.invFun y)) := (e.map_mul _ _).symm
    _ = e.toFun (algA.mul (e.invFun y) (e.invFun x)) := by rw [hA]
    _ = algB.mul (e.toFun (e.invFun y)) (e.toFun (e.invFun x)) := e.map_mul _ _
    _ = algB.mul y x := by rw [e.right_inv, e.right_inv]

/-! ## The Three Canonical Frobenius Division Algebras: `realAlg`, `ComplexOver`, `QuatOver` -/

/-- 1. Real type: `F` as a 1-dimensional commutative division `F`-algebra. -/
def realAlg (F : Type) [FormallyRealField F] : Alg F F where
  zero := 0
  one := 1
  add a b := a + b
  neg a := -a
  mul a b := a * b
  smul c a := c * a
  add_assoc := CommRingOps.add_assoc
  add_comm := CommRingOps.add_comm
  zero_add := CommRingOps.zero_add
  neg_add_cancel := CommRingOps.neg_add_cancel
  mul_assoc := CommRingOps.mul_assoc
  one_mul := CommRingOps.one_mul
  mul_one := cr_mul_one
  left_distrib := CommRingOps.left_distrib
  right_distrib := cr_right_distrib
  one_smul := CommRingOps.one_mul
  mul_smul := CommRingOps.mul_assoc
  smul_add := CommRingOps.left_distrib
  add_smul := cr_right_distrib
  smul_mul_left _ _ _ := CommRingOps.mul_assoc _ _ _
  smul_mul_right c x y := cr_mul_left_comm x c y

theorem realAlg_isComm : IsCommAlg (realAlg F) := CommRingOps.mul_comm

theorem realAlg_isDivision : IsDivisionAlg (realAlg F) := by
  refine ⟨one_ne_zeroF, fun x hx => ⟨x⁻¹, ?_, ?_⟩⟩
  · exact FormallyRealField.mul_inv_cancel x hx
  · exact inv_mul_cancelF hx

/-- 2. Complex type: `ComplexOver F = F[i]/(i² + 1)`, a 2-dimensional commutative field over `F`. -/
@[ext]
structure ComplexOver (F : Type) where
  re : F
  im : F

namespace ComplexOver

def zero : ComplexOver F := ⟨0, 0⟩
def one : ComplexOver F := ⟨1, 0⟩
def unitI : ComplexOver F := ⟨0, 1⟩
def add (z w : ComplexOver F) : ComplexOver F := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : ComplexOver F) : ComplexOver F := ⟨-z.re, -z.im⟩
def sub (z w : ComplexOver F) : ComplexOver F := add z (neg w)
def mul (z w : ComplexOver F) : ComplexOver F :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def smul (c : F) (z : ComplexOver F) : ComplexOver F := ⟨c * z.re, c * z.im⟩
def conj (z : ComplexOver F) : ComplexOver F := ⟨z.re, -z.im⟩
def normSq (z : ComplexOver F) : F := z.re * z.re + z.im * z.im
def inv (z : ComplexOver F) : ComplexOver F :=
  smul (normSq z)⁻¹ (conj z)

def alg (F : Type) [FormallyRealField F] : Alg F (ComplexOver F) where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  smul := smul
  add_assoc x y z := by ext <;> exact CommRingOps.add_assoc _ _ _
  add_comm x y := by ext <;> exact CommRingOps.add_comm _ _
  zero_add x := by ext <;> exact CommRingOps.zero_add _
  neg_add_cancel x := by ext <;> exact CommRingOps.neg_add_cancel _
  mul_assoc x y z := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .sub (.mul (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 4))
                    (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.var 5)))
        (e₂ := .sub (.mul (.var 0) (.sub (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))))
                    (.mul (.var 1) (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4))))) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .add (.mul (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 5))
                    (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.var 4)))
        (e₂ := .add (.mul (.var 0) (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4))))
                    (.mul (.var 1) (.sub (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))))) rfl
  one_mul x := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im])
        (e₁ := .sub (.mul .one (.var 0)) (.mul .zero (.var 1))) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im])
        (e₁ := .add (.mul .one (.var 1)) (.mul .zero (.var 0))) (e₂ := .var 1) rfl
  mul_one x := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im])
        (e₁ := .sub (.mul (.var 0) .one) (.mul (.var 1) .zero)) (e₂ := .var 0) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im])
        (e₁ := .add (.mul (.var 0) .zero) (.mul (.var 1) .one)) (e₂ := .var 1) rfl
  left_distrib x y z := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .sub (.mul (.var 0) (.add (.var 2) (.var 4))) (.mul (.var 1) (.add (.var 3) (.var 5))))
        (e₂ := .add (.sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                    (.sub (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .add (.mul (.var 0) (.add (.var 3) (.var 5))) (.mul (.var 1) (.add (.var 2) (.var 4))))
        (e₂ := .add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                    (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))) rfl
  right_distrib x y z := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .sub (.mul (.add (.var 0) (.var 2)) (.var 4)) (.mul (.add (.var 1) (.var 3)) (.var 5)))
        (e₂ := .add (.sub (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
                    (.sub (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5)))) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im, z.re, z.im])
        (e₁ := .add (.mul (.add (.var 0) (.var 2)) (.var 5)) (.mul (.add (.var 1) (.var 3)) (.var 4)))
        (e₂ := .add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))
                    (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4)))) rfl
  one_smul x := by ext <;> exact CommRingOps.one_mul _
  mul_smul c d x := by ext <;> exact CommRingOps.mul_assoc _ _ _
  smul_add c x y := by ext <;> exact CommRingOps.left_distrib _ _ _
  add_smul c d x := by ext <;> exact cr_right_distrib _ _ _
  smul_mul_left c x y := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.re, x.im, y.re, y.im])
        (e₁ := .sub (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4)))
        (e₂ := .mul (.var 0) (.sub (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.re, x.im, y.re, y.im])
        (e₁ := .add (.mul (.mul (.var 0) (.var 1)) (.var 4)) (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) rfl
  smul_mul_right c x y := by
    ext
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.re, x.im, y.re, y.im])
        (e₁ := .sub (.mul (.var 1) (.mul (.var 0) (.var 3))) (.mul (.var 2) (.mul (.var 0) (.var 4))))
        (e₂ := .mul (.var 0) (.sub (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) rfl
    · exact RExpr.eq_of_norm_eq (envGet (0 : F) [c, x.re, x.im, y.re, y.im])
        (e₁ := .add (.mul (.var 1) (.mul (.var 0) (.var 4))) (.mul (.var 2) (.mul (.var 0) (.var 3))))
        (e₂ := .mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) rfl

theorem isComm : IsCommAlg (alg F) := by
  intro x y
  ext
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im])
      (e₁ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (e₂ := .sub (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))) rfl
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [x.re, x.im, y.re, y.im])
      (e₁ := .add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
      (e₂ := .add (.mul (.var 2) (.var 1)) (.mul (.var 3) (.var 0))) rfl

theorem normSq_ne_zero {z : ComplexOver F} (hz : z ≠ zero) : normSq z ≠ 0 := by
  intro h
  obtain ⟨hre, him⟩ := sum_two_sq_eq_zeroF h
  apply hz
  ext <;> assumption

theorem mul_inv_cancelC {z : ComplexOver F} (hz : z ≠ zero) : mul z (inv z) = one := by
  have hn : normSq z ≠ 0 := normSq_ne_zero hz
  ext
  · change z.re * ((normSq z)⁻¹ * z.re) - z.im * ((normSq z)⁻¹ * -z.im) = 1
    calc
      z.re * ((normSq z)⁻¹ * z.re) - z.im * ((normSq z)⁻¹ * -z.im)
          = (z.re * z.re + z.im * z.im) * (normSq z)⁻¹ :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [z.re, z.im, (normSq z)⁻¹])
              (e₁ := .sub (.mul (.var 0) (.mul (.var 2) (.var 0)))
                          (.mul (.var 1) (.mul (.var 2) (.neg (.var 1)))))
              (e₂ := .mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.var 2)) rfl
      _ = normSq z * (normSq z)⁻¹ := rfl
      _ = 1 := FormallyRealField.mul_inv_cancel _ hn
  · change z.re * ((normSq z)⁻¹ * -z.im) + z.im * ((normSq z)⁻¹ * z.re) = 0
    exact RExpr.eq_of_norm_eq (envGet (0 : F) [z.re, z.im, (normSq z)⁻¹])
      (e₁ := .add (.mul (.var 0) (.mul (.var 2) (.neg (.var 1))))
                  (.mul (.var 1) (.mul (.var 2) (.var 0))))
      (e₂ := .zero) rfl

theorem isDivision : IsDivisionAlg (alg F) := by
  refine ⟨fun h => one_ne_zeroF (congrArg ComplexOver.re h), fun z hz => ⟨inv z, ?_, ?_⟩⟩
  · exact mul_inv_cancelC hz
  · rw [isComm (inv z) z]
    exact mul_inv_cancelC hz

theorem unitI_sq : mul (unitI (F := F)) unitI = neg one := by
  ext
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .sub (.mul .zero .zero) (.mul .one .one)) (e₂ := .neg .one) rfl
  · exact RExpr.eq_of_norm_eq (envGet (0 : F) [])
      (e₁ := .add (.mul .zero .one) (.mul .one .zero)) (e₂ := .neg .zero) rfl

instance commRingOps : CommRingOps (ComplexOver F) where
  add := add
  sub := sub
  mul := mul
  neg := neg
  zero := zero
  one := one
  add_assoc := (alg F).add_assoc
  add_comm := (alg F).add_comm
  zero_add := (alg F).zero_add
  neg_add_cancel := (alg F).neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  mul_assoc := (alg F).mul_assoc
  mul_comm := isComm
  one_mul := (alg F).one_mul
  left_distrib := (alg F).left_distrib

end ComplexOver

/-- 3. Quaternionic type: Hamilton's quaternion division algebra `QuatOver F` of `F`-dimension 4. -/
@[ext]
structure QuatOver (F : Type) where
  w : F
  x : F
  y : F
  z : F

namespace QuatOver

def zero : QuatOver F := ⟨0, 0, 0, 0⟩
def one : QuatOver F := ⟨1, 0, 0, 0⟩
def qi : QuatOver F := ⟨0, 1, 0, 0⟩
def qj : QuatOver F := ⟨0, 0, 1, 0⟩
def qk : QuatOver F := ⟨0, 0, 0, 1⟩

def add (p q : QuatOver F) : QuatOver F :=
  ⟨p.w + q.w, p.x + q.x, p.y + q.y, p.z + q.z⟩

def neg (p : QuatOver F) : QuatOver F :=
  ⟨-p.w, -p.x, -p.y, -p.z⟩

def smul (c : F) (p : QuatOver F) : QuatOver F :=
  ⟨c * p.w, c * p.x, c * p.y, c * p.z⟩

def mul (p q : QuatOver F) : QuatOver F :=
  ⟨p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z,
   p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y,
   p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x,
   p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w⟩

def conj (p : QuatOver F) : QuatOver F :=
  ⟨p.w, -p.x, -p.y, -p.z⟩

def normSq (p : QuatOver F) : F :=
  p.w * p.w + p.x * p.x + p.y * p.y + p.z * p.z

def inv (p : QuatOver F) : QuatOver F :=
  smul (normSq p)⁻¹ (conj p)

def qMulW (pw px py pz qw qx qy qz : RExpr) : RExpr :=
  .sub (.sub (.sub (.mul pw qw) (.mul px qx)) (.mul py qy)) (.mul pz qz)
def qMulX (pw px py pz qw qx qy qz : RExpr) : RExpr :=
  .sub (.add (.add (.mul pw qx) (.mul px qw)) (.mul py qz)) (.mul pz qy)
def qMulY (pw px py pz qw qx qy qz : RExpr) : RExpr :=
  .add (.add (.sub (.mul pw qy) (.mul px qz)) (.mul py qw)) (.mul pz qx)
def qMulZ (pw px py pz qw qx qy qz : RExpr) : RExpr :=
  .add (.sub (.add (.mul pw qz) (.mul px qy)) (.mul py qx)) (.mul pz qw)

/-- Cayley–Dickson representation `(⟨w, x⟩, ⟨y, z⟩)` for ultra-fast quaternion associativity. -/
private def cdFst (p : QuatOver F) : ComplexOver F := ⟨p.w, p.x⟩
private def cdSnd (p : QuatOver F) : ComplexOver F := ⟨p.y, p.z⟩

private theorem cdFst_mul (p q : QuatOver F) :
    cdFst (mul p q) =
      ComplexOver.sub (ComplexOver.mul (cdFst p) (cdFst q))
                      (ComplexOver.mul (ComplexOver.conj (cdSnd q)) (cdSnd p)) := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulW (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
      (e₂ := .add (.sub (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
                  (.neg (.sub (.mul (.var 6) (.var 2)) (.mul (.neg (.var 7)) (.var 3))))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulX (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
      (e₂ := .add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4)))
                  (.neg (.add (.mul (.var 6) (.var 3)) (.mul (.neg (.var 7)) (.var 2))))) rfl

private theorem cdSnd_mul (p q : QuatOver F) :
    cdSnd (mul p q) =
      ComplexOver.add (ComplexOver.mul (cdSnd q) (cdFst p))
                      (ComplexOver.mul (cdSnd p) (ComplexOver.conj (cdFst q))) := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulY (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
      (e₂ := .add (.sub (.mul (.var 6) (.var 0)) (.mul (.var 7) (.var 1)))
                  (.sub (.mul (.var 2) (.var 4)) (.mul (.var 3) (.neg (.var 5))))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulZ (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7))
      (e₂ := .add (.add (.mul (.var 6) (.var 1)) (.mul (.var 7) (.var 0)))
                  (.add (.mul (.var 2) (.neg (.var 5))) (.mul (.var 3) (.var 4)))) rfl

private theorem c_conj_add (z w : ComplexOver F) :
    ComplexOver.conj (ComplexOver.add z w) =
      ComplexOver.add (ComplexOver.conj z) (ComplexOver.conj w) := by
  ext
  · rfl
  · exact cr_neg_add_distrib z.im w.im

private theorem c_conj_sub (z w : ComplexOver F) :
    ComplexOver.conj (ComplexOver.sub z w) =
      ComplexOver.sub (ComplexOver.conj z) (ComplexOver.conj w) := by
  ext
  · rfl
  · exact cr_neg_add_distrib z.im (-w.im)

private theorem c_conj_mul (z w : ComplexOver F) :
    ComplexOver.conj (ComplexOver.mul z w) =
      ComplexOver.mul (ComplexOver.conj z) (ComplexOver.conj w) := by
  let env := envGet (0 : F) [z.re, z.im, w.re, w.im]
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .sub (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (e₂ := .sub (.mul (.var 0) (.var 2)) (.mul (.neg (.var 1)) (.neg (.var 3)))) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .neg (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
      (e₂ := .add (.mul (.var 0) (.neg (.var 3))) (.mul (.neg (.var 1)) (.var 2))) rfl

private theorem c_conj_conj (z : ComplexOver F) :
    ComplexOver.conj (ComplexOver.conj z) = z := by
  ext
  · rfl
  · exact cr_neg_neg z.im

theorem mul_assocQ (p q r : QuatOver F) : mul (mul p q) r = mul p (mul q r) := by
  have h1 : cdFst (mul (mul p q) r) = cdFst (mul p (mul q r)) := by
    rw [cdFst_mul, cdFst_mul, cdSnd_mul, cdFst_mul, cdFst_mul, cdSnd_mul,
        c_conj_add, c_conj_mul, c_conj_mul, c_conj_conj]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdSnd p, cdFst q, cdSnd q, cdFst r, cdSnd r,
         ComplexOver.conj (cdFst p), ComplexOver.conj (cdSnd p),
         ComplexOver.conj (cdFst q), ComplexOver.conj (cdSnd q),
         ComplexOver.conj (cdFst r), ComplexOver.conj (cdSnd r)])
      (e₁ := .sub (.mul (.sub (.mul (.var 0) (.var 2)) (.mul (.var 9) (.var 1))) (.var 4))
                  (.mul (.var 11) (.add (.mul (.var 3) (.var 0)) (.mul (.var 1) (.var 8)))))
      (e₂ := .sub (.mul (.var 0) (.sub (.mul (.var 2) (.var 4)) (.mul (.var 11) (.var 3))))
                  (.mul (.add (.mul (.var 11) (.var 8)) (.mul (.var 9) (.var 4))) (.var 1))) rfl
  have h2 : cdSnd (mul (mul p q) r) = cdSnd (mul p (mul q r)) := by
    rw [cdSnd_mul, cdFst_mul, cdSnd_mul, cdSnd_mul, cdFst_mul, cdSnd_mul,
        c_conj_sub, c_conj_mul, c_conj_mul, c_conj_conj]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdSnd p, cdFst q, cdSnd q, cdFst r, cdSnd r,
         ComplexOver.conj (cdFst p), ComplexOver.conj (cdSnd p),
         ComplexOver.conj (cdFst q), ComplexOver.conj (cdSnd q),
         ComplexOver.conj (cdFst r), ComplexOver.conj (cdSnd r)])
      (e₁ := .add (.mul (.var 5) (.sub (.mul (.var 0) (.var 2)) (.mul (.var 9) (.var 1))))
                  (.mul (.add (.mul (.var 3) (.var 0)) (.mul (.var 1) (.var 8))) (.var 10)))
      (e₂ := .add (.mul (.add (.mul (.var 5) (.var 2)) (.mul (.var 3) (.var 10))) (.var 0))
                  (.mul (.var 1) (.sub (.mul (.var 8) (.var 10)) (.mul (.var 5) (.var 9))))) rfl
  ext
  · exact congrArg ComplexOver.re h1
  · exact congrArg ComplexOver.im h1
  · exact congrArg ComplexOver.re h2
  · exact congrArg ComplexOver.im h2

theorem one_mulQ (p : QuatOver F) : mul one p = p := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z]
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulW .one .zero .zero .zero (.var 0) (.var 1) (.var 2) (.var 3)) (e₂ := .var 0) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulX .one .zero .zero .zero (.var 0) (.var 1) (.var 2) (.var 3)) (e₂ := .var 1) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulY .one .zero .zero .zero (.var 0) (.var 1) (.var 2) (.var 3)) (e₂ := .var 2) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulZ .one .zero .zero .zero (.var 0) (.var 1) (.var 2) (.var 3)) (e₂ := .var 3) rfl

theorem mul_oneQ (p : QuatOver F) : mul p one = p := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z]
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulW (.var 0) (.var 1) (.var 2) (.var 3) .one .zero .zero .zero) (e₂ := .var 0) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulX (.var 0) (.var 1) (.var 2) (.var 3) .one .zero .zero .zero) (e₂ := .var 1) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulY (.var 0) (.var 1) (.var 2) (.var 3) .one .zero .zero .zero) (e₂ := .var 2) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulZ (.var 0) (.var 1) (.var 2) (.var 3) .one .zero .zero .zero) (e₂ := .var 3) rfl

theorem left_distribQ (p q r : QuatOver F) : mul p (add q r) = add (mul p q) (mul p r) := by
  have h1 : cdFst (mul p (add q r)) = ComplexOver.add (cdFst (mul p q)) (cdFst (mul p r)) := by
    rw [cdFst_mul, cdFst_mul, cdFst_mul]
    have hc : ComplexOver.conj (cdSnd (add q r)) =
        ComplexOver.add (ComplexOver.conj (cdSnd q)) (ComplexOver.conj (cdSnd r)) :=
      c_conj_add (cdSnd q) (cdSnd r)
    have hf : cdFst (add q r) = ComplexOver.add (cdFst q) (cdFst r) := rfl
    rw [hc, hf]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdSnd p, cdFst q, cdFst r, ComplexOver.conj (cdSnd q), ComplexOver.conj (cdSnd r)])
      (e₁ := .sub (.mul (.var 0) (.add (.var 2) (.var 3))) (.mul (.add (.var 4) (.var 5)) (.var 1)))
      (e₂ := .add (.sub (.mul (.var 0) (.var 2)) (.mul (.var 4) (.var 1)))
                  (.sub (.mul (.var 0) (.var 3)) (.mul (.var 5) (.var 1)))) rfl
  have h2 : cdSnd (mul p (add q r)) = ComplexOver.add (cdSnd (mul p q)) (cdSnd (mul p r)) := by
    rw [cdSnd_mul, cdSnd_mul, cdSnd_mul]
    have hc : ComplexOver.conj (cdFst (add q r)) =
        ComplexOver.add (ComplexOver.conj (cdFst q)) (ComplexOver.conj (cdFst r)) :=
      c_conj_add (cdFst q) (cdFst r)
    have hs : cdSnd (add q r) = ComplexOver.add (cdSnd q) (cdSnd r) := rfl
    rw [hc, hs]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdSnd p, cdSnd q, cdSnd r, ComplexOver.conj (cdFst q), ComplexOver.conj (cdFst r)])
      (e₁ := .add (.mul (.add (.var 2) (.var 3)) (.var 0)) (.mul (.var 1) (.add (.var 4) (.var 5))))
      (e₂ := .add (.add (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 4)))
                  (.add (.mul (.var 3) (.var 0)) (.mul (.var 1) (.var 5)))) rfl
  ext
  · exact congrArg ComplexOver.re h1
  · exact congrArg ComplexOver.im h1
  · exact congrArg ComplexOver.re h2
  · exact congrArg ComplexOver.im h2

theorem right_distribQ (p q r : QuatOver F) : mul (add p q) r = add (mul p r) (mul q r) := by
  have h1 : cdFst (mul (add p q) r) = ComplexOver.add (cdFst (mul p r)) (cdFst (mul q r)) := by
    rw [cdFst_mul, cdFst_mul, cdFst_mul]
    have hf : cdFst (add p q) = ComplexOver.add (cdFst p) (cdFst q) := rfl
    have hs : cdSnd (add p q) = ComplexOver.add (cdSnd p) (cdSnd q) := rfl
    rw [hf, hs]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdFst q, cdSnd p, cdSnd q, cdFst r, ComplexOver.conj (cdSnd r)])
      (e₁ := .sub (.mul (.add (.var 0) (.var 1)) (.var 4)) (.mul (.var 5) (.add (.var 2) (.var 3))))
      (e₂ := .add (.sub (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 2)))
                  (.sub (.mul (.var 1) (.var 4)) (.mul (.var 5) (.var 3)))) rfl
  have h2 : cdSnd (mul (add p q) r) = ComplexOver.add (cdSnd (mul p r)) (cdSnd (mul q r)) := by
    rw [cdSnd_mul, cdSnd_mul, cdSnd_mul]
    have hf : cdFst (add p q) = ComplexOver.add (cdFst p) (cdFst q) := rfl
    have hs : cdSnd (add p q) = ComplexOver.add (cdSnd p) (cdSnd q) := rfl
    rw [hf, hs]
    exact RExpr.eq_of_norm_eq
      (envGet (ComplexOver.zero (F := F))
        [cdFst p, cdFst q, cdSnd p, cdSnd q, cdSnd r, ComplexOver.conj (cdFst r)])
      (e₁ := .add (.mul (.var 4) (.add (.var 0) (.var 1))) (.mul (.add (.var 2) (.var 3)) (.var 5)))
      (e₂ := .add (.add (.mul (.var 4) (.var 0)) (.mul (.var 2) (.var 5)))
                  (.add (.mul (.var 4) (.var 1)) (.mul (.var 3) (.var 5)))) rfl
  ext
  · exact congrArg ComplexOver.re h1
  · exact congrArg ComplexOver.im h1
  · exact congrArg ComplexOver.re h2
  · exact congrArg ComplexOver.im h2

theorem smul_mul_leftQ (c : F) (p q : QuatOver F) : mul (smul c p) q = smul c (mul p q) := by
  let env := envGet (0 : F) [c, p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z]
  let cv := RExpr.var 0
  let pw := RExpr.var 1; let px := RExpr.var 2; let py := RExpr.var 3; let pz := RExpr.var 4
  let qw := RExpr.var 5; let qx := RExpr.var 6; let qy := RExpr.var 7; let qz := RExpr.var 8
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulW (.mul cv pw) (.mul cv px) (.mul cv py) (.mul cv pz) qw qx qy qz)
      (e₂ := .mul cv (qMulW pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulX (.mul cv pw) (.mul cv px) (.mul cv py) (.mul cv pz) qw qx qy qz)
      (e₂ := .mul cv (qMulX pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulY (.mul cv pw) (.mul cv px) (.mul cv py) (.mul cv pz) qw qx qy qz)
      (e₂ := .mul cv (qMulY pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulZ (.mul cv pw) (.mul cv px) (.mul cv py) (.mul cv pz) qw qx qy qz)
      (e₂ := .mul cv (qMulZ pw px py pz qw qx qy qz)) rfl

theorem smul_mul_rightQ (c : F) (p q : QuatOver F) : mul p (smul c q) = smul c (mul p q) := by
  let env := envGet (0 : F) [c, p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z]
  let cv := RExpr.var 0
  let pw := RExpr.var 1; let px := RExpr.var 2; let py := RExpr.var 3; let pz := RExpr.var 4
  let qw := RExpr.var 5; let qx := RExpr.var 6; let qy := RExpr.var 7; let qz := RExpr.var 8
  ext
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulW pw px py pz (.mul cv qw) (.mul cv qx) (.mul cv qy) (.mul cv qz))
      (e₂ := .mul cv (qMulW pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulX pw px py pz (.mul cv qw) (.mul cv qx) (.mul cv qy) (.mul cv qz))
      (e₂ := .mul cv (qMulX pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulY pw px py pz (.mul cv qw) (.mul cv qx) (.mul cv qy) (.mul cv qz))
      (e₂ := .mul cv (qMulY pw px py pz qw qx qy qz)) rfl
  · exact RExpr.eq_of_norm_eq env (e₁ := qMulZ pw px py pz (.mul cv qw) (.mul cv qx) (.mul cv qy) (.mul cv qz))
      (e₂ := .mul cv (qMulZ pw px py pz qw qx qy qz)) rfl

def alg (F : Type) [FormallyRealField F] : Alg F (QuatOver F) where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  smul := smul
  add_assoc p q r := by ext <;> exact CommRingOps.add_assoc _ _ _
  add_comm p q := by ext <;> exact CommRingOps.add_comm _ _
  zero_add p := by ext <;> exact CommRingOps.zero_add _
  neg_add_cancel p := by ext <;> exact CommRingOps.neg_add_cancel _
  mul_assoc := mul_assocQ
  one_mul := one_mulQ
  mul_one := mul_oneQ
  left_distrib := left_distribQ
  right_distrib := right_distribQ
  one_smul p := by ext <;> exact CommRingOps.one_mul _
  mul_smul c d p := by ext <;> exact CommRingOps.mul_assoc _ _ _
  smul_add c p q := by ext <;> exact CommRingOps.left_distrib _ _ _
  add_smul c d p := by ext <;> exact cr_right_distrib _ _ _
  smul_mul_left := smul_mul_leftQ
  smul_mul_right := smul_mul_rightQ

theorem conj_mul (p q : QuatOver F) : conj (mul p q) = mul (conj q) (conj p) := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z, q.w, q.x, q.y, q.z]
  let pw := RExpr.var 0; let px := RExpr.var 1; let py := RExpr.var 2; let pz := RExpr.var 3
  let qw := RExpr.var 4; let qx := RExpr.var 5; let qy := RExpr.var 6; let qz := RExpr.var 7
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulW pw px py pz qw qx qy qz)
      (e₂ := qMulW qw (.neg qx) (.neg qy) (.neg qz) pw (.neg px) (.neg py) (.neg pz)) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .neg (qMulX pw px py pz qw qx qy qz))
      (e₂ := qMulX qw (.neg qx) (.neg qy) (.neg qz) pw (.neg px) (.neg py) (.neg pz)) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .neg (qMulY pw px py pz qw qx qy qz))
      (e₂ := qMulY qw (.neg qx) (.neg qy) (.neg qz) pw (.neg px) (.neg py) (.neg pz)) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := .neg (qMulZ pw px py pz qw qx qy qz))
      (e₂ := qMulZ qw (.neg qx) (.neg qy) (.neg qz) pw (.neg px) (.neg py) (.neg pz)) rfl

theorem conj_conj (p : QuatOver F) : conj (conj p) = p := by
  ext
  · rfl
  · exact cr_neg_neg p.x
  · exact cr_neg_neg p.y
  · exact cr_neg_neg p.z

theorem mul_conj (p : QuatOver F) : mul p (conj p) = smul (normSq p) one := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z]
  let pw := RExpr.var 0; let px := RExpr.var 1; let py := RExpr.var 2; let pz := RExpr.var 3
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulW pw px py pz pw (.neg px) (.neg py) (.neg pz))
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .one) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulX pw px py pz pw (.neg px) (.neg py) (.neg pz))
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulY pw px py pz pw (.neg px) (.neg py) (.neg pz))
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulZ pw px py pz pw (.neg px) (.neg py) (.neg pz))
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl

theorem conj_mul_self (p : QuatOver F) : mul (conj p) p = smul (normSq p) one := by
  let env := envGet (0 : F) [p.w, p.x, p.y, p.z]
  let pw := RExpr.var 0; let px := RExpr.var 1; let py := RExpr.var 2; let pz := RExpr.var 3
  ext
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulW pw (.neg px) (.neg py) (.neg pz) pw px py pz)
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .one) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulX pw (.neg px) (.neg py) (.neg pz) pw px py pz)
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulY pw (.neg px) (.neg py) (.neg pz) pw px py pz)
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl
  · exact RExpr.eq_of_norm_eq env
      (e₁ := qMulZ pw (.neg px) (.neg py) (.neg pz) pw px py pz)
      (e₂ := .mul (.add (.add (.add (.mul pw pw) (.mul px px)) (.mul py py)) (.mul pz pz)) .zero) rfl

theorem normSq_ne_zero {p : QuatOver F} (hp : p ≠ zero) : normSq p ≠ 0 := by
  intro h
  obtain ⟨hw, hx, hy, hz⟩ := FormallyRealField.sum_four_sq_eq_zero p.w p.x p.y p.z h
  apply hp
  ext <;> assumption

theorem isDivision : IsDivisionAlg (alg F) := by
  refine ⟨fun h => one_ne_zeroF (congrArg QuatOver.w h), fun p hp => ⟨inv p, ?_, ?_⟩⟩
  · have hn : normSq p ≠ 0 := normSq_ne_zero hp
    change (alg F).mul p ((alg F).smul (normSq p)⁻¹ (conj p)) = (alg F).one
    rw [(alg F).smul_mul_right]
    change (alg F).smul (normSq p)⁻¹ (mul p (conj p)) = (alg F).one
    rw [mul_conj]
    change (alg F).smul (normSq p)⁻¹ ((alg F).smul (normSq p) (alg F).one) = (alg F).one
    rw [← (alg F).mul_smul, inv_mul_cancelF hn, (alg F).one_smul]
  · have hn : normSq p ≠ 0 := normSq_ne_zero hp
    change (alg F).mul ((alg F).smul (normSq p)⁻¹ (conj p)) p = (alg F).one
    rw [(alg F).smul_mul_left]
    change (alg F).smul (normSq p)⁻¹ (mul (conj p) p) = (alg F).one
    rw [conj_mul_self]
    change (alg F).smul (normSq p)⁻¹ ((alg F).smul (normSq p) (alg F).one) = (alg F).one
    rw [← (alg F).mul_smul, inv_mul_cancelF hn, (alg F).one_smul]

theorem qi_mul_qj_ne_qj_mul_qi : mul (qi (F := F)) qj ≠ mul qj qi := by
  intro h
  have hz : (mul (qi (F := F)) qj).z = (mul qj qi).z := congrArg QuatOver.z h
  have htwo : twoF F = 0 := by
    calc
      twoF F = ((1 : F) + 1) := rfl
      _ = (mul (qi (F := F)) qj).z - (mul qj qi).z :=
            RExpr.eq_of_norm_eq (envGet (0 : F) [])
              (e₁ := .add .one .one)
              (e₂ := .sub (qMulZ .zero .one .zero .zero .zero .zero .one .zero)
                          (qMulZ .zero .zero .one .zero .zero .one .zero .zero)) rfl
      _ = (mul qj qi).z - (mul qj qi).z := by rw [hz]
      _ = 0 := RExpr.eq_of_norm_eq (envGet (0 : F) [(mul (F := F) qj qi).z])
                 (e₁ := .sub (.var 0) (.var 0)) (e₂ := .zero) rfl
  exact two_ne_zeroF htwo

theorem not_isComm : ¬ IsCommAlg (alg F) :=
  fun h => qi_mul_qj_ne_qj_mul_qi (h qi qj)

end QuatOver

/-! ## Pairwise Non-Isomorphism of the Three Division Algebra Types (`F`, `ComplexOver F`, `QuatOver F`) -/

theorem not_algIso_real_complex :
    ¬ Nonempty (AlgIso F (realAlg F) (ComplexOver.alg F)) := by
  rintro ⟨e⟩
  let u : F := e.symm.toFun ComplexOver.unitI
  have hu2 : (realAlg F).mul u u = (realAlg F).neg (realAlg F).one := by
    calc
      (realAlg F).mul u u
          = e.symm.toFun ((ComplexOver.alg F).mul ComplexOver.unitI ComplexOver.unitI) :=
            (e.symm.map_mul _ _).symm
      _ = e.symm.toFun ((ComplexOver.alg F).neg (ComplexOver.alg F).one) := by
            change e.symm.toFun (ComplexOver.mul ComplexOver.unitI ComplexOver.unitI) =
              e.symm.toFun (ComplexOver.neg ComplexOver.one)
            rw [ComplexOver.unitI_sq]
      _ = (realAlg F).neg (e.symm.toFun (ComplexOver.alg F).one) :=
            algHom_map_neg e.symm.toAlgHom _
      _ = (realAlg F).neg (realAlg F).one := by rw [e.symm.map_one]
  have hsq : u * u + 1 = 0 := by
    change u * u = -1 at hu2
    rw [hu2, CommRingOps.neg_add_cancel]
  exact sq_add_one_ne_zeroF u hsq

theorem not_algIso_real_quat :
    ¬ Nonempty (AlgIso F (realAlg F) (QuatOver.alg F)) := by
  rintro ⟨e⟩
  exact QuatOver.not_isComm (isCommAlg_of_algIso e realAlg_isComm)

theorem not_algIso_complex_quat :
    ¬ Nonempty (AlgIso F (ComplexOver.alg F) (QuatOver.alg F)) := by
  rintro ⟨e⟩
  exact QuatOver.not_isComm (isCommAlg_of_algIso e ComplexOver.isComm)

/-- Over any formally real field `F` (in particular `ℝ` and `ℚ`), the three Frobenius
    division algebras `F`, `ComplexOver F`, and `QuatOver F` are all division `F`-algebras
    and are pairwise non-isomorphic. -/
theorem three_division_types_pairwise_noniso :
    IsDivisionAlg (realAlg F) ∧
    IsDivisionAlg (ComplexOver.alg F) ∧
    IsDivisionAlg (QuatOver.alg F) ∧
    ¬ Nonempty (AlgIso F (realAlg F) (ComplexOver.alg F)) ∧
    ¬ Nonempty (AlgIso F (realAlg F) (QuatOver.alg F)) ∧
    ¬ Nonempty (AlgIso F (ComplexOver.alg F) (QuatOver.alg F)) :=
  ⟨realAlg_isDivision, ComplexOver.isDivision, QuatOver.isDivision,
   not_algIso_real_complex, not_algIso_real_quat, not_algIso_complex_quat⟩

end AlgBasic

end Conjecture00000007605
