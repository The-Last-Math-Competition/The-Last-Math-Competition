/-
  SpinorMinimalIdeals/PolyNorm.lean
  Self-contained verified multivariate polynomial normalizer over `Int`
  in Core Lean 4.19.0 (zero external dependencies, zero `native_decide`).
  Uses pure structural `Bool`/`Ordering` helpers so `e1.norm = e2.norm` reduces
  instantly in the Lean kernel via `rfl`.
-/

namespace SpinorMinimalIdeals.PolyNorm

/-- Pure structural zero test on `Int` (avoids `Decidable` overhead in kernel `rfl`). -/
def isZeroInt : Int → Bool
  | .ofNat 0 => true
  | _ => false

theorem isZeroInt_eq_true_iff : ∀ (c : Int), isZeroInt c = true ↔ c = 0
  | .ofNat 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | .ofNat (_ + 1) => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | .negSucc _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- Pure structural `≤` on `Nat`. -/
def leNat : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | x + 1, y + 1 => leNat x y

/-- Pure structural comparison on `Nat`. -/
def cmpNat : Nat → Nat → Ordering
  | 0, 0 => .eq
  | 0, _ + 1 => .lt
  | _ + 1, 0 => .gt
  | x + 1, y + 1 => cmpNat x y

theorem cmpNat_eq_iff : ∀ (x y : Nat), cmpNat x y = .eq ↔ x = y
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 0, _ + 1 => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ + 1, 0 => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | x + 1, y + 1 => by
      simp only [cmpNat]
      constructor
      · intro h; rw [(cmpNat_eq_iff x y).mp h]
      · intro h; injection h with hxy; exact (cmpNat_eq_iff x y).mpr hxy

/-- Variable lookup in an `Int` environment (defaults to `0` out of bounds). -/
def evalVar : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => evalVar xs i

/-- Evaluate a monomial (sorted list of variable indices) as a product in `Int`. -/
def evalMonom (env : List Int) : List Nat → Int
  | [] => 1
  | v :: vs => evalVar env v * evalMonom env vs

/-- Insert one variable index into a sorted variable-index list (pure structural recursion). -/
def insertVar (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      match leNat x y with
      | true => x :: y :: ys
      | false => y :: insertVar x ys

theorem evalMonom_insertVar (env : List Int) (x : Nat) :
    ∀ (ys : List Nat), evalMonom env (insertVar x ys) = evalVar env x * evalMonom env ys
  | [] => by simp [insertVar, evalMonom]
  | y :: ys => by
      simp only [insertVar]
      split
      · simp only [evalMonom]
      · simp only [evalMonom, evalMonom_insertVar env x ys]
        ac_rfl

/-- Merge two sorted variable-index lists (pure structural recursion — fast kernel reduction!). -/
def mergeMonom : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => insertVar x (mergeMonom xs ys)

theorem evalMonom_merge (env : List Int) :
    ∀ (m1 m2 : List Nat), evalMonom env (mergeMonom m1 m2) = evalMonom env m1 * evalMonom env m2
  | [], ys => by simp [mergeMonom, evalMonom]
  | x :: xs, ys => by
      simp only [mergeMonom, evalMonom_insertVar, evalMonom_merge env xs ys, evalMonom]
      ac_rfl

/-- Total lexicographic comparison on `List Nat`. -/
def cmpMonom : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
      match cmpNat x y with
      | .lt => .lt
      | .gt => .gt
      | .eq => cmpMonom xs ys

theorem cmpMonom_eq_iff : ∀ (m1 m2 : List Nat), cmpMonom m1 m2 = .eq ↔ m1 = m2
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | x :: xs, y :: ys => by
      simp only [cmpMonom]
      split
      · next hlt =>
        constructor
        · intro h; nomatch h
        · intro heq
          injection heq with hx _
          rw [(cmpNat_eq_iff x y).mpr hx] at hlt
          nomatch hlt
      · next hgt =>
        constructor
        · intro h; nomatch h
        · intro heq
          injection heq with hx _
          rw [(cmpNat_eq_iff x y).mpr hx] at hgt
          nomatch hgt
      · next heq_cmp =>
        have hx : x = y := (cmpNat_eq_iff x y).mp heq_cmp
        subst hx
        constructor
        · intro h; rw [(cmpMonom_eq_iff xs ys).mp h]
        · intro h; injection h with _ hxs; exact (cmpMonom_eq_iff xs ys).mpr hxs

/-- Sparse polynomial: list of `(coeff, monom)` pairs. -/
abbrev Poly := List (Int × List Nat)

def evalPoly (env : List Int) : Poly → Int
  | [] => 0
  | (c, m) :: rest => c * evalMonom env m + evalPoly env rest

def consTerm (c : Int) (m : List Nat) (rest : Poly) : Poly :=
  match isZeroInt c with
  | true => rest
  | false => (c, m) :: rest

theorem evalPoly_consTerm (env : List Int) (c : Int) (m : List Nat) (rest : Poly) :
    evalPoly env (consTerm c m rest) = c * evalMonom env m + evalPoly env rest := by
  unfold consTerm
  split
  · next h =>
    have hc : c = 0 := (isZeroInt_eq_true_iff c).mp h
    subst hc
    simp [evalPoly]
  · rfl

def negPoly : Poly → Poly
  | [] => []
  | (c, m) :: rest => (-c, m) :: negPoly rest

theorem evalPoly_neg (env : List Int) : ∀ (p : Poly), evalPoly env (negPoly p) = - evalPoly env p
  | [] => by simp [negPoly, evalPoly]
  | (c, m) :: rest => by
      simp only [negPoly, evalPoly, evalPoly_neg env rest, Int.neg_mul]
      omega

/-- Insert a single `(c, m)` into a sorted `Poly`. -/
def insertTerm (c : Int) (m : List Nat) : Poly → Poly
  | [] => consTerm c m []
  | (c2, m2) :: rest =>
      match cmpMonom m m2 with
      | .lt => consTerm c m ((c2, m2) :: rest)
      | .gt => (c2, m2) :: insertTerm c m rest
      | .eq => consTerm (c + c2) m rest

theorem evalPoly_insertTerm (env : List Int) (c : Int) (m : List Nat) :
    ∀ (p : Poly), evalPoly env (insertTerm c m p) = c * evalMonom env m + evalPoly env p
  | [] => by rw [insertTerm, evalPoly_consTerm]
  | (c2, m2) :: rest => by
      unfold insertTerm
      split
      · rw [evalPoly_consTerm]
      · simp only [evalPoly, evalPoly_insertTerm env c m rest]
        omega
      · next heq =>
        have hm : m = m2 := (cmpMonom_eq_iff m m2).mp heq
        subst hm
        rw [evalPoly_consTerm]
        simp only [evalPoly, Int.add_mul]
        omega

/-- Multiply a single `(c, m)` across a `Poly`. -/
def mulTermPoly (c : Int) (m : List Nat) : Poly → Poly
  | [] => []
  | (c2, m2) :: rest => insertTerm (c * c2) (mergeMonom m m2) (mulTermPoly c m rest)

theorem evalPoly_mulTerm (env : List Int) (c : Int) (m : List Nat) :
    ∀ (q : Poly), evalPoly env (mulTermPoly c m q) = (c * evalMonom env m) * evalPoly env q
  | [] => by simp [mulTermPoly, evalPoly]
  | (c2, m2) :: rest => by
      simp only [mulTermPoly, evalPoly_insertTerm, evalMonom_merge, evalPoly_mulTerm env c m rest,
                 evalPoly]
      rw [Int.mul_add]
      have h : c * c2 * (evalMonom env m * evalMonom env m2) =
          c * evalMonom env m * (c2 * evalMonom env m2) := by ac_rfl
      rw [h]

/-- Structural polynomial addition (fast kernel reduction via `rfl`). -/
def addPolyFast : Poly → Poly → Poly
  | [], q => q
  | (c, m) :: rest, q => insertTerm c m (addPolyFast rest q)

theorem evalPoly_addFast (env : List Int) :
    ∀ (p q : Poly), evalPoly env (addPolyFast p q) = evalPoly env p + evalPoly env q
  | [], q => by simp [addPolyFast, evalPoly]
  | (c, m) :: rest, q => by
      simp only [addPolyFast, evalPoly_insertTerm, evalPoly_addFast env rest q, evalPoly]
      omega

/-- Structural polynomial multiplication (fast kernel reduction via `rfl`). -/
def mulPolyFast : Poly → Poly → Poly
  | [], _ => []
  | (c, m) :: rest, q => addPolyFast (mulTermPoly c m q) (mulPolyFast rest q)

theorem evalPoly_mulFast (env : List Int) :
    ∀ (p q : Poly), evalPoly env (mulPolyFast p q) = evalPoly env p * evalPoly env q
  | [], q => by simp [mulPolyFast, evalPoly]
  | (c, m) :: rest, q => by
      simp only [mulPolyFast, evalPoly_addFast, evalPoly_mulTerm, evalPoly_mulFast env rest q,
                 evalPoly]
      rw [Int.add_mul]

/-- Polynomial AST with integer constants. -/
inductive PExpr : Type where
  | const : Int → PExpr
  | var   : Nat → PExpr
  | neg   : PExpr → PExpr
  | add   : PExpr → PExpr → PExpr
  | sub   : PExpr → PExpr → PExpr
  | mul   : PExpr → PExpr → PExpr
  deriving Repr

def PExpr.eval (env : List Int) : PExpr → Int
  | .const k => k
  | .var i   => evalVar env i
  | .neg a   => - a.eval env
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env

/-- Canonical normalizer `norm : PExpr → Poly`. -/
def PExpr.norm : PExpr → Poly
  | .const k => consTerm k [] []
  | .var i   => [(1, [i])]
  | .neg a   => negPoly a.norm
  | .add a b => addPolyFast a.norm b.norm
  | .sub a b => addPolyFast a.norm (negPoly b.norm)
  | .mul a b => mulPolyFast a.norm b.norm

theorem PExpr.eval_norm (env : List Int) : ∀ (e : PExpr), evalPoly env e.norm = e.eval env
  | .const k => by
      simp only [PExpr.norm, evalPoly_consTerm, evalMonom, evalPoly, PExpr.eval,
                 Int.mul_one, Int.add_zero]
  | .var i => by
      simp only [PExpr.norm, evalPoly, evalMonom, PExpr.eval,
                 Int.one_mul, Int.mul_one, Int.add_zero]
  | .neg a => by
      simp only [PExpr.norm, evalPoly_neg, PExpr.eval_norm env a, PExpr.eval]
  | .add a b => by
      simp only [PExpr.norm, evalPoly_addFast, PExpr.eval_norm env a, PExpr.eval_norm env b,
                 PExpr.eval]
  | .sub a b => by
      simp only [PExpr.norm, evalPoly_addFast, evalPoly_neg,
                 PExpr.eval_norm env a, PExpr.eval_norm env b, PExpr.eval]
      omega
  | .mul a b => by
      simp only [PExpr.norm, evalPoly_mulFast, PExpr.eval_norm env a, PExpr.eval_norm env b,
                 PExpr.eval]

/-- Reflection lemma over `Int`: if `e1.norm = e2.norm` (by `rfl`), then `e1.eval = e2.eval`. -/
theorem PExpr.eq_of_norm_eq (env : List Int) (e1 e2 : PExpr) (h : e1.norm = e2.norm) :
    e1.eval env = e2.eval env := by
  rw [← PExpr.eval_norm env e1, ← PExpr.eval_norm env e2, h]

end SpinorMinimalIdeals.PolyNorm
