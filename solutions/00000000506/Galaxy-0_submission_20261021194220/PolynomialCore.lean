import Std

/-! Concrete finitely supported bivariate polynomials with coefficients in F₂.
`false` is zero, `true` is one, addition is exclusive-or, and multiplication
of coefficients is conjunction. No degree bound is part of polynomial equality.
-/
namespace TLMC506

structure Poly where
  coeff : Nat → Nat → Bool
  finite : ∃ N : Nat, ∀ i j, N ≤ i + j → coeff i j = false

@[ext] theorem Poly.ext {p q : Poly}
    (h : ∀ i j, p.coeff i j = q.coeff i j) : p = q := by
  cases p with | mk pc pf =>
    cases q with | mk qc qf =>
      have hc : pc = qc := funext fun i => funext fun j => h i j
      cases hc
      rfl

def zero : Poly := ⟨fun _ _ => false, ⟨0, by intros; rfl⟩⟩

def add (p q : Poly) : Poly where
  coeff i j := p.coeff i j ^^ q.coeff i j
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    obtain ⟨M, hM⟩ := q.finite
    refine ⟨N + M, ?_⟩
    intro i j hij
    rw [hN i j (by omega), hM i j (by omega)]
    rfl

def one : Poly where
  coeff i j := decide (i = 0 ∧ j = 0)
  finite := by
    refine ⟨1, ?_⟩
    intro i j hij
    simp only [decide_eq_false_iff_not]
    omega

def xMul (p : Poly) : Poly where
  coeff i j := match i with | 0 => false | i+1 => p.coeff i j
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N + 1, ?_⟩
    intro i j hij
    cases i with
    | zero => rfl
    | succ i => exact hN i j (by omega)

def yMul (p : Poly) : Poly where
  coeff i j := match j with | 0 => false | j+1 => p.coeff i j
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N + 1, ?_⟩
    intro i j hij
    cases j with
    | zero => rfl
    | succ j => exact hN i j (by omega)

def X : Poly := xMul one
def Y : Poly := yMul one

@[simp] theorem zero_coeff (i j : Nat) : zero.coeff i j = false := rfl
@[simp] theorem add_coeff (p q : Poly) (i j : Nat) :
    (add p q).coeff i j = (p.coeff i j ^^ q.coeff i j) := rfl
@[simp] theorem one_coeff (i j : Nat) : one.coeff i j = decide (i = 0 ∧ j = 0) := rfl
@[simp] theorem xMul_coeff_zero (p : Poly) (j : Nat) :
    (xMul p).coeff 0 j = false := rfl
@[simp] theorem xMul_coeff_succ (p : Poly) (i j : Nat) :
    (xMul p).coeff (i+1) j = p.coeff i j := rfl
@[simp] theorem yMul_coeff_zero (p : Poly) (i : Nat) :
    (yMul p).coeff i 0 = false := rfl
@[simp] theorem yMul_coeff_succ (p : Poly) (i j : Nat) :
    (yMul p).coeff i (j+1) = p.coeff i j := rfl

theorem add_comm (p q : Poly) : add p q = add q p := by
  apply Poly.ext; intro i j; exact Bool.xor_comm _ _
theorem add_assoc (p q r : Poly) : add (add p q) r = add p (add q r) := by
  apply Poly.ext; intro i j; exact Bool.xor_assoc _ _ _
@[simp] theorem add_zero (p : Poly) : add p zero = p := by
  apply Poly.ext; intro i j; exact Bool.xor_false _
@[simp] theorem zero_add (p : Poly) : add zero p = p := by
  apply Poly.ext; intro i j; exact Bool.false_xor _
@[simp] theorem add_self (p : Poly) : add p p = zero := by
  apply Poly.ext; intro i j; exact Bool.xor_self _
@[simp] theorem xMul_zero : xMul zero = zero := by
  apply Poly.ext; intro i j; cases i <;> rfl
@[simp] theorem yMul_zero : yMul zero = zero := by
  apply Poly.ext; intro i j; cases j <;> rfl

theorem xMul_add (p q : Poly) : xMul (add p q) = add (xMul p) (xMul q) := by
  apply Poly.ext; intro i j; cases i <;> rfl
theorem yMul_add (p q : Poly) : yMul (add p q) = add (yMul p) (yMul q) := by
  apply Poly.ext; intro i j; cases j <;> rfl
theorem xMul_yMul (p : Poly) : xMul (yMul p) = yMul (xMul p) := by
  apply Poly.ext; intro i j; cases i <;> cases j <;> rfl

theorem xMul_injective {p q : Poly} (h : xMul p = xMul q) : p = q := by
  apply Poly.ext; intro i j
  exact congrArg (fun r : Poly => r.coeff (i+1) j) h
theorem yMul_injective {p q : Poly} (h : yMul p = yMul q) : p = q := by
  apply Poly.ext; intro i j
  exact congrArg (fun r : Poly => r.coeff i (j+1)) h

theorem xor_eq_false_iff (a b : Bool) : (a ^^ b) = false ↔ a = b := by
  cases a <;> cases b <;> decide
theorem add_eq_zero_iff (p q : Poly) : add p q = zero ↔ p = q := by
  constructor
  · intro h
    apply Poly.ext; intro i j
    exact (xor_eq_false_iff _ _).mp (congrArg (fun r : Poly => r.coeff i j) h)
  · intro h; subst q; exact add_self p

end TLMC506
