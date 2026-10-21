import Std

/-! Finitely supported coefficient families over the two-element field. -/
namespace ThreePoly

structure Poly where
  coeff : Nat → Nat → Nat → Bool
  finite : ∃ N : Nat, ∀ i j k, N ≤ i + j + k → coeff i j k = false

@[ext] theorem Poly.ext {p q : Poly}
    (h : ∀ i j k, p.coeff i j k = q.coeff i j k) : p = q := by
  cases p with | mk pc pf =>
    cases q with | mk qc qf =>
      have hc : pc = qc := funext fun i => funext fun j => funext fun k => h i j k
      cases hc
      rfl

def zero : Poly := ⟨fun _ _ _ => false, ⟨0, by intros; rfl⟩⟩

def add (p q : Poly) : Poly where
  coeff i j k := p.coeff i j k ^^ q.coeff i j k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    obtain ⟨M, hM⟩ := q.finite
    refine ⟨N + M, ?_⟩
    intro i j k h
    rw [hN i j k (by omega), hM i j k (by omega)]
    rfl

def one : Poly where
  coeff i j k := decide (i = 0 ∧ j = 0 ∧ k = 0)
  finite := by
    refine ⟨1, ?_⟩
    intro i j k h
    simp only [decide_eq_false_iff_not]
    omega

@[simp] theorem zero_coeff (i j k : Nat) : zero.coeff i j k = false := rfl
@[simp] theorem add_coeff (p q : Poly) (i j k : Nat) :
    (add p q).coeff i j k = (p.coeff i j k ^^ q.coeff i j k) := rfl
@[simp] theorem one_coeff (i j k : Nat) :
    one.coeff i j k = decide (i = 0 ∧ j = 0 ∧ k = 0) := rfl

theorem add_comm (p q : Poly) : add p q = add q p := by
  apply Poly.ext; intro i j k; exact Bool.xor_comm _ _
theorem add_assoc (p q r : Poly) : add (add p q) r = add p (add q r) := by
  apply Poly.ext; intro i j k; exact Bool.xor_assoc _ _ _
@[simp] theorem add_zero (p : Poly) : add p zero = p := by
  apply Poly.ext; intro i j k; exact Bool.xor_false _
@[simp] theorem zero_add (p : Poly) : add zero p = p := by
  apply Poly.ext; intro i j k; exact Bool.false_xor _
@[simp] theorem add_self (p : Poly) : add p p = zero := by
  apply Poly.ext; intro i j k; exact Bool.xor_self _

theorem xor_eq_false_iff (a b : Bool) : (a ^^ b) = false ↔ a = b := by
  cases a <;> cases b <;> decide
theorem add_eq_zero_iff (p q : Poly) : add p q = zero ↔ p = q := by
  constructor
  · intro h
    apply Poly.ext; intro i j k
    exact (xor_eq_false_iff _ _).mp (congrArg (fun r : Poly => r.coeff i j k) h)
  · intro h; subst q; exact add_self p

def xMul (p : Poly) : Poly where
  coeff i j k := match i with | 0 => false | i+1 => p.coeff i j k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N + 1, ?_⟩
    intro i j k h
    cases i with
    | zero => rfl
    | succ i => exact hN i j k (by omega)

def X : Poly := xMul one

@[simp] theorem xMul_coeff_zero (p : Poly) (j k : Nat) :
    (xMul p).coeff 0 j k = false := rfl
@[simp] theorem xMul_coeff_succ (p : Poly) (i j k : Nat) :
    (xMul p).coeff (i+1) j k = p.coeff i j k := rfl
@[simp] theorem xMul_zero : xMul zero = zero := by
  apply Poly.ext; intro i j k; cases i <;> rfl
theorem xMul_add (p q : Poly) : xMul (add p q) = add (xMul p) (xMul q) := by
  apply Poly.ext; intro i j k; cases i <;> rfl
theorem xMul_injective {p q : Poly} (h : xMul p = xMul q) : p = q := by
  apply Poly.ext; intro i j k
  exact congrArg (fun r : Poly => r.coeff (i+1) j k) h

def dropX (p : Poly) : Poly where
  coeff i j k := p.coeff (i+1) j k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j k h
    exact hN (i+1) j k (by omega)
@[simp] theorem dropX_coeff (p : Poly) (i j k : Nat) :
    (dropX p).coeff i j k = p.coeff (i+1) j k := rfl
@[simp] theorem dropX_xMul (p : Poly) : dropX (xMul p) = p := by
  apply Poly.ext; intros; rfl

theorem dropX_cancel (p : Poly)
    (h : ∀ j k, p.coeff 0 j k = false) : xMul (dropX p) = p := by
  apply Poly.ext; intro i j k
  cases i with
  | zero => exact (h j k).symm
  | succ i => rfl

theorem xMul_image_iff (p : Poly) :
    (∃ q, p = xMul q) ↔ ∀ j k, p.coeff 0 j k = false := by
  constructor
  · rintro ⟨q, rfl⟩; intros; rfl
  · intro h; exact ⟨dropX p, (dropX_cancel p h).symm⟩

def yMul (p : Poly) : Poly where
  coeff i j k := match j with | 0 => false | j+1 => p.coeff i j k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N + 1, ?_⟩
    intro i j k h
    cases j with
    | zero => rfl
    | succ j => exact hN i j k (by omega)

def Y : Poly := yMul one

@[simp] theorem yMul_coeff_zero (p : Poly) (i k : Nat) :
    (yMul p).coeff i 0 k = false := rfl
@[simp] theorem yMul_coeff_succ (p : Poly) (i j k : Nat) :
    (yMul p).coeff i (j+1) k = p.coeff i j k := rfl
@[simp] theorem yMul_zero : yMul zero = zero := by
  apply Poly.ext; intro i j k; cases j <;> rfl
theorem yMul_add (p q : Poly) : yMul (add p q) = add (yMul p) (yMul q) := by
  apply Poly.ext; intro i j k; cases j <;> rfl
theorem yMul_injective {p q : Poly} (h : yMul p = yMul q) : p = q := by
  apply Poly.ext; intro i j k
  exact congrArg (fun r : Poly => r.coeff i (j+1) k) h

def dropY (p : Poly) : Poly where
  coeff i j k := p.coeff i (j+1) k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j k h
    exact hN i (j+1) k (by omega)
@[simp] theorem dropY_coeff (p : Poly) (i j k : Nat) :
    (dropY p).coeff i j k = p.coeff i (j+1) k := rfl
@[simp] theorem dropY_yMul (p : Poly) : dropY (yMul p) = p := by
  apply Poly.ext; intros; rfl

theorem dropY_cancel (p : Poly)
    (h : ∀ i k, p.coeff i 0 k = false) : yMul (dropY p) = p := by
  apply Poly.ext; intro i j k
  cases j with
  | zero => exact (h i k).symm
  | succ j => rfl

theorem yMul_image_iff (p : Poly) :
    (∃ q, p = yMul q) ↔ ∀ i k, p.coeff i 0 k = false := by
  constructor
  · rintro ⟨q, rfl⟩; intros; rfl
  · intro h; exact ⟨dropY p, (dropY_cancel p h).symm⟩

def zMul (p : Poly) : Poly where
  coeff i j k := match k with | 0 => false | k+1 => p.coeff i j k
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N + 1, ?_⟩
    intro i j k h
    cases k with
    | zero => rfl
    | succ k => exact hN i j k (by omega)

def Z : Poly := zMul one

@[simp] theorem zMul_coeff_zero (p : Poly) (i j : Nat) :
    (zMul p).coeff i j 0 = false := rfl
@[simp] theorem zMul_coeff_succ (p : Poly) (i j k : Nat) :
    (zMul p).coeff i j (k+1) = p.coeff i j k := rfl
@[simp] theorem zMul_zero : zMul zero = zero := by
  apply Poly.ext; intro i j k; cases k <;> rfl
theorem zMul_add (p q : Poly) : zMul (add p q) = add (zMul p) (zMul q) := by
  apply Poly.ext; intro i j k; cases k <;> rfl
theorem zMul_injective {p q : Poly} (h : zMul p = zMul q) : p = q := by
  apply Poly.ext; intro i j k
  exact congrArg (fun r : Poly => r.coeff i j (k+1)) h

def dropZ (p : Poly) : Poly where
  coeff i j k := p.coeff i j (k+1)
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j k h
    exact hN i j (k+1) (by omega)
@[simp] theorem dropZ_coeff (p : Poly) (i j k : Nat) :
    (dropZ p).coeff i j k = p.coeff i j (k+1) := rfl
@[simp] theorem dropZ_zMul (p : Poly) : dropZ (zMul p) = p := by
  apply Poly.ext; intros; rfl

theorem dropZ_cancel (p : Poly)
    (h : ∀ i j, p.coeff i j 0 = false) : zMul (dropZ p) = p := by
  apply Poly.ext; intro i j k
  cases k with
  | zero => exact (h i j).symm
  | succ k => rfl

theorem zMul_image_iff (p : Poly) :
    (∃ q, p = zMul q) ↔ ∀ i j, p.coeff i j 0 = false := by
  constructor
  · rintro ⟨q, rfl⟩; intros; rfl
  · intro h; exact ⟨dropZ p, (dropZ_cancel p h).symm⟩

theorem xMul_yMul (p : Poly) : xMul (yMul p) = yMul (xMul p) := by
  apply Poly.ext; intro i j k; cases i <;> cases j <;> rfl

theorem xMul_zMul (p : Poly) : xMul (zMul p) = zMul (xMul p) := by
  apply Poly.ext; intro i j k; cases i <;> cases k <;> rfl

theorem yMul_zMul (p : Poly) : yMul (zMul p) = zMul (yMul p) := by
  apply Poly.ext; intro i j k; cases j <;> cases k <;> rfl

def constant (c : Bool) : Poly := if c then one else zero
def scale (c : Bool) (p : Poly) : Poly := if c then p else zero
@[simp] theorem constant_false : constant false = zero := rfl
@[simp] theorem constant_true : constant true = one := rfl
@[simp] theorem scale_false (p : Poly) : scale false p = zero := rfl
@[simp] theorem scale_true (p : Poly) : scale true p = p := rfl
@[simp] theorem constant_coeff (c : Bool) (i j k : Nat) :
    (constant c).coeff i j k = (c && decide (i = 0 ∧ j = 0 ∧ k = 0)) := by cases c <;> rfl
@[simp] theorem scale_coeff (c : Bool) (p : Poly) (i j k : Nat) :
    (scale c p).coeff i j k = (c && p.coeff i j k) := by cases c <;> rfl

/-- Bool with XOR and AND is the two-element field. -/
theorem coefficient_field_laws :
    (∀ a b : Bool, (a ^^ b) = (b ^^ a)) ∧
    (∀ a b c : Bool, ((a ^^ b) ^^ c) = (a ^^ (b ^^ c))) ∧
    (∀ a : Bool, (a ^^ false) = a) ∧
    (∀ a : Bool, (a ^^ a) = false) ∧
    (∀ a b : Bool, (a && b) = (b && a)) ∧
    (∀ a b c : Bool, ((a && b) && c) = (a && (b && c))) ∧
    (∀ a : Bool, (true && a) = a) ∧
    (∀ a b c : Bool, (a && (b ^^ c)) = ((a && b) ^^ (a && c))) ∧
    (true ≠ false) ∧
    (∀ a : Bool, a ≠ false → (a && a) = true) := by decide

theorem one_ne_zero : one ≠ zero := by
  intro h
  have hc := congrArg (fun p : Poly => p.coeff 0 0 0) h
  exact Bool.noConfusion hc

end ThreePoly
