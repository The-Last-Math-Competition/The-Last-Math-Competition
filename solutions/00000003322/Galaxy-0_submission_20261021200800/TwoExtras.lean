import PolynomialRing

namespace TLMC506

def dropX (p : Poly) : Poly where
  coeff i j := p.coeff (i+1) j
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j hij
    exact hN (i+1) j (by omega)

def dropY (p : Poly) : Poly where
  coeff i j := p.coeff i (j+1)
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j hij
    exact hN i (j+1) (by omega)

def axisY (p : Poly) : Poly where
  coeff i j := if i = 0 then p.coeff 0 (j+1) else false
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j hij
    by_cases hi : i = 0
    · simp only [hi]
      exact hN 0 (j+1) (by omega)
    · simp only [hi, if_false]

def constant (c : Bool) : Poly where
  coeff i j := c && decide (i = 0 ∧ j = 0)
  finite := by
    refine ⟨1, ?_⟩
    intro i j hij
    have h : ¬ (i = 0 ∧ j = 0) := by omega
    simp [h]

def scale (c : Bool) (p : Poly) : Poly where
  coeff i j := c && p.coeff i j
  finite := by
    obtain ⟨N, hN⟩ := p.finite
    refine ⟨N, ?_⟩
    intro i j hij
    simp only [hN i j hij, Bool.and_false]

@[simp] theorem dropX_coeff (p : Poly) (i j : Nat) :
    (dropX p).coeff i j = p.coeff (i+1) j := rfl
@[simp] theorem dropY_coeff (p : Poly) (i j : Nat) :
    (dropY p).coeff i j = p.coeff i (j+1) := rfl
@[simp] theorem constant_coeff (c : Bool) (i j : Nat) :
    (constant c).coeff i j = (c && decide (i = 0 ∧ j = 0)) := rfl
@[simp] theorem scale_coeff (c : Bool) (p : Poly) (i j : Nat) :
    (scale c p).coeff i j = (c && p.coeff i j) := rfl
@[simp] theorem constant_false : constant false = zero := by
  apply Poly.ext; intros; rfl
@[simp] theorem constant_true : constant true = one := by
  apply Poly.ext; intros; rfl
@[simp] theorem scale_false (p : Poly) : scale false p = zero := by
  apply Poly.ext; intros; rfl
@[simp] theorem scale_true (p : Poly) : scale true p = p := by
  apply Poly.ext; intros; rfl

theorem constant_split (p : Poly) :
    p = add (constant (p.coeff 0 0)) (add (xMul (dropX p)) (yMul (axisY p))) := by
  apply Poly.ext; intro i j
  cases i with
  | zero => cases j <;> simp [axisY]
  | succ i => cases j <;> simp [axisY]

theorem xMul_mul (p q : Poly) : mul (xMul p) q = xMul (mul p q) := by
  rw [mul_comm, mul_xMul, mul_comm q p]
theorem yMul_mul (p q : Poly) : mul (yMul p) q = yMul (mul p q) := by
  rw [mul_comm, mul_yMul, mul_comm q p]
@[simp] theorem constant_mul (c : Bool) (p : Poly) : mul (constant c) p = scale c p := by
  cases c <;> simp

theorem mul_constant_coefficient (p q : Poly) :
    (mul p q).coeff 0 0 = (p.coeff 0 0 && q.coeff 0 0) := by
  conv => lhs; rw [constant_split p]
  rw [add_mul, add_mul, constant_mul, xMul_mul, yMul_mul]
  simp

/-- Kernel of the residue homomorphism to F₂. -/
def Maximal (p : Poly) : Prop := p.coeff 0 0 = false

def MaximalGenerated (p : Poly) : Prop :=
  ∃ a b, p = add (mul X a) (mul Y b)

theorem maximal_iff_generated (p : Poly) : Maximal p ↔ MaximalGenerated p := by
  constructor
  · intro h
    change p.coeff 0 0 = false at h
    refine ⟨dropX p,axisY p,?_⟩
    simpa only [h,constant_false,zero_add,X_mul,Y_mul] using constant_split p
  · rintro ⟨a,b,rfl⟩
    simp [Maximal]

@[simp] theorem maximal_zero : Maximal zero := rfl

theorem maximal_add {p q : Poly} (hp : Maximal p) (hq : Maximal q) : Maximal (add p q) := by
  change (p.coeff 0 0 ^^ q.coeff 0 0) = false
  rw [hp,hq]; rfl

theorem maximal_mul (p : Poly) {q : Poly} (hq : Maximal q) : Maximal (mul p q) := by
  change (mul p q).coeff 0 0 = false
  rw [mul_constant_coefficient,hq,Bool.and_false]

theorem maximal_generated_least (J : Poly → Prop)
    (hadd : ∀ p q, J p → J q → J (add p q))
    (hmul : ∀ p q, J q → J (mul p q))
    (hx : J X) (hy : J Y) : ∀ p, Maximal p → J p := by
  intro p hp
  obtain ⟨a,b,rfl⟩ := (maximal_iff_generated p).mp hp
  apply hadd
  · rw [mul_comm]; exact hmul _ _ hx
  · rw [mul_comm]; exact hmul _ _ hy

theorem residue_field_certificate :
    (∀ p q, (add p q).coeff 0 0 = (p.coeff 0 0 ^^ q.coeff 0 0)) ∧
    (∀ p q, (mul p q).coeff 0 0 = (p.coeff 0 0 && q.coeff 0 0)) ∧
    one.coeff 0 0 = true ∧
    (∀ c : Bool, ∃ p : Poly, p.coeff 0 0 = c) ∧
    (∀ p, p.coeff 0 0 = false ↔ MaximalGenerated p) := by
  refine ⟨fun _ _ => rfl,mul_constant_coefficient,rfl,?_,maximal_iff_generated⟩
  intro c
  exact ⟨constant c, by cases c <;> rfl⟩

end TLMC506
