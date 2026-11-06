import PolynomialRing
import Syzygy
namespace TLMC506

/-- `Bool` with XOR and AND is the two-element field. Every nonzero element
has the displayed multiplicative inverse (itself). -/
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
  have hc := congrArg (fun p : Poly => p.coeff 0 0) h
  exact Bool.noConfusion hc

@[simp] theorem constant_mul (c : Bool) (p : Poly) : mul (constant c) p = scale c p := by
  cases c <;> simp

theorem xMul_mul (p q : Poly) : mul (xMul p) q = xMul (mul p q) := by
  rw [mul_comm, mul_xMul, mul_comm q p]
theorem yMul_mul (p q : Poly) : mul (yMul p) q = yMul (mul p q) := by
  rw [mul_comm, mul_yMul, mul_comm q p]

theorem mul_constant_coefficient (p q : Poly) :
    (mul p q).coeff 0 0 = (p.coeff 0 0 && q.coeff 0 0) := by
  conv => lhs; rw [constant_split p]
  rw [add_mul, add_mul, constant_mul, xMul_mul, yMul_mul]
  simp

theorem mul_in_ideal (p : Poly) {q : Poly} (hq : InIdeal q) : InIdeal (mul p q) := by
  obtain ⟨a,b,rfl⟩ := hq
  refine ⟨mul p a, mul p b, ?_⟩
  rw [mul_add, mul_xMul, mul_yMul]

/-- The ordinary scalar action on the free rank-two polynomial module. -/
noncomputable def pairMul (p : Poly) (v : FreeTwo) : FreeTwo :=
  (mul p v.1, mul p v.2)

theorem pairAdd_comm (v w : FreeTwo) : pairAdd v w = pairAdd w v := by
  apply Prod.ext <;> exact add_comm _ _
theorem pairAdd_assoc (u v w : FreeTwo) :
    pairAdd (pairAdd u v) w = pairAdd u (pairAdd v w) := by
  apply Prod.ext <;> exact add_assoc _ _ _
@[simp] theorem pairAdd_zero (v : FreeTwo) : pairAdd v pairZero = v := by
  apply Prod.ext <;> exact add_zero _
@[simp] theorem pairZero_add (v : FreeTwo) : pairAdd pairZero v = v := by
  apply Prod.ext <;> exact zero_add _
@[simp] theorem pairAdd_self (v : FreeTwo) : pairAdd v v = pairZero := by
  apply Prod.ext <;> exact add_self _
@[simp] theorem pairMul_one (v : FreeTwo) : pairMul one v = v := by
  apply Prod.ext <;> exact one_mul _
@[simp] theorem pairMul_zero (v : FreeTwo) : pairMul zero v = pairZero := by
  apply Prod.ext <;> exact zero_mul _
@[simp] theorem pairMul_pairZero (p : Poly) : pairMul p pairZero = pairZero := by
  apply Prod.ext <;> exact mul_zero _
theorem pairMul_assoc (p q : Poly) (v : FreeTwo) :
    pairMul (mul p q) v = pairMul p (pairMul q v) := by
  apply Prod.ext <;> exact mul_assoc _ _ _
theorem pairMul_add (p q : Poly) (v : FreeTwo) :
    pairMul (add p q) v = pairAdd (pairMul p v) (pairMul q v) := by
  apply Prod.ext <;> exact add_mul _ _ _
theorem pairMul_pairAdd (p : Poly) (v w : FreeTwo) :
    pairMul p (pairAdd v w) = pairAdd (pairMul p v) (pairMul p w) := by
  apply Prod.ext <;> exact mul_add _ _ _
@[simp] theorem pairMul_X (v : FreeTwo) : pairMul X v = pairX v := by
  apply Prod.ext <;> exact X_mul _
@[simp] theorem pairMul_Y (v : FreeTwo) : pairMul Y v = pairY v := by
  apply Prod.ext <;> exact Y_mul _
@[simp] theorem pairMul_constant (c : Bool) (v : FreeTwo) : pairMul (constant c) v = pairScale c v := by
  apply Prod.ext <;> exact constant_mul _ _

theorem free_module_laws :
    (∀ v w, pairAdd v w = pairAdd w v) ∧
    (∀ u v w, pairAdd (pairAdd u v) w = pairAdd u (pairAdd v w)) ∧
    (∀ v, pairAdd v pairZero = v) ∧
    (∀ v, pairAdd v v = pairZero) ∧
    (∀ v, pairMul one v = v) ∧
    (∀ p q v, pairMul (mul p q) v = pairMul p (pairMul q v)) ∧
    (∀ p q v, pairMul (add p q) v = pairAdd (pairMul p v) (pairMul q v)) ∧
    (∀ p v w, pairMul p (pairAdd v w) = pairAdd (pairMul p v) (pairMul p w)) :=
  ⟨pairAdd_comm, pairAdd_assoc, pairAdd_zero, pairAdd_self, pairMul_one,
    pairMul_assoc, pairMul_add, pairMul_pairAdd⟩

theorem koszul_mul (p q : Poly) : koszul (mul p q) = pairMul p (koszul q) := by
  apply Prod.ext
  · exact (mul_yMul p q).symm
  · exact (mul_xMul p q).symm

theorem augmentation_mul (p : Poly) (v : FreeTwo) :
    augmentation (pairMul p v) = mul p (augmentation v) := by
  simp only [augmentation, pairMul, mul_add, mul_xMul, mul_yMul]

theorem augmentation_add (v w : FreeTwo) :
    augmentation (pairAdd v w) = add (augmentation v) (augmentation w) := by
  apply Poly.ext
  intro i j
  simp only [augmentation, pairAdd, xMul_add, yMul_add, add_coeff]
  generalize (xMul v.1).coeff i j = A
  generalize (xMul w.1).coeff i j = B
  generalize (yMul v.2).coeff i j = C
  generalize (yMul w.2).coeff i j = D
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

theorem pairMul_syzygy (p : Poly) {v : FreeTwo} (hv : IsSyzygy v) : IsSyzygy (pairMul p v) := by
  unfold IsSyzygy at *
  rw [augmentation_mul, hv, mul_zero]
theorem pairAdd_syzygy {v w : FreeTwo} (hv : IsSyzygy v) (hw : IsSyzygy w) :
    IsSyzygy (pairAdd v w) := by
  unfold IsSyzygy at *
  rw [augmentation_add, hv, hw, add_zero]

/-- The standard product mK: finite sums of arbitrary products of an element
of m=(X,Y) and an element of the syzygy module K. The inductive constructors
are exactly the empty sum, a single summand, and concatenation of sums. -/
inductive IdealSyzygyProduct : FreeTwo → Prop
  | zero : IdealSyzygyProduct pairZero
  | single (p : Poly) (v : FreeTwo) : InIdeal p → IsSyzygy v →
      IdealSyzygyProduct (pairMul p v)
  | add {v w : FreeTwo} : IdealSyzygyProduct v → IdealSyzygyProduct w →
      IdealSyzygyProduct (pairAdd v w)

theorem ideal_syzygy_product_parameter {v : FreeTwo} (hv : IdealSyzygyProduct v) :
    ∃ h : Poly, v = koszul h ∧ InIdeal h := by
  induction hv with
  | zero => exact ⟨zero, koszul_zero.symm, zero_in_ideal⟩
  | single p v hp hv =>
    obtain ⟨h,rfl⟩ := (kernel_exact v).mp hv
    refine ⟨mul p h, (koszul_mul p h).symm, ?_⟩
    rw [mul_comm]
    exact mul_in_ideal h hp
  | add hv hw ihv ihw =>
    obtain ⟨p,rfl,hp⟩ := ihv
    obtain ⟨q,rfl,hq⟩ := ihw
    exact ⟨add p q, (koszul_add p q).symm, add_in_ideal hp hq⟩

/-- The author's two-generator formula is exactly the actual ideal-module
product, not merely a selected family of shifts. -/
theorem maximal_times_syzygy_is_ideal_product (v : FreeTwo) :
    InMaximalTimesSyzygy v ↔ IdealSyzygyProduct v := by
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    rw [← pairMul_X, ← pairMul_Y]
    exact IdealSyzygyProduct.add
      (IdealSyzygyProduct.single X a X_in_ideal ha)
      (IdealSyzygyProduct.single Y b Y_in_ideal hb)
  · intro hv
    obtain ⟨h,rfl,hh⟩ := ideal_syzygy_product_parameter hv
    exact (koszul_in_maximal_iff h).mpr ((ideal_iff_constant_zero h).mp hh)

theorem ideal_syzygy_product_scalar_closed (r : Poly) {v : FreeTwo}
    (hv : IdealSyzygyProduct v) : IdealSyzygyProduct (pairMul r v) := by
  induction hv with
  | zero => simpa only [pairMul_pairZero] using IdealSyzygyProduct.zero
  | single p v hp hv =>
    rw [← pairMul_assoc]
    exact IdealSyzygyProduct.single (mul r p) v (mul_in_ideal r hp) hv
  | add hv hw ihv ihw =>
    rw [pairMul_pairAdd]
    exact IdealSyzygyProduct.add ihv ihw

end TLMC506
