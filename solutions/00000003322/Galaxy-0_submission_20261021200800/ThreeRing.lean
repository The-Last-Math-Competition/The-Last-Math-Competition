import ThreeCore
import ThreeRaw
namespace ThreePoly

/-- Interpret a finite list of monomials with parity as its F₂ coefficients. -/
def ofRaw (p : Raw.Poly) : Poly := ⟨Raw.coeff p, Raw.finite p⟩

@[simp] theorem ofRaw_coeff (p : Raw.Poly) (i j k : Nat) :
    (ofRaw p).coeff i j k = Raw.coeff p i j k := rfl

theorem ofRaw_eq_iff (p q : Raw.Poly) : ofRaw p = ofRaw q ↔ Raw.Equiv p q := by
  constructor
  · intro h i j k; exact congrArg (fun r : Poly => r.coeff i j k) h
  · intro h; exact Poly.ext h

/-- Every finitely supported coefficient family is a finite monomial sum. -/
theorem ofRaw_surjective (p : Poly) : ∃ l : Raw.Poly, ofRaw l = p := by
  obtain ⟨N,hN⟩ := p.finite
  refine ⟨Raw.box p.coeff N N N, ?_⟩
  apply Poly.ext
  intro i j k
  rw [ofRaw_coeff, Raw.coeff_box]
  by_cases h : i<N ∧ j<N ∧ k<N
  · exact if_pos h
  · rw [if_neg h]
    exact (hN i j k (by omega)).symm

noncomputable def raw (p : Poly) : Raw.Poly := Classical.choose (ofRaw_surjective p)
@[simp] theorem ofRaw_raw (p : Poly) : ofRaw (raw p) = p := Classical.choose_spec (ofRaw_surjective p)

theorem raw_ofRaw (l : Raw.Poly) : Raw.Equiv (raw (ofRaw l)) l := by
  exact (ofRaw_eq_iff _ _).mp (ofRaw_raw _)

/-- Ordinary polynomial multiplication: distribute every finite monomial sum,
add exponents, and collect equal monomials by parity. Representation independence
is proved below, rather than assumed. -/
noncomputable def mul (p q : Poly) : Poly := ofRaw (Raw.mul (raw p) (raw q))

theorem mul_ofRaw (p q : Raw.Poly) : mul (ofRaw p) (ofRaw q) = ofRaw (Raw.mul p q) := by
  apply (ofRaw_eq_iff _ _).mpr
  intro i j k
  rw [Raw.mul_congr_left (raw_ofRaw p) (raw (ofRaw q)) i j k]
  exact Raw.mul_congr_right p (raw_ofRaw q) i j k

@[simp] theorem ofRaw_nil : ofRaw [] = zero := by apply Poly.ext; intros; rfl
@[simp] theorem ofRaw_append (p q : Raw.Poly) : ofRaw (p++q) = add (ofRaw p) (ofRaw q) := by
  apply Poly.ext; intro i j k; exact Raw.coeff_append p q i j k

@[simp] theorem ofRaw_one : ofRaw [(0,0,0)] = one := by
  apply Poly.ext
  intro i j k
  apply Bool.eq_iff_iff.mpr
  simp only [ofRaw_coeff, Raw.coeff_cons, Raw.coeff_nil, Bool.xor_false,
    one_coeff, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

theorem ofRaw_shiftX (p : Raw.Poly) : ofRaw (Raw.shift 1 0 0 p) = xMul (ofRaw p) := by
  apply Poly.ext
  intro i j k
  rw [ofRaw_coeff, Raw.coeff_shift]
  cases i with
  | zero => simp
  | succ i => simp

theorem ofRaw_shiftY (p : Raw.Poly) : ofRaw (Raw.shift 0 1 0 p) = yMul (ofRaw p) := by
  apply Poly.ext
  intro i j k
  rw [ofRaw_coeff, Raw.coeff_shift]
  cases j with
  | zero => simp
  | succ j => simp

@[simp] theorem ofRaw_X : ofRaw [(1,0,0)] = X := by
  rw [show [(1,0,0)] = Raw.shift 1 0 0 [(0,0,0)] from rfl, ofRaw_shiftX, ofRaw_one]
  rfl
@[simp] theorem ofRaw_Y : ofRaw [(0,1,0)] = Y := by
  rw [show [(0,1,0)] = Raw.shift 0 1 0 [(0,0,0)] from rfl, ofRaw_shiftY, ofRaw_one]
  rfl

theorem ofRaw_shiftZ (p : Raw.Poly) : ofRaw (Raw.shift 0 0 1 p) = zMul (ofRaw p) := by
  apply Poly.ext
  intro i j k
  rw [ofRaw_coeff, Raw.coeff_shift]
  cases k with
  | zero => simp
  | succ k => simp

@[simp] theorem ofRaw_Z : ofRaw [(0,0,1)] = Z := by
  rw [show [(0,0,1)] = Raw.shift 0 0 1 [(0,0,0)] from rfl, ofRaw_shiftZ, ofRaw_one]
  rfl

theorem mul_comm (p q : Poly) : mul p q = mul q p := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  obtain ⟨b,rfl⟩ := ofRaw_surjective q
  rw [mul_ofRaw, mul_ofRaw]
  exact (ofRaw_eq_iff _ _).mpr (Raw.mul_comm a b)

theorem mul_assoc (p q r : Poly) : mul (mul p q) r = mul p (mul q r) := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  obtain ⟨b,rfl⟩ := ofRaw_surjective q
  obtain ⟨c,rfl⟩ := ofRaw_surjective r
  simp only [mul_ofRaw, Raw.mul_assoc]

theorem add_mul (p q r : Poly) : mul (add p q) r = add (mul p r) (mul q r) := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  obtain ⟨b,rfl⟩ := ofRaw_surjective q
  obtain ⟨c,rfl⟩ := ofRaw_surjective r
  rw [← ofRaw_append, mul_ofRaw, Raw.mul_append_left, ofRaw_append, mul_ofRaw, mul_ofRaw]

theorem mul_add (p q r : Poly) : mul p (add q r) = add (mul p q) (mul p r) := by
  rw [mul_comm p, add_mul, mul_comm q p, mul_comm r p]

@[simp] theorem zero_mul (p : Poly) : mul zero p = zero := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  rw [← ofRaw_nil, mul_ofRaw]
  rfl
@[simp] theorem mul_zero (p : Poly) : mul p zero = zero := by rw [mul_comm, zero_mul]
@[simp] theorem one_mul (p : Poly) : mul one p = p := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  rw [← ofRaw_one, mul_ofRaw, Raw.mul_singleton_left, Raw.shift_zero]
@[simp] theorem mul_one (p : Poly) : mul p one = p := by rw [mul_comm, one_mul]

@[simp] theorem X_mul (p : Poly) : mul X p = xMul p := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  rw [← ofRaw_X, mul_ofRaw, Raw.mul_singleton_left, ofRaw_shiftX]
@[simp] theorem Y_mul (p : Poly) : mul Y p = yMul p := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  rw [← ofRaw_Y, mul_ofRaw, Raw.mul_singleton_left, ofRaw_shiftY]

theorem mul_xMul (p q : Poly) : mul p (xMul q) = xMul (mul p q) := by
  rw [← X_mul q, ← mul_assoc, mul_comm p X, mul_assoc, X_mul]
theorem mul_yMul (p q : Poly) : mul p (yMul q) = yMul (mul p q) := by
  rw [← Y_mul q, ← mul_assoc, mul_comm p Y, mul_assoc, Y_mul]

@[simp] theorem Z_mul (p : Poly) : mul Z p = zMul p := by
  obtain ⟨a,rfl⟩ := ofRaw_surjective p
  rw [← ofRaw_Z, mul_ofRaw, Raw.mul_singleton_left, ofRaw_shiftZ]

theorem mul_zMul (p q : Poly) : mul p (zMul q) = zMul (mul p q) := by
  rw [← Z_mul q, ← mul_assoc, mul_comm p Z, mul_assoc, Z_mul]

theorem xMul_mul (p q : Poly) : mul (xMul p) q = xMul (mul p q) := by
  rw [mul_comm, mul_xMul, mul_comm q p]
theorem yMul_mul (p q : Poly) : mul (yMul p) q = yMul (mul p q) := by
  rw [mul_comm, mul_yMul, mul_comm q p]
theorem zMul_mul (p q : Poly) : mul (zMul p) q = zMul (mul p q) := by
  rw [mul_comm, mul_zMul, mul_comm q p]

@[simp] theorem constant_mul (c : Bool) (p : Poly) : mul (constant c) p = scale c p := by
  cases c <;> simp

/-- The full commutative-ring axioms, with the characteristic-two additive inverse.
This is an explicit certificate and does not rely on a Mathlib typeclass. -/
theorem polynomial_ring_laws :
    (∀ p q, add p q = add q p) ∧
    (∀ p q r, add (add p q) r = add p (add q r)) ∧
    (∀ p, add p zero = p) ∧
    (∀ p, add p p = zero) ∧
    (∀ p q, mul p q = mul q p) ∧
    (∀ p q r, mul (mul p q) r = mul p (mul q r)) ∧
    (∀ p, mul one p = p) ∧
    (∀ p q r, mul p (add q r) = add (mul p q) (mul p r)) :=
  ⟨add_comm, add_assoc, add_zero, add_self, mul_comm, mul_assoc, one_mul, mul_add⟩

end ThreePoly
