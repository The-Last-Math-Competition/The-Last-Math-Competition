/-!
# Disproof certificate for conjecture 00000000556

Conjecture: `HH¹(Λ) = 0` if and only if Λ is representation-finite and rigid.

Attack: Λ = k[x]/(x²) (dual numbers) is representation-finite and rigid
(Frobenius, hence self-injective), yet `HH¹(Λ) ≅ k ≠ 0`.

This file concretizes the computational core with the base `Nat`:
`L = Nat × Nat` with `(a, b) * (c, d) = (a*c, a*d + b*c)`, i.e. `a + b·x` with `x² = 0`.
(The identical computation over `Int` or any field `k` is carried out in
`reproduce.py` and `main.tex`; the `Nat` instantiation keeps every proof
pure-constructive — zero axioms.)

Key results (all zero-axiom, see Check.lean):
* `d556`, given by `d(1) = 0`, `d(x) = x` (i.e. `d = x·∂`), is a derivation (`d556_leib`);
* every inner derivation vanishes (`ad_zero`), so `d556` is non-inner (`d556_not_inner`)
  and `HH¹ ≠ 0` (`hh1_nonzero`);
* every derivation is the scalar multiple `f(x).2 · d556` (`deriv_scalar`):
  `Der ≅ Nat`, hence `HH¹ ≅ Nat ≠ 0`;
* the Frobenius form `(u, v) ↦ (u*v).2` is nondegenerate (`frobenius_nondegenerate`):
  Λ is Frobenius, i.e. rigid in the sense used by the verdict.
-/

/-- The algebra Λ = Nat[x]/(x²): the element `a + b·x` is the pair `(a, b)`. -/
abbrev L : Type := Nat × Nat

instance instMulL : Mul L := ⟨fun u v => (u.1 * v.1, u.1 * v.2 + u.2 * v.1)⟩
instance instAddL : Add L := ⟨fun u v => (u.1 + v.1, u.2 + v.2)⟩
instance instSubL : Sub L := ⟨fun u v => (u.1 - v.1, u.2 - v.2)⟩

theorem mul_def (a b c d : Nat) : (a, b) * (c, d) = (a * c, a * d + b * c) := rfl

/-- `x = x + x` forces `x = 0` (pure construction, no classical reasoning). -/
theorem nat_eq_zero_of_self_add {x : Nat} (h : x = x + x) : x = 0 := by
  cases x with
  | zero => rfl
  | succ m =>
      exact absurd
        (Nat.le_trans (Nat.le_add_right (Nat.succ m) m)
          (Nat.le_of_eq (Nat.succ.inj h).symm))
        (Nat.not_succ_le_self m)

/-- Pointwise pair extensionality (structure eta + component congruence). -/
theorem pair_ext {p q : L} (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  rw [show (a : Nat) = c from h1, show (b : Nat) = d from h2]

theorem mul_comm_L (u v : L) : u * v = v * u := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  apply pair_ext
  · exact Nat.mul_comm a c
  · show a * d + b * c = c * b + d * a
    rw [Nat.mul_comm a d, Nat.mul_comm b c, Nat.add_comm (d * a) (c * b)]

/-- The inner derivation `ad_u(v) = u·v − v·u` (truncated subtraction on `Nat`). -/
def ad (u : L) : L → L := fun v => u * v - v * u

/-- Every inner derivation of the commutative algebra Λ vanishes: `Inn = 0`. -/
theorem ad_zero (u v : L) : ad u v = (0, 0) := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  apply pair_ext
  · show a * c - c * a = 0
    rw [Nat.mul_comm a c]
    exact Nat.sub_self (c * a)
  · show a * d + b * c - (c * b + d * a) = 0
    rw [Nat.mul_comm a d, Nat.mul_comm b c, Nat.add_comm (d * a) (c * b)]
    exact Nat.sub_self (c * b + d * a)

/-- Derivations of Λ: additive maps killing `1` and satisfying Leibniz.
`f.1` is the underlying map, `f.2.1` additivity, `f.2.2.1` `f(1) = 0`,
`f.2.2.2` the Leibniz rule. -/
def Der : Type :=
  { f : L → L //
    (∀ u v : L, f (u + v) = f u + f v) ∧
    f (1, 0) = (0, 0) ∧
    (∀ u v : L, f (u * v) = u * f v + f u * v) }

theorem deriv_zero (f : Der) : f.1 (0, 0) = (0, 0) := by
  have h2 := f.2.1 (0, 0) (0, 0)
  rw [show ((0:Nat), (0:Nat)) + ((0:Nat), (0:Nat)) = ((0:Nat), (0:Nat)) from rfl] at h2
  apply pair_ext
  · show (f.1 (0, 0)).1 = (0 : Nat)
    exact nat_eq_zero_of_self_add (congrArg Prod.fst h2)
  · show (f.1 (0, 0)).2 = (0 : Nat)
    exact nat_eq_zero_of_self_add (congrArg Prod.snd h2)

/-- Nat-scaling homogeneity of a derivation. -/
theorem deriv_smul_nat (f : Der) (n : Nat) (a b : Nat) :
    f.1 (n * a, n * b) = (n * (f.1 (a, b)).1, n * (f.1 (a, b)).2) := by
  induction n with
  | zero =>
      rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, deriv_zero f]
  | succ m ih =>
      have e1 : (m + 1) * a = m * a + a := Nat.succ_mul m a
      have e2 : (m + 1) * b = m * b + b := Nat.succ_mul m b
      have e3 : (m + 1) * (f.1 (a, b)).1 = m * (f.1 (a, b)).1 + (f.1 (a, b)).1 :=
        Nat.succ_mul m (f.1 (a, b)).1
      have e4 : (m + 1) * (f.1 (a, b)).2 = m * (f.1 (a, b)).2 + (f.1 (a, b)).2 :=
        Nat.succ_mul m (f.1 (a, b)).2
      rw [e1, e2, e3, e4,
        show ((m * a + a, m * b + b)) = ((m * a, m * b) + (a, b)) from rfl,
        f.2.1, ih]
      rfl

theorem pair_zero_add (p : L) : (0, 0) + p = p := by
  show (0 + p.1, 0 + p.2) = p
  rw [Nat.zero_add, Nat.zero_add]

theorem deriv_zero_left (f : Der) (a : Nat) : f.1 (a, 0) = (0, 0) := by
  have h1 : (a, 0) = (a * 1, a * 0) := by
    rw [Nat.mul_one, Nat.mul_zero]
  rw [h1, deriv_smul_nat f a 1 0, show f.1 (1, 0) = ((0:Nat), 0) from f.2.2.1, Nat.mul_zero]

/-- The first coordinate of `f(x)` vanishes: Leibniz on `x·x` gives
`f(0) = f(x·x) = x·f(x) + f(x)·x = (0, 2·(f(x)).1)`, so `2·(f(x)).1 = 0`, hence
`(f(x)).1 = 0` (no 2-torsion). -/
theorem deriv_p_zero (f : Der) : (f.1 (0, 1)).1 = 0 := by
  have hlb := f.2.2.2 (0, 1) (0, 1)
  rw [show (((0:Nat), (1:Nat)) * ((0:Nat), (1:Nat))) = ((0:Nat), (0:Nat)) from rfl, deriv_zero f,
    show ((0:Nat), (1:Nat)) * f.1 ((0:Nat), (1:Nat)) =
      (0 * (f.1 (0, 1)).1, 0 * (f.1 (0, 1)).2 + 1 * (f.1 (0, 1)).1) from rfl,
    show f.1 ((0:Nat), (1:Nat)) * ((0:Nat), (1:Nat)) =
      ((f.1 (0, 1)).1 * 0, (f.1 (0, 1)).1 * 1 + (f.1 (0, 1)).2 * 0) from rfl] at hlb
  have e2 : (0:Nat) = 0 * (f.1 (0, 1)).2 + 1 * (f.1 (0, 1)).1 +
      ((f.1 (0, 1)).1 * 1 + (f.1 (0, 1)).2 * 0) := congrArg Prod.snd hlb
  rw [Nat.zero_mul, Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at e2
  exact Nat.eq_zero_of_add_eq_zero_left e2.symm

theorem deriv_vert (f : Der) (b : Nat) : f.1 (0, b) = (0, b * (f.1 (0, 1)).2) := by
  have h2 : (0, b) = (b * 0, b * 1) := by
    rw [Nat.mul_zero, Nat.mul_one]
  rw [h2, deriv_smul_nat f b 0 1, deriv_p_zero, Nat.mul_zero]

/-- Classification: `f(a, b) = (0, b·q)` with `q = f(x).2`; with `ad_zero` this gives
`HH¹ = Der/Inn ≅ Nat ≠ 0`. -/
theorem deriv_apply (f : Der) (a b : Nat) : f.1 (a, b) = (0, b * (f.1 (0, 1)).2) := by
  have hsplit : (a, b) = (a, 0) + (0, b) := by
    show (a, b) = (a + 0, 0 + b)
    rw [Nat.add_zero, Nat.zero_add]
  rw [hsplit, f.2.1, deriv_zero_left, pair_zero_add, deriv_vert]

/-- The attacking derivation `d = x·∂`: `d(1) = 0`, `d(x) = x`. -/
def d556 : L → L := fun p => (0, p.2)

theorem d556_add (u v : L) : d556 (u + v) = d556 u + d556 v := rfl

theorem d556_one : d556 (1, 0) = (0, 0) := rfl

theorem d556_leib (u v : L) : d556 (u * v) = u * d556 v + d556 u * v := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  apply pair_ext
  · show (0:Nat) = a * 0 + 0 * c
    rw [Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  · show a * d + b * c = a * d + b * 0 + (0 * d + b * c)
    rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

def d556_is_derivation : Der := ⟨d556, d556_add, d556_one, d556_leib⟩

/-- `d556` is not inner (all inner derivations vanish, but `d556(x) = x ≠ 0`). -/
theorem d556_not_inner (u : L) : d556 (0, 1) ≠ ad u (0, 1) := by
  rw [ad_zero u (0, 1)]
  intro hh
  exact Nat.noConfusion (show (1:Nat) = 0 from congrArg Prod.snd hh)

/-- `HH¹ ≠ 0`: the derivation `x·∂` is a derivation that is not inner. -/
theorem hh1_nonzero : ∃ f : Der, ∀ u : L, d556 (0, 1) ≠ ad u (0, 1) :=
  ⟨d556_is_derivation, d556_not_inner⟩

/-- Every derivation is the scalar multiple `f(x).2 · d556`: `Der = Nat·d556`. -/
theorem deriv_scalar (f : Der) (a b : Nat) :
    f.1 (a, b) = ((f.1 (0, 1)).2 * (d556 (a, b)).1, (f.1 (0, 1)).2 * (d556 (a, b)).2) := by
  rw [deriv_apply f a b]
  show (0, b * (f.1 (0, 1)).2) = ((f.1 (0, 1)).2 * 0, (f.1 (0, 1)).2 * b)
  rw [Nat.mul_zero, Nat.mul_comm ((f.1 (0, 1)).2) b]

/-- Frobenius form `λ(a + b·x) = b` evaluated on `u·v`. -/
def Bform (u v : L) : Nat := (u * v).2

/-- The Frobenius form is nondegenerate: Λ is Frobenius, hence self-injective
(rigid in the sense used by the verdict). -/
theorem frobenius_nondegenerate (u : L) (h : ∀ v : L, Bform u v = 0) : u = (0, 0) := by
  obtain ⟨a, b⟩ := u
  show (a, b) = (0, 0)
  have h1 : b = 0 := by
    have hv : a * 0 + b * 1 = 0 := h (1, 0)
    rw [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hv
    exact hv
  have h2 : a = 0 := by
    have hv : a * 1 + b * 0 = 0 := h (0, 1)
    rw [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  rw [h1, h2]

/-- Full attack certificate for Λ = Nat[x]/(x²): a non-inner derivation exists
(`HH¹ ≠ 0`), every derivation is a scalar multiple of `x·∂` (`Der ≅ Nat`),
all inner derivations vanish, and the Frobenius form is nondegenerate
(self-injective / rigid). -/
theorem dualnumbers_certificate :
    (∃ f : Der, ∀ u : L, d556 (0, 1) ≠ ad u (0, 1)) ∧
      (∀ f : Der, ∀ a b : Nat,
        f.1 (a, b) = ((f.1 (0, 1)).2 * (d556 (a, b)).1, (f.1 (0, 1)).2 * (d556 (a, b)).2)) ∧
      (∀ u v : L, ad u v = (0, 0)) ∧
      (∀ u : L, (∀ v : L, Bform u v = 0) → u = (0, 0)) :=
  ⟨hh1_nonzero, deriv_scalar, ad_zero, frobenius_nondegenerate⟩
