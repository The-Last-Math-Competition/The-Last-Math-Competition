/-
  Conjecture 00000000546 — Foundational Arithmetic & Polynomial Algebra
  Core Lean 4.19.0 (zero external dependencies)
-/

namespace Conjecture00000000546

/-! ## 1. Ceiling Division and Modular Arithmetic -/

/-- Ceiling division `⌈n / k⌉` on natural numbers for `k > 0`. -/
def ceilDiv (n k : Nat) : Nat :=
  (n + k - 1) / k

theorem le_ceilDiv_iff {n k m : Nat} (hk : 0 < k) :
    ceilDiv n k ≤ m ↔ n ≤ m * k := by
  unfold ceilDiv
  have h1 : ((n + k - 1) / k) * k + (n + k - 1) % k = n + k - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod (n + k - 1) k
  have hmod : (n + k - 1) % k < k := Nat.mod_lt _ hk
  constructor
  · intro h
    have hmul : ((n + k - 1) / k) * k ≤ m * k := Nat.mul_le_mul_right k h
    omega
  · intro h
    by_cases hle : (n + k - 1) / k ≤ m
    · exact hle
    · have hge : m + 1 ≤ (n + k - 1) / k := by omega
      have hmul : (m + 1) * k ≤ ((n + k - 1) / k) * k := Nat.mul_le_mul_right k hge
      have hexp : (m + 1) * k = m * k + k := Nat.succ_mul m k
      omega

theorem lt_ceilDiv_iff {n k m : Nat} (hk : 0 < k) :
    m < ceilDiv n k ↔ m * k < n := by
  have h := le_ceilDiv_iff (n := n) (k := k) (m := m) hk
  omega

theorem ceilDiv_pos {n k : Nat} (hn : 0 < n) (hk : 0 < k) :
    0 < ceilDiv n k := by
  rw [lt_ceilDiv_iff hk]
  omega

theorem ceilDiv_spec_upper {n k : Nat} (hk : 0 < k) :
    n ≤ ceilDiv n k * k :=
  (le_ceilDiv_iff hk).mp (Nat.le_refl _)

theorem ceilDiv_spec_lower {n k : Nat} (hn : 0 < n) (hk : 0 < k) :
    (ceilDiv n k - 1) * k < n := by
  have hpos : 0 < ceilDiv n k := ceilDiv_pos hn hk
  exact (lt_ceilDiv_iff hk).mp (by omega)

theorem ceilDiv_eq_iff {n k q : Nat} (hn : 0 < n) (hk : 0 < k) :
    ceilDiv n k = q ↔ 0 < q ∧ (q - 1) * k < n ∧ n ≤ q * k := by
  constructor
  · intro h
    subst h
    exact ⟨ceilDiv_pos hn hk, ceilDiv_spec_lower hn hk, ceilDiv_spec_upper hk⟩
  · rintro ⟨hq, hlow, hhigh⟩
    have hle : ceilDiv n k ≤ q := (le_ceilDiv_iff hk).mpr hhigh
    have hlt : q - 1 < ceilDiv n k := (lt_ceilDiv_iff hk).mpr hlow
    omega

theorem ceilDiv_mul_self {q k : Nat} (hk : 0 < k) :
    ceilDiv (q * k) k = q := by
  by_cases hq : q = 0
  · subst hq
    simp [ceilDiv]
    exact Nat.div_eq_of_lt (by omega)
  · have hn : 0 < q * k := Nat.mul_pos (by omega) hk
    rw [ceilDiv_eq_iff hn hk]
    refine ⟨by omega, ?_, Nat.le_refl _⟩
    have hexp : q * k = (q - 1) * k + k := by
      have : q - 1 + 1 = q := by omega
      calc q * k = (q - 1 + 1) * k := by rw [this]
        _ = (q - 1) * k + k := Nat.succ_mul (q - 1) k
    omega

theorem ceilDiv_succ_gt_iff {m k : Nat} (hk : 0 < k) :
    ceilDiv m k < ceilDiv (m + 1) k ↔ m % k = 0 := by
  constructor
  · intro hlt
    by_cases hmod : m % k = 0
    · exact hmod
    · let q := ceilDiv m k
      have hupper : m ≤ q * k := ceilDiv_spec_upper hk
      have hneq : m ≠ q * k := by
        intro heq
        rw [heq, Nat.mul_mod_left] at hmod
        exact hmod rfl
      have hm1 : m + 1 ≤ q * k := by omega
      have hle : ceilDiv (m + 1) k ≤ q := (le_ceilDiv_iff hk).mpr hm1
      omega
  · intro hmod
    have hdiv : (m / k) * k = m := by
      have h1 := Nat.div_add_mod m k
      have h2 : k * (m / k) = (m / k) * k := Nat.mul_comm k (m / k)
      omega
    have h1 : ceilDiv m k = m / k := by
      calc ceilDiv m k = ceilDiv (m / k * k) k := by rw [hdiv]
        _ = m / k := ceilDiv_mul_self hk
    have h2 : m / k < ceilDiv (m + 1) k := by
      rw [lt_ceilDiv_iff hk]
      omega
    omega

theorem ceilDiv_le_succ (m k : Nat) :
    ceilDiv m k ≤ ceilDiv (m + 1) k := by
  by_cases hk : k = 0
  · subst hk; simp [ceilDiv]
  · have hkpos : 0 < k := by omega
    rw [le_ceilDiv_iff hkpos]
    have := ceilDiv_spec_upper (n := m + 1) hkpos
    omega

theorem ceilDiv_succ_eq_self_or_succ {m k : Nat} (hk : 0 < k) :
    ceilDiv (m + 1) k = ceilDiv m k ∨ ceilDiv (m + 1) k = ceilDiv m k + 1 := by
  have hle : ceilDiv m k ≤ ceilDiv (m + 1) k := ceilDiv_le_succ m k
  have hup : ceilDiv (m + 1) k ≤ ceilDiv m k + 1 := by
    rw [le_ceilDiv_iff hk]
    have h1 : m ≤ ceilDiv m k * k := ceilDiv_spec_upper hk
    have hexp : (ceilDiv m k + 1) * k = ceilDiv m k * k + k := Nat.succ_mul _ k
    omega
  omega

/-! ## 2. Minimal Field Typeclass and Concrete Witness `F2` -/

/-- Minimal field axioms over `K` with decidable equality for constructive polynomial algebra. -/
class FieldCoeff (K : Type) where
  decEq : DecidableEq K
  zero : K
  one : K
  add : K → K → K
  neg : K → K
  mul : K → K → K
  inv : K → K
  zero_ne_one : zero ≠ one
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  zero_mul : ∀ a, mul zero a = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one

instance instDecidableEqOfFieldCoeff {K : Type} [FieldCoeff K] : DecidableEq K :=
  FieldCoeff.decEq

namespace FieldCoeff

variable {K : Type} [FieldCoeff K]

theorem add_zero (a : K) : add a zero = a := by
  rw [add_comm, zero_add]

theorem mul_one (a : K) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem mul_zero (a : K) : mul a zero = zero := by
  rw [mul_comm, zero_mul]

theorem right_distrib (a b c : K) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_eq_zero {a b : K} (h : mul a b = zero) : a = zero ∨ b = zero := by
  by_cases ha : a = zero
  · exact Or.inl ha
  · right
    have hinv : mul (inv a) (mul a b) = mul (inv a) zero := congrArg (mul (inv a)) h
    rw [mul_zero, ← mul_assoc, mul_comm (inv a) a, mul_inv a ha, one_mul] at hinv
    exact hinv

theorem mul_ne_zero {a b : K} (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := by
  intro h
  rcases mul_eq_zero h with rfl | rfl
  · exact ha rfl
  · exact hb rfl

end FieldCoeff

/-- Concrete field `𝔽₂` (`Bool` with XOR and AND) witnessing `FieldCoeff` non-vacuity. -/
abbrev F2 : Type := Bool

instance instFieldCoeffF2 : FieldCoeff F2 where
  decEq := inferInstance
  zero := false
  one := true
  add := xor
  neg := id
  mul := and
  inv := id
  zero_ne_one := by decide
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_neg := by intro a; cases a <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_inv := by
    intro a ha
    cases a
    · exact False.elim (ha rfl)
    · rfl

/-! ## 3. Univariate Polynomials `Poly1 K` and Support Calculus -/

/-- Univariate polynomials over `K` represented by coefficient lists. -/
abbrev Poly1 (K : Type) := List K

section Poly1Ops

variable {K : Type} [FieldCoeff K]

/-- Coefficient of `t^n` in `p`. -/
def coeff1 (p : Poly1 K) (n : Nat) : K :=
  match p, n with
  | [], _ => FieldCoeff.zero
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeff1 cs n

/-- Polynomial equality (extensional equality of all coefficients). -/
def Poly1Eq (p q : Poly1 K) : Prop :=
  ∀ n, coeff1 p n = coeff1 q n

theorem Poly1Eq.refl (p : Poly1 K) : Poly1Eq p p :=
  fun _ => rfl

theorem Poly1Eq.symm {p q : Poly1 K} (h : Poly1Eq p q) : Poly1Eq q p :=
  fun n => (h n).symm

theorem Poly1Eq.trans {p q r : Poly1 K} (h1 : Poly1Eq p q) (h2 : Poly1Eq q r) : Poly1Eq p r :=
  fun n => (h1 n).trans (h2 n)

def polyAdd : Poly1 K → Poly1 K → Poly1 K
  | [], qs => qs
  | ps, [] => ps
  | p :: ps, q :: qs => FieldCoeff.add p q :: polyAdd ps qs

def polyScale (c : K) : Poly1 K → Poly1 K
  | [] => []
  | p :: ps => FieldCoeff.mul c p :: polyScale c ps

def polyMul : Poly1 K → Poly1 K → Poly1 K
  | [], _ => []
  | p :: ps, qs => polyAdd (polyScale p qs) (FieldCoeff.zero :: polyMul ps qs)

def polyPow (p : Poly1 K) : Nat → Poly1 K
  | 0 => [FieldCoeff.one]
  | m + 1 => polyMul p (polyPow p m)

def monomial1 (c : K) : Nat → Poly1 K
  | 0 => [c]
  | d + 1 => FieldCoeff.zero :: monomial1 c d

@[simp] theorem coeff1_nil (n : Nat) : coeff1 ([] : Poly1 K) n = FieldCoeff.zero := rfl

theorem coeff1_polyAdd (p q : Poly1 K) (n : Nat) :
    coeff1 (polyAdd p q) n = FieldCoeff.add (coeff1 p n) (coeff1 q n) := by
  induction p generalizing q n with
  | nil =>
    simp [polyAdd, coeff1_nil, FieldCoeff.zero_add]
  | cons a ps ih =>
    cases q with
    | nil =>
      simp [polyAdd, coeff1_nil, FieldCoeff.add_zero]
    | cons b qs =>
      cases n with
      | zero => rfl
      | succ m => exact ih qs m

theorem coeff1_polyScale (c : K) (p : Poly1 K) (n : Nat) :
    coeff1 (polyScale c p) n = FieldCoeff.mul c (coeff1 p n) := by
  induction p generalizing n with
  | nil =>
    simp [polyScale, coeff1_nil, FieldCoeff.mul_zero]
  | cons a ps ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih m

theorem coeff1_monomial1_eq (c : K) (d : Nat) :
    coeff1 (monomial1 c d) d = c := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem coeff1_monomial1_ne (c : K) {d n : Nat} (h : n ≠ d) :
    coeff1 (monomial1 c d) n = FieldCoeff.zero := by
  induction d generalizing n with
  | zero =>
    cases n with
    | zero => exact False.elim (h rfl)
    | succ m => rfl
  | succ d ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih (by omega)

theorem coeff1_mul_monomial1_lt (d : Nat) (p : Poly1 K) {n : Nat} (hn : n < d) :
    coeff1 (polyMul (monomial1 FieldCoeff.one d) p) n = FieldCoeff.zero := by
  induction d generalizing n with
  | zero => omega
  | succ d ih =>
    cases n with
    | zero =>
      simp [monomial1, polyMul, coeff1_polyAdd, coeff1_polyScale, FieldCoeff.zero_mul,
            coeff1, FieldCoeff.zero_add]
    | succ m =>
      simp [monomial1, polyMul, coeff1_polyAdd, coeff1_polyScale, FieldCoeff.zero_mul,
            coeff1, FieldCoeff.zero_add]
      exact ih (by omega)

theorem coeff1_mul_monomial1_add (d : Nat) (p : Poly1 K) (n : Nat) :
    coeff1 (polyMul (monomial1 FieldCoeff.one d) p) (d + n) = coeff1 p n := by
  induction d with
  | zero =>
    have h0 : coeff1 ([FieldCoeff.zero] : Poly1 K) n = FieldCoeff.zero := by
      cases n <;> rfl
    rw [Nat.zero_add]
    simp [monomial1, polyMul, coeff1_polyAdd, coeff1_polyScale, FieldCoeff.one_mul,
          h0, FieldCoeff.add_zero]
  | succ d ih =>
    have hshift : d + 1 + n = (d + n) + 1 := by omega
    rw [hshift]
    simp [monomial1, polyMul, coeff1_polyAdd, coeff1_polyScale, FieldCoeff.zero_mul,
          coeff1, FieldCoeff.zero_add]
    exact ih

/-- Shifted support preservation under polynomial Cauchy product. -/
theorem coeff1_polyMul_support_shift {P Q R : Nat → Prop}
    (hcombine : ∀ i j, P i → Q j → R (i + j))
    (p q : Poly1 K) (d : Nat)
    (hp : ∀ i, coeff1 p i ≠ FieldCoeff.zero → P (d + i))
    (hq : ∀ j, coeff1 q j ≠ FieldCoeff.zero → Q j) :
    ∀ n, coeff1 (polyMul p q) n ≠ FieldCoeff.zero → R (d + n) := by
  induction p generalizing d with
  | nil =>
    intro n hn
    exact False.elim (hn rfl)
  | cons c ps ih =>
    intro n hn
    rw [polyMul, coeff1_polyAdd] at hn
    by_cases h1 : coeff1 (polyScale c q) n = FieldCoeff.zero
    · rw [h1, FieldCoeff.zero_add] at hn
      cases n with
      | zero => exact False.elim (hn rfl)
      | succ m =>
        have hps : ∀ i, coeff1 ps i ≠ FieldCoeff.zero → P ((d + 1) + i) := by
          intro i hi
          have : d + (i + 1) = (d + 1) + i := by omega
          rw [← this]
          exact hp (i + 1) hi
        have hres := ih (d + 1) hps m hn
        have : (d + 1) + m = d + (m + 1) := by omega
        rwa [this] at hres
    · rw [coeff1_polyScale] at h1
      have hc : c ≠ FieldCoeff.zero := by
        intro hc0
        rw [hc0, FieldCoeff.zero_mul] at h1
        exact h1 rfl
      have hqn : coeff1 q n ≠ FieldCoeff.zero := by
        intro hq0
        rw [hq0, FieldCoeff.mul_zero] at h1
        exact h1 rfl
      have hPd : P d := by
        have h0 := hp 0 hc
        rwa [Nat.add_zero] at h0
      exact hcombine d n hPd (hq n hqn)

theorem coeff1_polyMul_support {P Q R : Nat → Prop}
    (hcombine : ∀ i j, P i → Q j → R (i + j))
    (p q : Poly1 K)
    (hp : ∀ i, coeff1 p i ≠ FieldCoeff.zero → P i)
    (hq : ∀ j, coeff1 q j ≠ FieldCoeff.zero → Q j) :
    ∀ n, coeff1 (polyMul p q) n ≠ FieldCoeff.zero → R n := by
  have hp0 : ∀ i, coeff1 p i ≠ FieldCoeff.zero → P (0 + i) := by
    intro i hi
    rw [Nat.zero_add]
    exact hp i hi
  have h := coeff1_polyMul_support_shift hcombine p q 0 hp0 hq
  intro n hn
  have hres := h n hn
  rwa [Nat.zero_add] at hres

theorem coeff1_polyPow_lower_bound {a : Nat} {p : Poly1 K}
    (hp : ∀ i, coeff1 p i ≠ FieldCoeff.zero → a ≤ i) (m : Nat) :
    ∀ n, coeff1 (polyPow p m) n ≠ FieldCoeff.zero → m * a ≤ n := by
  induction m with
  | zero =>
    intro n _
    omega
  | succ m ih =>
    intro n hn
    refine coeff1_polyMul_support (P := fun i => a ≤ i) (Q := fun j => m * a ≤ j)
      (R := fun k => (m + 1) * a ≤ k) ?_ p (polyPow p m) hp ih n hn
    intro i j hi hj
    have hexp : (m + 1) * a = m * a + a := Nat.succ_mul m a
    omega

theorem coeff1_drop (d : Nat) (p : Poly1 K) (n : Nat) :
    coeff1 (p.drop d) n = coeff1 p (d + n) := by
  induction d generalizing p with
  | zero => simp
  | succ d ih =>
    cases p with
    | nil => simp [coeff1]
    | cons c ps =>
      have hshift : d + 1 + n = (d + n) + 1 := by omega
      rw [List.drop_succ_cons, ih ps, hshift]
      rfl

/-- Exact divisibility by `t^d`: if all nonzero coefficients of `f` sit at indices `≥ d`,
    then `f` equals `t^d * (f.drop d)`. -/
theorem poly1_div_by_monomial1 (d : Nat) (f : Poly1 K)
    (hf : ∀ n, coeff1 f n ≠ FieldCoeff.zero → d ≤ n) :
    Poly1Eq f (polyMul (monomial1 FieldCoeff.one d) (f.drop d)) := by
  intro n
  by_cases hlt : n < d
  · rw [coeff1_mul_monomial1_lt d (f.drop d) hlt]
    by_cases hne : coeff1 f n = FieldCoeff.zero
    · exact hne
    · have := hf n hne
      omega
  · have hsplit : n = d + (n - d) := by omega
    rw [hsplit, coeff1_mul_monomial1_add d (f.drop d) (n - d), coeff1_drop, ← hsplit]

end Poly1Ops

end Conjecture00000000546
