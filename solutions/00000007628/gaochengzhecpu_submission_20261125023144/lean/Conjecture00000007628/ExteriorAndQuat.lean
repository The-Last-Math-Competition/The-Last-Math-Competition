/-
  Conjecture 00000007628 — Degenerate Clifford / Exterior Algebra `Λ(K²) = Cl(K², 0)`,
  Characteristic-Zero Division Clifford Algebra `Cl_{0,2}(ℤ) = ℍ_ℤ`, and 1D Clifford Algebra `Cl_{1,0}(K)`.
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007628.Field

namespace Conjecture00000007628

open CommField

/-! ### 1. Degenerate Clifford Algebra `Cl(K², 0) = Λ(K²)` (`Ext2 K`) -/

/-- 4-dimensional exterior algebra `Λ(K²) = Cl(K², 0)` with basis `{1, e₁, e₂, e₁₂}`. -/
structure Ext2 (K : Type) where
  c0  : K
  c1  : K
  c2  : K
  c12 : K
  deriving DecidableEq, Repr

namespace Ext2

@[ext]
theorem ext {K : Type} {a b : Ext2 K}
    (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) (h12 : a.c12 = b.c12) : a = b := by
  cases a; cases b
  simp only at h0 h1 h2 h12
  subst h0; subst h1; subst h2; subst h12; rfl

section ExtOps
variable {K : Type} [CommField K]

def zero : Ext2 K := ⟨0, 0, 0, 0⟩
def one  : Ext2 K := ⟨1, 0, 0, 0⟩
def e1   : Ext2 K := ⟨0, 1, 0, 0⟩
def e2   : Ext2 K := ⟨0, 0, 1, 0⟩
def e12  : Ext2 K := ⟨0, 0, 0, 1⟩

def add (a b : Ext2 K) : Ext2 K :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c12 + b.c12⟩

def smul (c : K) (a : Ext2 K) : Ext2 K :=
  ⟨c * a.c0, c * a.c1, c * a.c2, c * a.c12⟩

def mul (a b : Ext2 K) : Ext2 K :=
  ⟨a.c0 * b.c0,
   a.c0 * b.c1 + a.c1 * b.c0,
   a.c0 * b.c2 + a.c2 * b.c0,
   a.c0 * b.c12 + a.c12 * b.c0 + (a.c1 * b.c2 - a.c2 * b.c1)⟩

/-- Universal Clifford law for `Q ≡ 0` on `V = span{e₁, e₂}`: every vector `v = x e₁ + y e₂`
    satisfies `v² = 0 = Q(v) • 1`, with `e₁ e₂ = e₁₂ = -e₂ e₁`. -/
theorem clifford_zero_relations (x y : K) :
    let v : Ext2 K := ⟨0, x, y, 0⟩
    mul v v = zero ∧
    mul (e1 (K := K)) e2 = e12 ∧
    add (mul (e1 (K := K)) e2) (mul e2 e1) = zero := by
  refine ⟨?_, ?_, ?_⟩
  · ext
    · simp [mul, zero, zero_mul]
    · simp [mul, zero, zero_mul, mul_zero, add_zero]
    · simp [mul, zero, zero_mul, mul_zero, add_zero]
    · simp only [mul, zero, zero_mul, mul_zero, add_zero, zero_add]
      rw [mul_comm y x, sub_self]
  · ext <;> simp [mul, e1, e2, e12, zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero]
  · ext <;> simp [add, mul, e1, e2, zero, zero_mul, mul_zero, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, add_neg_cancel]

/-- Every element in the 3-dimensional augmentation ideal `Λ⁺(K²) = {a | a.c0 = 0}` squares to 0. -/
theorem augmentation_ideal_nilpotent {a : Ext2 K} (ha : a.c0 = 0) : mul a a = zero := by
  ext
  · simp [mul, zero, ha, zero_mul]
  · simp [mul, zero, ha, zero_mul, mul_zero, add_zero]
  · simp [mul, zero, ha, zero_mul, mul_zero, add_zero]
  · simp only [mul, zero, ha, zero_mul, mul_zero, add_zero, zero_add]
    rw [mul_comm a.c2 a.c1, sub_self]

/-- `Λ(K²)` has NO nontrivial idempotents: `a² = a ↔ a = 0 ∨ a = 1`. -/
theorem idempotent_trivial {a : Ext2 K} (hidem : mul a a = a) : a = zero ∨ a = one := by
  have h0 : a.c0 * a.c0 = a.c0 := congrArg Ext2.c0 hidem
  have h1 : a.c0 * a.c1 + a.c1 * a.c0 = a.c1 := congrArg Ext2.c1 hidem
  have h2 : a.c0 * a.c2 + a.c2 * a.c0 = a.c2 := congrArg Ext2.c2 hidem
  have h12 : a.c0 * a.c12 + a.c12 * a.c0 + (a.c1 * a.c2 - a.c2 * a.c1) = a.c12 :=
    congrArg Ext2.c12 hidem
  rw [mul_comm a.c2 a.c1, sub_self, add_zero] at h12
  have hfactor : a.c0 * (a.c0 - 1) = 0 := by
    rw [mul_sub, mul_one, h0, sub_self]
  cases mul_eq_zero hfactor with
  | inl hc0 =>
    left
    rw [hc0, zero_mul, mul_zero, add_zero] at h1 h2 h12
    exact ext hc0 h1.symm h2.symm h12.symm
  | inr hc1 =>
    right
    have ha0 : a.c0 = 1 := eq_of_sub_eq_zero hc1
    rw [ha0, one_mul, mul_one] at h1 h2 h12
    have ha1 : a.c1 = 0 := add_left_cancel (a := a.c1) (by rw [h1, add_zero])
    have ha2 : a.c2 = 0 := add_left_cancel (a := a.c2) (by rw [h2, add_zero])
    have ha12 : a.c12 = 0 := add_left_cancel (a := a.c12) (by rw [h12, add_zero])
    exact ext ha0 ha1 ha2 ha12

/-- Top exterior power `I_top = K e₁₂ = {a | a.c0 = 0 ∧ a.c1 = 0 ∧ a.c2 = 0}` (`dim_K = 1`). -/
def inTopIdeal (a : Ext2 K) : Prop := a.c0 = 0 ∧ a.c1 = 0 ∧ a.c2 = 0

theorem topIdeal_is_one_dim (a : Ext2 K) :
    inTopIdeal a ↔ a = smul a.c12 e12 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    ext <;> simp [smul, e12, h0, h1, h2, mul_zero, mul_one]
  · intro h
    rw [h]
    refine ⟨?_, ?_, ?_⟩ <;> simp [smul, e12, mul_zero]

/-- Unique minimal left ideal theorem for `Λ(K²)`: every nonzero element `x ∈ Λ(K²)` can be
    left-multiplied into the generator `e₁₂`! Hence `K e₁₂` (`dim_K = 1 ≠ 2 = 2^⌊2/2⌋`) is
    contained in EVERY nonzero left ideal of `Λ(K²)`. -/
theorem e12_mem_every_nonzero_left_ideal {x : Ext2 K} (hx : x ≠ zero) :
    ∃ m : Ext2 K, mul m x = e12 := by
  by_cases h0 : x.c0 ≠ 0
  · refine ⟨⟨0, 0, 0, inv x.c0⟩, ?_⟩
    ext
    · simp [mul, e12, zero_mul]
    · simp [mul, e12, zero_mul, add_zero]
    · simp [mul, e12, zero_mul, add_zero]
    · simp only [mul, e12, zero_mul, sub_self, zero_add, add_zero]
      exact inv_mul_cancel h0
  · have z0 : x.c0 = 0 := by by_cases h : x.c0 = 0; exact h; exact absurd h h0
    by_cases h1 : x.c1 ≠ 0
    · refine ⟨⟨0, 0, -(inv x.c1), 0⟩, ?_⟩
      ext
      · simp [mul, e12, zero_mul]
      · simp [mul, e12, zero_mul, add_zero]
      · simp [mul, e12, z0, zero_mul, mul_zero, add_zero]
      · simp only [mul, e12, z0, zero_mul, mul_zero, add_zero, zero_add, zero_sub]
        rw [neg_mul, neg_neg, inv_mul_cancel h1]
    · have z1 : x.c1 = 0 := by by_cases h : x.c1 = 0; exact h; exact absurd h h1
      by_cases h2 : x.c2 ≠ 0
      · refine ⟨⟨0, inv x.c2, 0, 0⟩, ?_⟩
        ext
        · simp [mul, e12, zero_mul]
        · simp [mul, e12, z0, zero_mul, mul_zero, add_zero]
        · simp [mul, e12, zero_mul, add_zero]
        · simp only [mul, e12, z0, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
          exact inv_mul_cancel h2
      · have z2 : x.c2 = 0 := by by_cases h : x.c2 = 0; exact h; exact absurd h h2
        have h12 : x.c12 ≠ 0 := by
          intro z12
          exact hx (ext z0 z1 z2 z12)
        refine ⟨⟨inv x.c12, 0, 0, 0⟩, ?_⟩
        ext
        · simp [mul, e12, z0, mul_zero]
        · simp [mul, e12, z0, z1, mul_zero, zero_mul, add_zero]
        · simp [mul, e12, z0, z2, mul_zero, zero_mul, add_zero]
        · simp only [mul, e12, z0, zero_mul, mul_zero, sub_self, add_zero]
          exact inv_mul_cancel h12

/-- Failure of semisimple decomposition (Maschke complementation fails): NO left ideal `L` of
    `Λ(K²)` satisfies `I_top ∩ L = {0}` and `I_top + L = Λ(K²)`. -/
theorem ext2_no_semisimple_complement
    (L : Ext2 K → Prop)
    (hL_left : ∀ m l : Ext2 K, L l → L (mul m l))
    (hdisj : ∀ x : Ext2 K, inTopIdeal x → L x → x = zero)
    (hspan : ∃ u l : Ext2 K, inTopIdeal u ∧ L l ∧ add u l = one) : False := by
  rcases hspan with ⟨u, l, hu, hl, hsum⟩
  rcases hu with ⟨hu0, _hu1, _hu2⟩
  have hl0 : l.c0 = 1 := by
    have hc0 := congrArg Ext2.c0 hsum
    simp only [add, one] at hc0
    rw [hu0, zero_add] at hc0
    exact hc0
  have hmul : mul e12 l = e12 := by
    ext
    · simp [mul, e12, zero_mul]
    · simp [mul, e12, zero_mul, add_zero]
    · simp [mul, e12, zero_mul, add_zero]
    · simp only [mul, e12, hl0, zero_mul, mul_one, sub_self, zero_add, add_zero]
  have he12_in_L : L e12 := by
    rw [← hmul]
    exact hL_left e12 l hl
  have he12_top : inTopIdeal (e12 (K := K)) := ⟨rfl, rfl, rfl⟩
  have he12_zero : (e12 (K := K)) = zero := hdisj e12 he12_top he12_in_L
  have h10 : (1 : K) = 0 := congrArg Ext2.c12 he12_zero
  exact zero_ne_one h10.symm

end ExtOps
end Ext2

/-! ### 2. Characteristic-Zero Division Clifford Algebra `Cl_{0,2}(ℤ) = ℍ_ℤ` -/

/-- Integral Hamilton quaternions `ℍ_ℤ = Cl_{0,2}(ℤ)` (`Q(x, y) = -x² - y²`). -/
structure QuatInt where
  re  : Int
  imI : Int
  imJ : Int
  imK : Int
  deriving DecidableEq, Repr

namespace QuatInt

def zero : QuatInt := ⟨0, 0, 0, 0⟩
def one  : QuatInt := ⟨1, 0, 0, 0⟩
def qi   : QuatInt := ⟨0, 1, 0, 0⟩
def qj   : QuatInt := ⟨0, 0, 1, 0⟩
def qk   : QuatInt := ⟨0, 0, 0, 1⟩

def add (p q : QuatInt) : QuatInt :=
  ⟨p.re + q.re, p.imI + q.imI, p.imJ + q.imJ, p.imK + q.imK⟩

def neg (q : QuatInt) : QuatInt :=
  ⟨-q.re, -q.imI, -q.imJ, -q.imK⟩

def scale (n : Int) (q : QuatInt) : QuatInt :=
  ⟨n * q.re, n * q.imI, n * q.imJ, n * q.imK⟩

def conj (q : QuatInt) : QuatInt :=
  ⟨q.re, -q.imI, -q.imJ, -q.imK⟩

def mul (p q : QuatInt) : QuatInt :=
  ⟨p.re * q.re  - p.imI * q.imI - p.imJ * q.imJ - p.imK * q.imK,
   p.re * q.imI + p.imI * q.re  + p.imJ * q.imK - p.imK * q.imJ,
   p.re * q.imJ - p.imI * q.imK + p.imJ * q.re  + p.imK * q.imI,
   p.re * q.imK + p.imI * q.imJ - p.imJ * q.imI + p.imK * q.re⟩

def normSq (q : QuatInt) : Int :=
  q.re * q.re + q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK

@[ext]
theorem ext {p q : QuatInt}
    (h1 : p.re = q.re) (h2 : p.imI = q.imI) (h3 : p.imJ = q.imJ) (h4 : p.imK = q.imK) : p = q := by
  cases p; cases q
  simp only at h1 h2 h3 h4
  subst h1; subst h2; subst h3; subst h4; rfl

theorem cl02_relations :
    mul qi qi = neg one ∧
    mul qj qj = neg one ∧
    add (mul qi qj) (mul qj qi) = zero := by
  refine ⟨by decide, by decide, by decide⟩

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  cases a with
  | ofNat n => exact Int.ofNat_le.mpr (Nat.zero_le (n * n))
  | negSucc n =>
    change 0 ≤ Int.ofNat ((n + 1) * (n + 1))
    exact Int.ofNat_le.mpr (Nat.zero_le _)

theorem int_sq_pos {a : Int} (ha : a ≠ 0) : 0 < a * a := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => exact absurd rfl ha
    | succ m =>
      change (Int.ofNat 0) < Int.ofNat ((m + 1) * (m + 1))
      exact Int.ofNat_lt.mpr (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m))
  | negSucc m =>
    change (Int.ofNat 0) < Int.ofNat ((m + 1) * (m + 1))
    exact Int.ofNat_lt.mpr (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m))

/-- Strict anisotropy of the quaternionic norm on `Cl_{0,2}(ℤ)`: every nonzero `q` satisfies
    `conj(q) * q = normSq(q) • 1` with `0 < normSq(q)`. Over `ℚ` (`Cl_{0,2}(ℚ) = ℍ_ℚ`), dividing
    by `normSq(q) ≠ 0` inverts every nonzero element, so the unique minimal nonzero left ideal
    is `ℍ_ℚ` itself of dimension `4 ≠ 2 = 2^⌊2/2⌋`. -/
theorem conj_mul_self_and_norm_pos {q : QuatInt} (hq : q ≠ zero) :
    mul (conj q) q = scale (normSq q) one ∧ 0 < normSq q := by
  refine ⟨?_, ?_⟩
  · ext
    · simp only [mul, conj, scale, one, normSq, Int.mul_one]
      have s1 : -((-q.imI) * q.imI) = q.imI * q.imI := by rw [Int.neg_mul, Int.neg_neg]
      have s2 : -((-q.imJ) * q.imJ) = q.imJ * q.imJ := by rw [Int.neg_mul, Int.neg_neg]
      have s3 : -((-q.imK) * q.imK) = q.imK * q.imK := by rw [Int.neg_mul, Int.neg_neg]
      omega
    · simp only [mul, conj, scale, one, Int.mul_zero]
      have c1 : q.re * q.imI + (-q.imI) * q.re = 0 := by
        rw [Int.neg_mul, Int.mul_comm q.imI q.re, Int.add_right_neg]
      have c2 : (-q.imJ) * q.imK - (-q.imK) * q.imJ = 0 := by
        rw [Int.neg_mul, Int.neg_mul, Int.mul_comm q.imK q.imJ]
        omega
      omega
    · simp only [mul, conj, scale, one, Int.mul_zero]
      have c1 : q.re * q.imJ + (-q.imJ) * q.re = 0 := by
        rw [Int.neg_mul, Int.mul_comm q.imJ q.re, Int.add_right_neg]
      have c2 : -((-q.imI) * q.imK) + (-q.imK) * q.imI = 0 := by
        rw [Int.neg_mul, Int.neg_mul, Int.mul_comm q.imK q.imI]
        omega
      omega
    · simp only [mul, conj, scale, one, Int.mul_zero]
      have c1 : q.re * q.imK + (-q.imK) * q.re = 0 := by
        rw [Int.neg_mul, Int.mul_comm q.imK q.re, Int.add_right_neg]
      have c2 : (-q.imI) * q.imJ - (-q.imJ) * q.imI = 0 := by
        rw [Int.neg_mul, Int.neg_mul, Int.mul_comm q.imJ q.imI]
        omega
      omega
  · unfold normSq
    have hr := int_sq_nonneg q.re
    have hi := int_sq_nonneg q.imI
    have hj := int_sq_nonneg q.imJ
    have hk := int_sq_nonneg q.imK
    by_cases hre : q.re ≠ 0
    · have hp := int_sq_pos hre; omega
    · by_cases himI : q.imI ≠ 0
      · have hp := int_sq_pos himI; omega
      · by_cases himJ : q.imJ ≠ 0
        · have hp := int_sq_pos himJ; omega
        · have z1 : q.re = 0 := by omega
          have z2 : q.imI = 0 := by omega
          have z3 : q.imJ = 0 := by omega
          have himK : q.imK ≠ 0 := by
            intro z4
            exact hq (ext z1 z2 z3 z4)
          have hp := int_sq_pos himK
          omega

end QuatInt

/-! ### 3. 1D Nondegenerate Clifford Algebra `Cl_{1,0}(K) ≅ K ⊕ K` (`dim_K I_min = 1`, No Symplectic Form) -/

/-- Every `K`-bilinear alternating form `ω : K × K → K` on a 1-dimensional minimal ideal `I₊ ≅ K¹`
    (such as `I₊ = K · ½(1 + e₁) ⊂ Cl_{1,0}(K)`) is identically zero, so `I₊` admits NO
    nondegenerate symplectic form over ANY field `K`. -/
theorem one_dim_no_alternating_form {K : Type} [CommField K]
    (omega1 : K → K → K)
    (hleft  : ∀ c x y : K, omega1 (c * x) y = c * omega1 x y)
    (hright : ∀ d x y : K, omega1 x (d * y) = d * omega1 x y)
    (halt   : ∀ x : K, omega1 x x = 0) :
    ∀ x y : K, omega1 x y = 0 := by
  intro x y
  have hx : x = x * 1 := (mul_one x).symm
  have hy : y = y * 1 := (mul_one y).symm
  rw [hx, hy, hleft, hright, halt 1, mul_zero, mul_zero]

end Conjecture00000007628
