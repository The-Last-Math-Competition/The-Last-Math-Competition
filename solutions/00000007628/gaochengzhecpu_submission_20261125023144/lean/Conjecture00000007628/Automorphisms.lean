/-
  Conjecture 00000007628 — Universal Refutation of Ideal Automorphism Group = Symplectic Group
  Across All Five Standard Definitions:
    (A) Left `Cl`-module automorphisms `Aut_{Cl}(S₁) ≅ Kˣ` (abelian vs. non-abelian `Sp₂(F)`),
    (B) `K`-linear automorphisms `GL_K(S)` (`det = -1` / order `48 ≠ 24` over `𝔽₃`, odd dim 1),
    (C) Non-unital `K`-algebra automorphisms `Aut_{K-alg}(S₁) ≅ Aff₁(K)` (metabelian vs. `Sp₂(F)`),
    (D) Unital `K`-algebra automorphisms `Aut_{K-alg}(M₂(K))` (trivial center vs. `{±I₂} ⊆ Z(Sp₂)`),
    (E) Canonical spinor bilinear pairing automorphisms (`O₂` on `Cl_{2,0}` + mod-8 periodicity at `n = 8`).
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007628.Field
import Conjecture00000007628.Mat2
import Conjecture00000007628.ExteriorAndQuat

namespace Conjecture00000007628

open CommField

/-! ### Symplectic Group `Sp₂(F)` over Any Field `F` -/

/-- The rank-1 symplectic group `Sp₂(F) = Aut_F(F², ω) = {g ∈ M₂(F) | ω(g u, g v) = ω(u, v)}`. -/
structure Sp2 (F : Type) [CommField F] where
  mat : Mat2 F
  symp : ∀ u v : Vec2 F, Mat2.omega (Mat2.act mat u) (Mat2.act mat v) = Mat2.omega u v

namespace Sp2

theorem ext {F : Type} [CommField F] {g1 g2 : Sp2 F} (h : g1.mat = g2.mat) : g1 = g2 := by
  cases g1; cases g2; simp only at h; subst h; rfl

section Sp2Group
variable {F : Type} [CommField F]

theorem det_eq_one (g : Sp2 F) : Mat2.det g.mat = 1 :=
  (Mat2.preserves_omega_iff_det_eq_one g.mat).mp g.symp

def ofDetOne (m : Mat2 F) (hd : Mat2.det m = 1) : Sp2 F :=
  ⟨m, (Mat2.preserves_omega_iff_det_eq_one m).mpr hd⟩

def one : Sp2 F :=
  ⟨Mat2.I2, fun u v => by rw [Mat2.act_I2, Mat2.act_I2]⟩

def mul (g1 g2 : Sp2 F) : Sp2 F :=
  ⟨Mat2.mul g1.mat g2.mat, fun u v => by
    rw [Mat2.act_mul, Mat2.act_mul, g1.symp, g2.symp]⟩

theorem det_cliffConj (m : Mat2 F) : Mat2.det (Mat2.cliffConj m) = Mat2.det m := by
  unfold Mat2.det Mat2.cliffConj
  rw [mul_comm m.a22 m.a11, neg_mul_neg]

def inv (g : Sp2 F) : Sp2 F :=
  ofDetOne (Mat2.cliffConj g.mat) (by rw [det_cliffConj, det_eq_one g])

theorem mul_left_inv (g : Sp2 F) : mul (inv g) g = one := by
  apply ext
  apply Mat2.eq_of_act_basis
  · change Mat2.act (Mat2.mul (Mat2.cliffConj g.mat) g.mat) Vec2.e1 = Mat2.act Mat2.I2 Vec2.e1
    rw [Mat2.act_mul, Mat2.act_I2, Mat2.act_cliffConj_act, det_eq_one g]
    apply Vec2.ext <;> simp [Vec2.smul, one_mul]
  · change Mat2.act (Mat2.mul (Mat2.cliffConj g.mat) g.mat) Vec2.e2 = Mat2.act Mat2.I2 Vec2.e2
    rw [Mat2.act_mul, Mat2.act_I2, Mat2.act_cliffConj_act, det_eq_one g]
    apply Vec2.ext <;> simp [Vec2.smul, one_mul]

theorem cliffConj_cliffConj (m : Mat2 F) : Mat2.cliffConj (Mat2.cliffConj m) = m := by
  apply Mat2.ext <;> simp [Mat2.cliffConj, neg_neg]

theorem mul_right_inv (g : Sp2 F) : mul g (inv g) = one := by
  have h := mul_left_inv (inv g)
  have hinv2 : inv (inv g) = g := by
    apply ext
    exact cliffConj_cliffConj g.mat
  rw [hinv2] at h
  exact h

def groupStruct (F : Type) [CommField F] : GroupStruct (Sp2 F) where
  mul := mul
  one := one
  inv := inv
  mul_assoc a b c := ext (Mat2.mul_assoc a.mat b.mat c.mat)
  one_mul a := ext (Mat2.I2_mul a.mat)
  mul_one a := ext (Mat2.mul_I2 a.mat)
  mul_left_inv := mul_left_inv
  mul_right_inv := mul_right_inv

/-- Transvections `U₁₂ = [[1,1],[0,1]]` and `L₂₁ = [[1,0],[1,1]]` in `Sp₂(F)`. -/
def U12 : Sp2 F := ofDetOne ⟨1, 1, 0, 1⟩ (by simp [Mat2.det, mul_one, mul_zero, sub_zero])
def L21 : Sp2 F := ofDetOne ⟨1, 0, 1, 1⟩ (by simp [Mat2.det, mul_one, zero_mul, sub_zero])
def J0  : Sp2 F := ofDetOne ⟨0, -1, 1, 0⟩
  (by simp [Mat2.det, zero_mul, neg_one_mul, zero_sub, neg_neg])

/-- `Sp₂(F)` is non-abelian over EVERY field `F` (including characteristic 2!). -/
theorem nonabelian : ∃ u v : Sp2 F, mul u v ≠ mul v u := by
  refine ⟨U12, L21, ?_⟩
  intro h
  have h11 : (mul (U12 (F := F)) L21).mat.a11 = (mul L21 U12).mat.a11 :=
    congrArg (fun g => g.mat.a11) h
  simp only [mul, U12, L21, ofDetOne, Mat2.mul, mul_one, mul_zero, add_zero] at h11
  have h10 : (1 : F) = 0 := add_left_cancel (a := 1) (by rw [h11, add_zero])
  exact zero_ne_one h10.symm

/-- Central involution `-I₂ ∈ Z(Sp₂(F))` is distinct from `I₂` whenever `char(F) ≠ 2`. -/
def negOne : Sp2 F :=
  ofDetOne Mat2.negI2 (by simp [Mat2.det, Mat2.negI2, neg_mul_neg, mul_one, mul_zero, sub_zero])

theorem nontrivial_center (hchar : (1 : F) + 1 ≠ 0) :
    ∃ z₁ z₂ : Sp2 F, z₁ ≠ z₂ ∧
      (∀ y : Sp2 F, mul z₁ y = mul y z₁) ∧
      (∀ y : Sp2 F, mul z₂ y = mul y z₂) := by
  refine ⟨one, negOne, ?_, ?_, ?_⟩
  · intro heq
    have h11 : (1 : F) = -1 := congrArg (fun g => g.mat.a11) heq
    exact one_ne_neg_one hchar h11
  · intro y
    apply ext
    change Mat2.mul Mat2.I2 y.mat = Mat2.mul y.mat Mat2.I2
    rw [Mat2.I2_mul, Mat2.mul_I2]
  · intro y
    apply ext
    apply Mat2.ext <;> simp [mul, negOne, ofDetOne, Mat2.mul, Mat2.negI2,
      neg_one_mul, mul_neg, mul_one, zero_mul, mul_zero, add_zero, zero_add]

/-- Over EVERY field `F` with `char(F) ≠ 2`, `Sp₂(F)` has non-abelian derived subgroup:
    the commutators `X = [J₀, U₁₂]` and `Y = [J₀, L₂₁]` do NOT commute! -/
theorem nonmetabelian (hchar : (1 : F) + 1 ≠ 0) :
    let S := groupStruct F
    ∃ u₁ v₁ u₂ v₂ : Sp2 F,
      S.mul (S.comm u₁ v₁) (S.comm u₂ v₂) ≠ S.mul (S.comm u₂ v₂) (S.comm u₁ v₁) := by
  intro S
  refine ⟨J0, U12, J0, L21, ?_⟩
  have hX : (S.comm J0 U12).mat = ⟨1, -1, -1, 1 + 1⟩ := by
    change (mul (mul J0 U12) (mul (inv J0) (inv U12))).mat = _
    apply Mat2.ext
    · simp [mul, inv, J0, U12, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
    · simp [mul, inv, J0, U12, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
    · simp [mul, inv, J0, U12, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
    · simp [mul, inv, J0, U12, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, neg_mul_neg]
  have hY : (S.comm J0 L21).mat = ⟨1 + 1, -1, -1, 1⟩ := by
    change (mul (mul J0 L21) (mul (inv J0) (inv L21))).mat = _
    apply Mat2.ext
    · simp [mul, inv, J0, L21, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, neg_mul_neg]
    · simp [mul, inv, J0, L21, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
    · simp [mul, inv, J0, L21, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
    · simp [mul, inv, J0, L21, ofDetOne, Mat2.mul, Mat2.cliffConj,
        zero_mul, mul_zero, one_mul, mul_one, neg_one_mul, mul_neg, neg_zero, neg_neg,
        add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  intro heq
  have h12 : (Mat2.mul (S.comm J0 U12).mat (S.comm J0 L21).mat).a12 =
             (Mat2.mul (S.comm J0 L21).mat (S.comm J0 U12).mat).a12 :=
    congrArg (fun g => g.mat.a12) heq
  rw [hX, hY] at h12
  simp only [Mat2.mul, one_mul, neg_one_mul, mul_neg, mul_one] at h12
  have lhs_eq : (-1 : F) + (-1) = -((1 : F) + 1) := (neg_add 1 1).symm
  rw [lhs_eq] at h12
  have hzero : -((1 : F) + 1) = 0 := by
    apply add_left_cancel (a := -((1 : F) + 1))
    rw [← h12, add_zero]
  have htwo0 : (1 : F) + 1 = 0 := by
    rw [← neg_neg ((1 : F) + 1), hzero, neg_zero]
  exact hchar htwo0

end Sp2Group
end Sp2

/-! ### (A) Refutation of Left `Cl`-Module Automorphisms `Aut_{Cl_{1,1}(K)}(S₁)` -/

/-- Left `Cl_{1,1}(K)`-module automorphism of the minimal left ideal `S₁ ≅ Vec2 K`. -/
structure ClModAut (K : Type) [CommField K] where
  toFun   : Vec2 K → Vec2 K
  invFun  : Vec2 K → Vec2 K
  left_inv  : ∀ u : Vec2 K, invFun (toFun u) = u
  right_inv : ∀ u : Vec2 K, toFun (invFun u) = u
  equivariant : ∀ (X : Mat2 K) (u : Vec2 K), toFun (Mat2.act X u) = Mat2.act X (toFun u)

namespace ClModAut

theorem ext {K : Type} [CommField K] {f g : ClModAut K}
    (h : ∀ u : Vec2 K, f.toFun u = g.toFun u) : f = g := by
  have hfun : f.toFun = g.toFun := funext h
  have hinv : f.invFun = g.invFun := by
    funext v
    rw [← f.left_inv (g.invFun v), hfun, g.right_inv]
  cases f; cases g
  simp only at hfun hinv
  subst hfun; subst hinv; rfl

section ModAutProps
variable {K : Type} [CommField K]

def comp (f g : ClModAut K) : ClModAut K where
  toFun u := f.toFun (g.toFun u)
  invFun u := g.invFun (f.invFun u)
  left_inv u := by rw [f.left_inv, g.left_inv]
  right_inv u := by rw [g.right_inv, f.right_inv]
  equivariant X u := by rw [g.equivariant, f.equivariant]

/-- Schur's Lemma on `S₁ = M₂(K) E₁₁`: EVERY `Cl_{1,1}(K)`-equivariant map `φ : S₁ → S₁` is
    scalar multiplication by `c = (φ e₁).x`. -/
theorem eq_smul (f : ClModAut K) :
    ∃ c : K, ∀ u : Vec2 K, f.toFun u = Vec2.smul c u := by
  refine ⟨(f.toFun Vec2.e1).x, ?_⟩
  have he11 : Mat2.act (Mat2.E11 (K := K)) Vec2.e1 = Vec2.e1 := by
    apply Vec2.ext <;> simp [Mat2.act, Mat2.E11, Vec2.e1, one_mul, zero_mul, add_zero]
  have hfe1 := f.equivariant Mat2.E11 Vec2.e1
  rw [he11] at hfe1
  have hfe1_y : (f.toFun Vec2.e1).y = 0 := by
    have hy := congrArg Vec2.y hfe1
    simp only [Mat2.act, Mat2.E11, zero_mul, add_zero] at hy
    exact hy
  intro u
  let Xu : Mat2 K := ⟨u.x, 0, u.y, 0⟩
  have hXu : Mat2.act Xu Vec2.e1 = u := by
    apply Vec2.ext <;> simp [Mat2.act, Xu, Vec2.e1, mul_one, zero_mul, add_zero]
  have hfu := f.equivariant Xu Vec2.e1
  rw [hXu] at hfu
  rw [hfu]
  apply Vec2.ext
  · simp only [Mat2.act, Xu, Vec2.smul, hfe1_y, mul_zero, add_zero]
    exact mul_comm u.x _
  · simp only [Mat2.act, Xu, Vec2.smul, hfe1_y, mul_zero, add_zero]
    exact mul_comm u.y _

theorem comp_comm (f g : ClModAut K) : comp f g = comp g f := by
  rcases eq_smul f with ⟨cf, hcf⟩
  rcases eq_smul g with ⟨cg, hcg⟩
  apply ext
  intro u
  simp only [comp]
  rw [hcg, hcf, hcf, hcg]
  apply Vec2.ext
  · simp only [Vec2.smul]
    rw [← CommField.mul_assoc, ← CommField.mul_assoc, mul_comm cf cg]
  · simp only [Vec2.smul]
    rw [← CommField.mul_assoc, ← CommField.mul_assoc, mul_comm cf cg]

end ModAutProps
end ClModAut

/-- Universal Refutation (A): Over ANY fields `K` and `F`, `Aut_{Cl_{1,1}(K)}(S₁)` is NOT
    group-isomorphic to `Sp₂(F)`! -/
theorem no_iso_clModAut_sp2 {K F : Type} [CommField K] [CommField F] :
    MulEquiv (ClModAut K) ClModAut.comp (Sp2 F) Sp2.mul → False :=
  no_mulEquiv_of_abelian_nonabelian ClModAut.comp_comm Sp2.nonabelian

/-! ### (B) Refutation of `K`-Linear Automorphisms `GL_K(S₁)` -/

/-- Whenever `char(K) ≠ 2`, reflection `diag(-1, 1) ∈ GL₂(K)` is invertible (`det = -1 ≠ 0`)
    yet fails to preserve the symplectic form `ω` (`det = -1 ≠ 1`), so `GL₂(K) ≠ Sp₂(K)`. -/
theorem gl2_not_equal_sp2 {K : Type} [CommField K] (hchar : (1 : K) + 1 ≠ 0) :
    let refl : Mat2 K := ⟨-1, 0, 0, 1⟩
    Mat2.det refl ≠ 0 ∧
    ¬ (∀ u v : Vec2 K, Mat2.omega (Mat2.act refl u) (Mat2.act refl v) = Mat2.omega u v) := by
  intro refl
  have hdet : Mat2.det refl = -1 := by
    simp [refl, Mat2.det, mul_one, zero_mul, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [hdet]
    intro hm1
    have h10 : (1 : K) = 0 := by rw [← neg_neg (1 : K), hm1, neg_zero]
    exact zero_ne_one h10.symm
  · intro hsymp
    have hd1 : Mat2.det refl = 1 := (Mat2.preserves_omega_iff_det_eq_one refl).mp hsymp
    rw [hdet] at hd1
    exact one_ne_neg_one hchar hd1.symm

/-! ### (C) Refutation of Non-Unital `K`-Algebra Automorphisms `Aut_{K-alg}(S₁)` -/

section S1Algebra
variable {K : Type} [CommField K]

/-- Multiplication induced on `S₁ = M₂(K) E₁₁ ≅ Vec2 K`: `u · v = v.x • u`. -/
def s1Mul (u v : Vec2 K) : Vec2 K := ⟨u.x * v.x, u.y * v.x⟩

theorem embedS1_mul (u v : Vec2 K) :
    Mat2.mul (Mat2.embedS1 u) (Mat2.embedS1 v) = Mat2.embedS1 (s1Mul u v) := by
  apply Mat2.ext <;> simp [Mat2.mul, Mat2.embedS1, s1Mul, zero_mul, mul_zero, add_zero]

/-- Exact characterization of `Aut_{K-alg}(S₁)`: a linear automorphism `g ∈ GL₂(K)` preserves
    the ideal multiplication `s1Mul` iff `g = [[1, 0], [q, s]]` with `s ≠ 0` (`Aff₁(K)`). -/
theorem s1_alg_aut_iff_affine (g : Mat2 K) :
    (Mat2.det g ≠ 0 ∧ ∀ u v : Vec2 K, Mat2.act g (s1Mul u v) = s1Mul (Mat2.act g u) (Mat2.act g v))
    ↔ (g.a11 = 1 ∧ g.a12 = 0 ∧ g.a22 ≠ 0) := by
  constructor
  · rintro ⟨hdet, hmul⟩
    have he22 := hmul Vec2.e2 Vec2.e2
    have hs0 : s1Mul (Vec2.e2 (K := K)) Vec2.e2 = Vec2.zero := by
      apply Vec2.ext <;> simp [s1Mul, Vec2.e2, Vec2.zero, mul_zero]
    rw [hs0] at he22
    have hx0 : (Mat2.act g Vec2.zero).x = (s1Mul (Mat2.act g Vec2.e2) (Mat2.act g Vec2.e2)).x :=
      congrArg Vec2.x he22
    simp only [Mat2.act, Vec2.zero, Vec2.e2, s1Mul, mul_zero, mul_one, add_zero, zero_add] at hx0
    have ha12 : g.a12 = 0 := sq_eq_zero hx0.symm
    have hdet' : g.a11 * g.a22 ≠ 0 := by
      unfold Mat2.det at hdet
      rw [ha12, zero_mul, sub_zero] at hdet
      exact hdet
    have ha11_ne : g.a11 ≠ 0 := by
      intro hz; rw [hz, zero_mul] at hdet'; exact hdet' rfl
    have ha22_ne : g.a22 ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hdet'; exact hdet' rfl
    have he11 := hmul Vec2.e1 Vec2.e1
    have hs1 : s1Mul (Vec2.e1 (K := K)) Vec2.e1 = Vec2.e1 := by
      apply Vec2.ext <;> simp [s1Mul, Vec2.e1, mul_one, mul_zero]
    rw [hs1] at he11
    have hx1 : (Mat2.act g Vec2.e1).x = (s1Mul (Mat2.act g Vec2.e1) (Mat2.act g Vec2.e1)).x :=
      congrArg Vec2.x he11
    simp only [Mat2.act, Vec2.e1, s1Mul, mul_one, mul_zero, add_zero] at hx1
    have ha11_one : g.a11 = 1 :=
      (mul_left_cancel ha11_ne (by rw [mul_one]; exact hx1)).symm
    exact ⟨ha11_one, ha12, ha22_ne⟩
  · rintro ⟨h11, h12, h22⟩
    refine ⟨?_, ?_⟩
    · unfold Mat2.det
      rw [h11, h12, one_mul, zero_mul, sub_zero]
      exact h22
    · intro u v
      apply Vec2.ext
      · simp only [Mat2.act, s1Mul, h11, h12, one_mul, zero_mul, add_zero]
      · simp only [Mat2.act, s1Mul, h11, h12, one_mul, zero_mul, add_zero]
        rw [right_distrib, CommField.mul_assoc, CommField.mul_assoc]

end S1Algebra

/-- 1D affine group `Aff₁(K) = K ⋊ Kˣ ≅ Aut_{K-alg}(S₁)`. -/
structure Aff1 (K : Type) [CommField K] where
  q  : K
  s  : K
  hs : s ≠ 0

namespace Aff1

theorem ext {K : Type} [CommField K] {a b : Aff1 K} (hq : a.q = b.q) (hs : a.s = b.s) : a = b := by
  cases a; cases b; simp only at hq hs; subst hq; subst hs; rfl

section Aff1Group
variable {K : Type} [CommField K]

theorem mul_ne_zero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  cases mul_eq_zero h with
  | inl h0 => exact ha h0
  | inr h0 => exact hb h0

def one : Aff1 K := ⟨0, 1, zero_ne_one.symm⟩

def mul (a b : Aff1 K) : Aff1 K :=
  ⟨a.q + a.s * b.q, a.s * b.s, mul_ne_zero a.hs b.hs⟩

def inv (a : Aff1 K) : Aff1 K :=
  ⟨-(CommField.inv a.s * a.q), CommField.inv a.s, inv_ne_zero a.hs⟩

def groupStruct : GroupStruct (Aff1 K) where
  mul := mul
  one := one
  inv := inv
  mul_assoc a b c := by
    apply ext
    · simp only [mul]
      rw [left_distrib, add_assoc, CommField.mul_assoc]
    · exact CommField.mul_assoc a.s b.s c.s
  one_mul a := by
    apply ext
    · simp [mul, one, zero_add, one_mul]
    · simp [mul, one, one_mul]
  mul_one a := by
    apply ext
    · simp [mul, one, mul_zero, add_zero]
    · simp [mul, one, mul_one]
  mul_left_inv a := by
    apply ext
    · simp only [mul, inv, one]
      exact neg_add_cancel _
    · exact inv_mul_cancel a.hs
  mul_right_inv a := by
    apply ext
    · simp only [mul, inv, one]
      rw [mul_neg, ← CommField.mul_assoc, mul_inv_cancel a.s a.hs, one_mul, add_neg_cancel]
    · exact mul_inv_cancel a.s a.hs

theorem comm_s_eq_one (a b : Aff1 K) :
    ((groupStruct (K := K)).comm a b).s = 1 := by
  change ((a.s * b.s) * (CommField.inv a.s * CommField.inv b.s)) = 1
  calc
    (a.s * b.s) * (CommField.inv a.s * CommField.inv b.s)
      = a.s * (b.s * (CommField.inv a.s * CommField.inv b.s)) := CommField.mul_assoc _ _ _
    _ = a.s * (CommField.inv a.s * (b.s * CommField.inv b.s)) := by
          rw [← CommField.mul_assoc b.s, mul_comm b.s (CommField.inv a.s), CommField.mul_assoc]
    _ = (a.s * CommField.inv a.s) * (b.s * CommField.inv b.s) := (CommField.mul_assoc _ _ _).symm
    _ = 1 * 1 := by rw [mul_inv_cancel a.s a.hs, mul_inv_cancel b.s b.hs]
    _ = 1 := one_mul 1

theorem metabelian (a₁ b₁ a₂ b₂ : Aff1 K) :
    let S := groupStruct (K := K)
    S.mul (S.comm a₁ b₁) (S.comm a₂ b₂) = S.mul (S.comm a₂ b₂) (S.comm a₁ b₁) := by
  intro S
  have hs1 : (S.comm a₁ b₁).s = 1 := comm_s_eq_one a₁ b₁
  have hs2 : (S.comm a₂ b₂).s = 1 := comm_s_eq_one a₂ b₂
  apply ext
  · change (S.comm a₁ b₁).q + (S.comm a₁ b₁).s * (S.comm a₂ b₂).q =
           (S.comm a₂ b₂).q + (S.comm a₂ b₂).s * (S.comm a₁ b₁).q
    rw [hs1, hs2, one_mul, one_mul, add_comm]
  · change (S.comm a₁ b₁).s * (S.comm a₂ b₂).s = (S.comm a₂ b₂).s * (S.comm a₁ b₁).s
    rw [hs1, hs2]

end Aff1Group
end Aff1

/-- Universal Refutation (C): Over ANY field `K` and ANY field `F` with `char(F) ≠ 2`,
    `Aut_{K-alg}(S₁) ≅ Aff₁(K)` is NOT group-isomorphic to `Sp₂(F)`! -/
theorem no_iso_s1AlgAut_sp2 {K F : Type} [CommField K] [CommField F]
    (hchar : (1 : F) + 1 ≠ 0) :
    MulEquiv (Aff1 K) Aff1.mul (Sp2 F) Sp2.mul → False :=
  GroupStruct.no_mulEquiv_of_metabelian_vs_nonmetabelian
    (Aff1.groupStruct (K := K)) (Sp2.groupStruct F) Aff1.metabelian (Sp2.nonmetabelian hchar)

/-! ### (D) Refutation of Unital `K`-Algebra Automorphisms `Aut_{K-alg}(M₂(K))` -/

/-- Unital `K`-algebra automorphism of the minimal two-sided ideal `J = M₂(K) ≅ Cl_{1,1}(K)`. -/
structure Mat2AlgAut (K : Type) [CommField K] where
  toFun   : Mat2 K → Mat2 K
  invFun  : Mat2 K → Mat2 K
  left_inv  : ∀ X : Mat2 K, invFun (toFun X) = X
  right_inv : ∀ X : Mat2 K, toFun (invFun X) = X
  map_I2    : toFun Mat2.I2 = Mat2.I2
  map_add   : ∀ X Y : Mat2 K, toFun (Mat2.add X Y) = Mat2.add (toFun X) (toFun Y)
  map_smul  : ∀ (c : K) (X : Mat2 K), toFun (Mat2.smul c X) = Mat2.smul c (toFun X)
  map_mul   : ∀ X Y : Mat2 K, toFun (Mat2.mul X Y) = Mat2.mul (toFun X) (toFun Y)

namespace Mat2AlgAut

theorem ext {K : Type} [CommField K] {α β : Mat2AlgAut K}
    (h : ∀ X : Mat2 K, α.toFun X = β.toFun X) : α = β := by
  have hfun : α.toFun = β.toFun := funext h
  have hinv : α.invFun = β.invFun := by
    funext Y
    rw [← α.left_inv (β.invFun Y), hfun, β.right_inv]
  cases α; cases β
  simp only at hfun hinv
  subst hfun; subst hinv; rfl

section AlgAutCenter
variable {K : Type} [CommField K]

theorem add_add_add_comm (a b c d : K) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b c d, add_comm b c, add_assoc, ← add_assoc]

theorem mul_left_comm (a b c : K) : a * (b * c) = b * (a * c) := by
  rw [← CommField.mul_assoc, mul_comm a b, CommField.mul_assoc]

theorem mat2_mul_add (P Q R : Mat2 K) :
    Mat2.mul P (Mat2.add Q R) = Mat2.add (Mat2.mul P Q) (Mat2.mul P R) := by
  apply Mat2.ext <;> simp only [Mat2.mul, Mat2.add, left_distrib, add_add_add_comm]

theorem mat2_add_mul (P Q R : Mat2 K) :
    Mat2.mul (Mat2.add P Q) R = Mat2.add (Mat2.mul P R) (Mat2.mul Q R) := by
  apply Mat2.ext <;> simp only [Mat2.mul, Mat2.add, right_distrib, add_add_add_comm]

theorem mat2_smul_mul (c : K) (P Q : Mat2 K) :
    Mat2.mul (Mat2.smul c P) Q = Mat2.smul c (Mat2.mul P Q) := by
  apply Mat2.ext <;> simp only [Mat2.mul, Mat2.smul, left_distrib, CommField.mul_assoc]

theorem mat2_mul_smul (c : K) (P Q : Mat2 K) :
    Mat2.mul P (Mat2.smul c Q) = Mat2.smul c (Mat2.mul P Q) := by
  apply Mat2.ext <;> simp only [Mat2.mul, Mat2.smul, left_distrib, mul_left_comm]

def id : Mat2AlgAut K where
  toFun X := X
  invFun X := X
  left_inv _ := rfl
  right_inv _ := rfl
  map_I2 := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_mul _ _ := rfl

def comp (α β : Mat2AlgAut K) : Mat2AlgAut K where
  toFun X := α.toFun (β.toFun X)
  invFun X := β.invFun (α.invFun X)
  left_inv X := by rw [α.left_inv, β.left_inv]
  right_inv X := by rw [β.right_inv, α.right_inv]
  map_I2 := by rw [β.map_I2, α.map_I2]
  map_add X Y := by rw [β.map_add, α.map_add]
  map_smul c X := by rw [β.map_smul, α.map_smul]
  map_mul X Y := by rw [β.map_mul, α.map_mul]

def ofInner (g gInv : Mat2 K)
    (hLR : Mat2.mul g gInv = Mat2.I2) (hRL : Mat2.mul gInv g = Mat2.I2) : Mat2AlgAut K where
  toFun X := Mat2.mul (Mat2.mul g X) gInv
  invFun X := Mat2.mul (Mat2.mul gInv X) g
  left_inv X := by
    rw [← Mat2.mul_assoc, ← Mat2.mul_assoc gInv g X, hRL, Mat2.I2_mul,
        Mat2.mul_assoc, hRL, Mat2.mul_I2]
  right_inv X := by
    rw [← Mat2.mul_assoc, ← Mat2.mul_assoc g gInv X, hLR, Mat2.I2_mul,
        Mat2.mul_assoc, hLR, Mat2.mul_I2]
  map_I2 := by rw [Mat2.mul_I2, hLR]
  map_add X Y := by rw [mat2_mul_add, mat2_add_mul]
  map_smul c X := by rw [mat2_mul_smul, mat2_smul_mul]
  map_mul X Y := by
    calc
      Mat2.mul (Mat2.mul g (Mat2.mul X Y)) gInv
        = Mat2.mul (Mat2.mul (Mat2.mul g X) Mat2.I2) (Mat2.mul Y gInv) := by
            rw [Mat2.mul_I2, ← Mat2.mul_assoc g X Y, Mat2.mul_assoc]
      _ = Mat2.mul (Mat2.mul (Mat2.mul g X) (Mat2.mul gInv g)) (Mat2.mul Y gInv) := by
            rw [hRL]
      _ = Mat2.mul (Mat2.mul (Mat2.mul g X) gInv) (Mat2.mul (Mat2.mul g Y) gInv) := by
            rw [← Mat2.mul_assoc (Mat2.mul g X) gInv g,
                Mat2.mul_assoc (Mat2.mul (Mat2.mul g X) gInv) g (Mat2.mul Y gInv),
                ← Mat2.mul_assoc g Y gInv]

theorem map_zero (α : Mat2AlgAut K) : α.toFun Mat2.zero = Mat2.zero := by
  have hz : (Mat2.zero (K := K)) = Mat2.smul 0 Mat2.I2 := by
    apply Mat2.ext <;> simp [Mat2.zero, Mat2.smul, Mat2.I2, zero_mul]
  rw [hz, α.map_smul, α.map_I2, ← hz]

theorem map_sub (α : Mat2AlgAut K) (X Y : Mat2 K) :
    α.toFun (Mat2.sub X Y) = Mat2.sub (α.toFun X) (α.toFun Y) := by
  have hsub : ∀ P Q : Mat2 K, Mat2.sub P Q = Mat2.add P (Mat2.smul (-1) Q) := by
    intro P Q
    apply Mat2.ext <;> simp [Mat2.sub, Mat2.add, Mat2.smul, sub_eq_add_neg, neg_one_mul]
  rw [hsub X Y, α.map_add, α.map_smul, ← hsub]

theorem scalar_of_comm_E12_E21 {M : Mat2 K}
    (h12 : Mat2.mul M Mat2.E12 = Mat2.mul Mat2.E12 M)
    (h21 : Mat2.mul M Mat2.E21 = Mat2.mul Mat2.E21 M) :
    M = Mat2.smul M.a11 Mat2.I2 := by
  have c21 := congrArg Mat2.a11 h12
  have c22 := congrArg Mat2.a12 h12
  have c12 := congrArg Mat2.a22 h21
  simp only [Mat2.mul, Mat2.E12, Mat2.E21, mul_zero, zero_mul, mul_one, one_mul,
    add_zero, zero_add] at c21 c22 c12
  apply Mat2.ext
  · simp [Mat2.smul, Mat2.I2, mul_one]
  · simp [Mat2.smul, Mat2.I2, mul_zero, c12.symm]
  · simp [Mat2.smul, Mat2.I2, mul_zero, c21.symm]
  · simp [Mat2.smul, Mat2.I2, mul_one, c22.symm]

theorem central_maps_invertible_to_smul (α : Mat2AlgAut K)
    (hcenter : ∀ β : Mat2AlgAut K, comp α β = comp β α)
    (g gInv : Mat2 K)
    (hLR : Mat2.mul g gInv = Mat2.I2) (hRL : Mat2.mul gInv g = Mat2.I2) :
    ∃ c : K, α.toFun g = Mat2.smul c g := by
  let β := ofInner g gInv hLR hRL
  have hc := hcenter β
  have hcomm_M : ∀ X : Mat2 K,
      Mat2.mul (Mat2.mul gInv (α.toFun g)) X = Mat2.mul X (Mat2.mul gInv (α.toFun g)) := by
    intro X
    have hpt : (comp α β).toFun (α.invFun X) = (comp β α).toFun (α.invFun X) :=
      congrArg (fun γ => γ.toFun (α.invFun X)) hc
    simp only [comp, β, ofInner] at hpt
    rw [α.map_mul, α.map_mul, α.right_inv] at hpt
    have hinv_ag : Mat2.mul (α.toFun gInv) (α.toFun g) = Mat2.I2 := by
      rw [← α.map_mul, hRL, α.map_I2]
    have hpt2 : Mat2.mul (Mat2.mul (Mat2.mul (α.toFun g) X) (α.toFun gInv)) (α.toFun g) =
                Mat2.mul (Mat2.mul (Mat2.mul g X) gInv) (α.toFun g) :=
      congrArg (fun Z => Mat2.mul Z (α.toFun g)) hpt
    rw [Mat2.mul_assoc (Mat2.mul (α.toFun g) X) (α.toFun gInv) (α.toFun g),
        hinv_ag, Mat2.mul_I2] at hpt2
    have hpt3 : Mat2.mul gInv (Mat2.mul (α.toFun g) X) =
                Mat2.mul gInv (Mat2.mul (Mat2.mul (Mat2.mul g X) gInv) (α.toFun g)) :=
      congrArg (fun Z => Mat2.mul gInv Z) hpt2
    rw [← Mat2.mul_assoc gInv (α.toFun g) X] at hpt3
    calc
      Mat2.mul (Mat2.mul gInv (α.toFun g)) X
        = Mat2.mul gInv (Mat2.mul (Mat2.mul (Mat2.mul g X) gInv) (α.toFun g)) := hpt3
      _ = Mat2.mul (Mat2.mul (Mat2.mul gInv g) X) (Mat2.mul gInv (α.toFun g)) := by
            rw [← Mat2.mul_assoc gInv (Mat2.mul (Mat2.mul g X) gInv) (α.toFun g),
                ← Mat2.mul_assoc gInv (Mat2.mul g X) gInv,
                ← Mat2.mul_assoc gInv g X,
                Mat2.mul_assoc (Mat2.mul (Mat2.mul gInv g) X) gInv (α.toFun g)]
      _ = Mat2.mul X (Mat2.mul gInv (α.toFun g)) := by
            rw [hRL, Mat2.I2_mul]
  let M := Mat2.mul gInv (α.toFun g)
  let c := M.a11
  have hM : M = Mat2.smul c Mat2.I2 :=
    scalar_of_comm_E12_E21 (hcomm_M Mat2.E12) (hcomm_M Mat2.E21)
  refine ⟨c, ?_⟩
  calc
    α.toFun g = Mat2.mul Mat2.I2 (α.toFun g) := (Mat2.I2_mul _).symm
    _ = Mat2.mul (Mat2.mul g gInv) (α.toFun g) := by rw [hLR]
    _ = Mat2.mul g M := Mat2.mul_assoc g gInv (α.toFun g)
    _ = Mat2.mul g (Mat2.smul c Mat2.I2) := by rw [hM]
    _ = Mat2.smul c (Mat2.mul g Mat2.I2) := mat2_mul_smul c g Mat2.I2
    _ = Mat2.smul c g := by rw [Mat2.mul_I2]

/-- Elementary center theorem (without Skolem–Noether): the center of `Aut_{K-alg}(M₂(K))`
    is trivial over EVERY field `K` (of ANY characteristic)! -/
theorem center_trivial (α : Mat2AlgAut K)
    (hcenter : ∀ β : Mat2AlgAut K, comp α β = comp β α) : α = id := by
  -- Step 1: Fix `E₁₂` via `g₁ = I₂ + E₁₂ = [[1,1],[0,1]]`
  let g1 : Mat2 K := ⟨1, 1, 0, 1⟩
  let g1Inv : Mat2 K := ⟨1, -1, 0, 1⟩
  have h1LR : Mat2.mul g1 g1Inv = Mat2.I2 := by
    apply Mat2.ext <;> simp [g1, g1Inv, Mat2.mul, Mat2.I2,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  have h1RL : Mat2.mul g1Inv g1 = Mat2.I2 := by
    apply Mat2.ext <;> simp [g1, g1Inv, Mat2.mul, Mat2.I2,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  rcases central_maps_invertible_to_smul α hcenter g1 g1Inv h1LR h1RL with ⟨c1, hc1⟩
  have hg1_sub : Mat2.sub g1 Mat2.I2 = Mat2.E12 := by
    apply Mat2.ext <;> simp [g1, Mat2.sub, Mat2.I2, Mat2.E12, sub_self, sub_zero]
  have haE12 : α.toFun Mat2.E12 = ⟨c1 - 1, c1, 0, c1 - 1⟩ := by
    rw [← hg1_sub, map_sub, hc1, α.map_I2]
    apply Mat2.ext <;> simp [g1, Mat2.sub, Mat2.smul, Mat2.I2, mul_one, mul_zero, sub_zero]
  have hE12_sq : Mat2.mul (Mat2.E12 (K := K)) Mat2.E12 = Mat2.zero := by
    apply Mat2.ext <;> simp [Mat2.mul, Mat2.E12, Mat2.zero, zero_mul, mul_zero, add_zero]
  have haE12_sq : Mat2.mul (α.toFun Mat2.E12) (α.toFun Mat2.E12) = Mat2.zero := by
    rw [← α.map_mul, hE12_sq, map_zero]
  rw [haE12] at haE12_sq
  have hc1_sq : (c1 - 1) * (c1 - 1) = 0 := by
    have h11 := congrArg Mat2.a11 haE12_sq
    simp only [Mat2.mul, Mat2.zero, mul_zero, add_zero] at h11
    exact h11
  have hc1_eq : c1 = 1 := eq_of_sub_eq_zero (sq_eq_zero hc1_sq)
  have hfixE12 : α.toFun Mat2.E12 = Mat2.E12 := by
    rw [haE12, hc1_eq, sub_self]
    rfl
  -- Step 2: Fix `E₂₁` via `g₂ = I₂ + E₂₁ = [[1,0],[1,1]]`
  let g2 : Mat2 K := ⟨1, 0, 1, 1⟩
  let g2Inv : Mat2 K := ⟨1, 0, -1, 1⟩
  have h2LR : Mat2.mul g2 g2Inv = Mat2.I2 := by
    apply Mat2.ext <;> simp [g2, g2Inv, Mat2.mul, Mat2.I2,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  have h2RL : Mat2.mul g2Inv g2 = Mat2.I2 := by
    apply Mat2.ext <;> simp [g2, g2Inv, Mat2.mul, Mat2.I2,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel, neg_add_cancel]
  rcases central_maps_invertible_to_smul α hcenter g2 g2Inv h2LR h2RL with ⟨c2, hc2⟩
  have hg2_sub : Mat2.sub g2 Mat2.I2 = Mat2.E21 := by
    apply Mat2.ext <;> simp [g2, Mat2.sub, Mat2.I2, Mat2.E21, sub_self, sub_zero]
  have haE21 : α.toFun Mat2.E21 = ⟨c2 - 1, 0, c2, c2 - 1⟩ := by
    rw [← hg2_sub, map_sub, hc2, α.map_I2]
    apply Mat2.ext <;> simp [g2, Mat2.sub, Mat2.smul, Mat2.I2, mul_one, mul_zero, sub_zero]
  have hE21_sq : Mat2.mul (Mat2.E21 (K := K)) Mat2.E21 = Mat2.zero := by
    apply Mat2.ext <;> simp [Mat2.mul, Mat2.E21, Mat2.zero, zero_mul, mul_zero, add_zero]
  have haE21_sq : Mat2.mul (α.toFun Mat2.E21) (α.toFun Mat2.E21) = Mat2.zero := by
    rw [← α.map_mul, hE21_sq, map_zero]
  rw [haE21] at haE21_sq
  have hc2_sq : (c2 - 1) * (c2 - 1) = 0 := by
    have h11 := congrArg Mat2.a11 haE21_sq
    simp only [Mat2.mul, Mat2.zero, zero_mul, add_zero] at h11
    exact h11
  have hc2_eq : c2 = 1 := eq_of_sub_eq_zero (sq_eq_zero hc2_sq)
  have hfixE21 : α.toFun Mat2.E21 = Mat2.E21 := by
    rw [haE21, hc2_eq, sub_self]
    rfl
  -- Step 3: Fix `E₁₁ = E₁₂ E₂₁` and `E₂₂ = E₂₁ E₁₂`, hence all of `M₂(K)`!
  have hE11_prod : Mat2.mul (Mat2.E12 (K := K)) Mat2.E21 = Mat2.E11 := by
    apply Mat2.ext <;> simp [Mat2.mul, Mat2.E12, Mat2.E21, Mat2.E11,
      one_mul, zero_mul, mul_zero, zero_add, add_zero]
  have hE22_prod : Mat2.mul (Mat2.E21 (K := K)) Mat2.E12 = Mat2.E22 := by
    apply Mat2.ext <;> simp [Mat2.mul, Mat2.E21, Mat2.E12, Mat2.E22,
      one_mul, zero_mul, mul_zero, zero_add, add_zero]
  have hfixE11 : α.toFun Mat2.E11 = Mat2.E11 := by
    rw [← hE11_prod, α.map_mul, hfixE12, hfixE21, hE11_prod]
  have hfixE22 : α.toFun Mat2.E22 = Mat2.E22 := by
    rw [← hE22_prod, α.map_mul, hfixE21, hfixE12, hE22_prod]
  apply ext
  intro X
  calc
    α.toFun X
      = α.toFun (Mat2.add (Mat2.add (Mat2.smul X.a11 Mat2.E11) (Mat2.smul X.a12 Mat2.E12))
                          (Mat2.add (Mat2.smul X.a21 Mat2.E21) (Mat2.smul X.a22 Mat2.E22))) := by
          rw [Mat2.mat2_basis_decomp X]
    _ = Mat2.add (Mat2.add (Mat2.smul X.a11 Mat2.E11) (Mat2.smul X.a12 Mat2.E12))
                 (Mat2.add (Mat2.smul X.a21 Mat2.E21) (Mat2.smul X.a22 Mat2.E22)) := by
          rw [α.map_add, α.map_add, α.map_add,
              α.map_smul, α.map_smul, α.map_smul, α.map_smul,
              hfixE11, hfixE12, hfixE21, hfixE22]
    _ = X := Mat2.mat2_basis_decomp X

end AlgAutCenter
end Mat2AlgAut

/-- Universal Refutation (D): Over ANY field `K` and ANY field `F` with `char(F) ≠ 2`,
    `Aut_{K-alg}(M₂(K))` has trivial center while `Sp₂(F)` has nontrivial center `{±I₂}`,
    so NO group isomorphism exists! -/
theorem no_iso_mat2AlgAut_sp2 {K F : Type} [CommField K] [CommField F]
    (hchar : (1 : F) + 1 ≠ 0) :
    MulEquiv (Mat2AlgAut K) Mat2AlgAut.comp (Sp2 F) Sp2.mul → False :=
  no_mulEquiv_of_trivial_center Mat2AlgAut.id Mat2AlgAut.center_trivial
    (Sp2.nontrivial_center hchar)

/-! ### Exact Finite-Group Order Spectrum `{2, 6, 8, 24, 48}` on `S₁ ≅ 𝔽₃²` & Mod-8 Periodicity -/

namespace F3Spectrum

def concatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ concatMap f l

def allVec2 : List (Vec2 F3) :=
  concatMap (fun x => F3.elems.map (fun y => Vec2.mk x y)) F3.elems

def allMat2 : List (Mat2 F3) :=
  concatMap (fun a11 =>
    concatMap (fun a12 =>
      concatMap (fun a21 =>
        F3.elems.map (fun a22 => Mat2.mk a11 a12 a21 a22))
      F3.elems)
    F3.elems)
  F3.elems

theorem allMat2_nodup : nodupBool allMat2 = true := by decide

theorem mem_allMat2 (M : Mat2 F3) : M ∈ allMat2 := by
  cases M with
  | mk a b c d => cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- General subtype filter preserving duplicate-freeness and completeness. -/
def filterSub {α : Type} (p : α → Bool) : List α → List { x : α // p x = true }
  | [] => []
  | a :: l =>
    if ha : p a = true then ⟨a, ha⟩ :: filterSub p l
    else filterSub p l

theorem filterSub_nodup {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ {l : List α}, NodupList l → NodupList (filterSub p l)
  | [], NodupList.nil => NodupList.nil
  | a :: l, NodupList.cons hnotmem htl => by
    unfold filterSub
    split
    · next ha =>
      refine NodupList.cons ?_ (filterSub_nodup p htl)
      intro hm
      have hmem_sub : ∀ {s : { x : α // p x = true }} {xs : List α},
          s ∈ filterSub p xs → s.1 ∈ xs := by
        intro s xs hsm
        induction xs with
        | nil => nomatch hsm
        | cons b bs ih =>
          unfold filterSub at hsm
          split at hsm
          · cases hsm with
            | head => exact List.Mem.head _
            | tail _ htail => exact List.Mem.tail _ (ih htail)
          · exact List.Mem.tail _ (ih hsm)
      exact hnotmem (hmem_sub hm)
    · exact filterSub_nodup p htl

theorem mem_filterSub {α : Type} (p : α → Bool) :
    ∀ {l : List α} (s : { x : α // p x = true }), s.1 ∈ l → s ∈ filterSub p l
  | [], _, h => nomatch h
  | a :: l, ⟨x, hx⟩, h => by
    unfold filterSub
    cases h with
    | head =>
      simp only [hx, ↓reduceDIte]
      exact List.Mem.head _
    | tail _ htl =>
      split
      · exact List.Mem.tail _ (mem_filterSub p ⟨x, hx⟩ htl)
      · exact mem_filterSub p ⟨x, hx⟩ htl

theorem filterSub_length {α : Type} (p : α → Bool) :
    ∀ (l : List α), (filterSub p l).length = (l.filter p).length
  | [] => rfl
  | a :: l => by
    unfold filterSub List.filter
    by_cases ha : p a = true
    · simp [ha, filterSub_length p l]
    · have hfalse : p a = false := by
        cases hpa : p a with
        | true => exact absurd hpa ha
        | false => rfl
      simp [ha, hfalse, filterSub_length p l]

/-- Non-bijection between two decidable subtypes of `Mat2 F3` with distinct filter counts. -/
theorem no_bij_subtypes_of_count_ne (p q : Mat2 F3 → Bool)
    (hne : (allMat2.filter p).length ≠ (allMat2.filter q).length)
    (f : { x : Mat2 F3 // p x = true } → { y : Mat2 F3 // q y = true })
    (g : { y : Mat2 F3 // q y = true } → { x : Mat2 F3 // p x = true })
    (hleft : ∀ x, g (f x) = x) (hright : ∀ y, f (g y) = y) : False := by
  have hnd : NodupList allMat2 := nodupList_of_nodupBool allMat2_nodup
  have hndP : NodupList (filterSub p allMat2) := filterSub_nodup p hnd
  have hndQ : NodupList (filterSub q allMat2) := filterSub_nodup q hnd
  have hinj_f : ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂ := by
    intro x₁ x₂ hf; rw [← hleft x₁, ← hleft x₂, hf]
  have hinj_g : ∀ y₁ y₂, g y₁ = g y₂ → y₁ = y₂ := by
    intro y₁ y₂ hg; rw [← hright y₁, ← hright y₂, hg]
  have hle1 : (filterSub p allMat2).length ≤ (filterSub q allMat2).length := by
    have hmap := nodupList_map hinj_f hndP
    have hlen : ((filterSub p allMat2).map f).length = (filterSub p allMat2).length := by simp
    rw [← hlen]
    exact nodup_length_le _ _ hmap (fun y _ => mem_filterSub q y (mem_allMat2 y.1))
  have hle2 : (filterSub q allMat2).length ≤ (filterSub p allMat2).length := by
    have hmap := nodupList_map hinj_g hndQ
    have hlen : ((filterSub q allMat2).map g).length = (filterSub q allMat2).length := by simp
    rw [← hlen]
    exact nodup_length_le _ _ hmap (fun x _ => mem_filterSub p x (mem_allMat2 x.1))
  have heq : (allMat2.filter p).length = (allMat2.filter q).length := by
    rw [← filterSub_length p allMat2, ← filterSub_length q allMat2]
    exact Nat.le_antisymm hle1 hle2
  exact hne heq

/-- Decidable predicates for the 5 matrix groups acting on the 2D spinor space `S₁ ≅ 𝔽₃²`:
    1. `isClModAutB`: `GL₂(𝔽₃)` commuting with `Cl_{1,1}(𝔽₃)` (`|G| = 2`),
    2. `isS1AlgAutB`: `GL₂(𝔽₃)` preserving left-ideal product `s1Mul` (`|G| = 6`),
    3. `isOrthogCl20B`: `GL₂(𝔽₃)` preserving Euclidean reversion form `u·v` of `Cl_{2,0}(𝔽₃)` (`|G| = 8`),
    4. `isSp2B`: `GL₂(𝔽₃)` preserving symplectic form `ω` (`|Sp₂(𝔽₃)| = 24`),
    5. `isGL2B`: full linear automorphism group `GL₂(𝔽₃)` (`|GL₂(𝔽₃)| = 48`). -/
def isGL2B (g : Mat2 F3) : Bool := Mat2.det g != 0

def isClModAutB (g : Mat2 F3) : Bool :=
  isGL2B g &&
  (Mat2.mul g Mat2.cl11_g1 == Mat2.mul Mat2.cl11_g1 g) &&
  (Mat2.mul g Mat2.cl11_g2 == Mat2.mul Mat2.cl11_g2 g)

def isS1AlgAutB (g : Mat2 F3) : Bool :=
  isGL2B g &&
  allVec2.all (fun u =>
    allVec2.all (fun v =>
      Mat2.act g (s1Mul u v) == s1Mul (Mat2.act g u) (Mat2.act g v)))

def dotF3 (u v : Vec2 F3) : F3 := u.x * v.x + u.y * v.y

def isOrthogCl20B (g : Mat2 F3) : Bool :=
  allVec2.all (fun u =>
    allVec2.all (fun v =>
      dotF3 (Mat2.act g u) (Mat2.act g v) == dotF3 u v))

def isSp2B (g : Mat2 F3) : Bool :=
  allVec2.all (fun u =>
    allVec2.all (fun v =>
      Mat2.omega (Mat2.act g u) (Mat2.act g v) == Mat2.omega u v))

/-- Exact finite-group order spectrum `{2, 6, 8, 24, 48}` over `𝔽₃`, certified by kernel `decide`! -/
theorem f3_exact_group_orders :
    (allMat2.filter isClModAutB).length = 2 ∧
    (allMat2.filter isS1AlgAutB).length = 6 ∧
    (allMat2.filter isOrthogCl20B).length = 8 ∧
    (allMat2.filter isSp2B).length = 24 ∧
    (allMat2.filter isGL2B).length = 48 := by
  decide

/-- None of `Aut_{Cl}(S₁)`, `Aut_{alg}(S₁)`, `O₂(𝔽₃)` (`Cl_{2,0}` reversion form), or `GL₂(𝔽₃)`
    admits a bijection (let alone a group isomorphism!) with `Sp₂(𝔽₃)`. -/
theorem f3_all_four_not_bijective_to_sp2 :
    (∀ (f : {m // isClModAutB m = true} → {m // isSp2B m = true})
       (g : {m // isSp2B m = true} → {m // isClModAutB m = true}),
        (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → False) ∧
    (∀ (f : {m // isS1AlgAutB m = true} → {m // isSp2B m = true})
       (g : {m // isSp2B m = true} → {m // isS1AlgAutB m = true}),
        (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → False) ∧
    (∀ (f : {m // isOrthogCl20B m = true} → {m // isSp2B m = true})
       (g : {m // isSp2B m = true} → {m // isOrthogCl20B m = true}),
        (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → False) ∧
    (∀ (f : {m // isGL2B m = true} → {m // isSp2B m = true})
       (g : {m // isSp2B m = true} → {m // isGL2B m = true}),
        (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → False) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g hl hr
    exact no_bij_subtypes_of_count_ne isClModAutB isSp2B (by decide) f g hl hr
  · intro f g hl hr
    exact no_bij_subtypes_of_count_ne isS1AlgAutB isSp2B (by decide) f g hl hr
  · intro f g hl hr
    exact no_bij_subtypes_of_count_ne isOrthogCl20B isSp2B (by decide) f g hl hr
  · intro f g hl hr
    exact no_bij_subtypes_of_count_ne isGL2B isSp2B (by decide) f g hl hr

end F3Spectrum

/-! ### Mod-8 Periodicity Obstruction at `n = 8` (`Cl_{4,4}(K) ≅ M₁₆(K)`):
    Neither Reversion Nor Clifford Conjugation Is Symplectic! -/

namespace Mod8Periodicity

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Reversion fixes `k`-blades iff `k ≡ 0, 1 (mod 4)`. -/
def revFixed (k : Nat) : Bool := (k % 4 == 0) || (k % 4 == 1)

/-- Clifford conjugation fixes `k`-blades iff `k ≡ 0, 3 (mod 4)`. -/
def conjFixed (k : Nat) : Bool := (k % 4 == 0) || (k % 4 == 3)

def countFixedBlades (n : Nat) (pred : Nat → Bool) : Nat :=
  (List.range (n + 1)).foldl (fun acc k => if pred k then acc + binom n k else acc) 0

/-- Dimension of the `+1`-eigenspace of `X ↦ B⁻¹ Xᵀ B` on `M_N(K)`:
    `N(N+1)/2` when `Bᵀ = +B` (orthogonal `O_N`), vs. `N(N-1)/2` when `Bᵀ = -B` (symplectic `Sp_N`). -/
def symDim (N : Nat) : Nat := N * (N + 1) / 2
def skewDim (N : Nat) : Nat := N * (N - 1) / 2

/-- At `n = 8` (`Cl_{4,4}(K) ≅ M₁₆(K)`, spinor dimension `N = 16`, total dimension `256`),
    BOTH reversion and Clifford conjugation have `136 = symDim 16` fixed basis blades, strictly
    exceeding `120 = skewDim 16`, so BOTH canonical anti-involutions induce symmetric (`O₁₆`)
    spinor bilinear forms and NEITHER induces a symplectic (`Sp₁₆`) form! -/
theorem cl8_both_involutions_orthogonal_not_symplectic :
    countFixedBlades 8 revFixed = 136 ∧
    countFixedBlades 8 conjFixed = 136 ∧
    symDim 16 = 136 ∧
    skewDim 16 = 120 ∧
    countFixedBlades 8 revFixed ≠ skewDim 16 ∧
    countFixedBlades 8 conjFixed ≠ skewDim 16 := by
  decide

end Mod8Periodicity

end Conjecture00000007628
