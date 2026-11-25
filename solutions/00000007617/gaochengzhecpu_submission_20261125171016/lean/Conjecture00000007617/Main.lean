/-
  Conjecture 00000007617 — Main Positive Theorems, Transverse Bilinear Rigidity,
  and Three Independent Refutations (R1, R2, R3)
  Core Lean 4.19.0 only (zero external dependencies).
-/

import Conjecture00000007617.PluckerMeet

namespace Conjecture00000007617
namespace Cl

/-! ### Part I: Positive Transverse Regime, Coordinate Helpers, and Rigidity -/

/-- Positive General-Dimension Transverse Basis-Blade Intersection Theorem:
    Whenever `I ∪ J = {0, ..., n-1}` (`coversAll I J = true`), `e_I ∨ e_J` is a
    pure sign `±1` times the intersection basis blade `e_{I ∩ J}` (nonzero over any `IDomain`). -/
theorem positive_transverse_basis_meet {R : Type} [IDomain R] {n : Nat} (I J : Fin n → Bool)
    (htrans : coversAll I J = true) :
    regressive n (basisBlade (R := R) n I) (basisBlade n J) =
      signCl n (meetSignExp I J) (basisBlade n (andMask I J)) ∧
    regressive n (basisBlade (R := R) n I) (basisBlade n J) ≠ zero n := by
  have h := regressive_basisBlade (R := R) I J
  rw [htrans] at h
  have h' : regressive n (basisBlade (R := R) n I) (basisBlade n J) =
      signCl n (meetSignExp I J) (basisBlade n (andMask I J)) := h
  refine ⟨h', ?_⟩
  rw [h']
  exact signCl_ne_zero (meetSignExp I J) (basisBlade_ne_zero (andMask I J))

section PositiveRegime
variable {R : Type} [CRing R]

/-- Positive Convention Sign-Correction Law across all dimensions `n` and grades `r + s ≥ n`. -/
theorem positive_convention_sign_corrections {n r s : Nat} {A B : Cl R n}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    (hA : HasGrade n r A) (hB : HasGrade n s B) :
    regressiveFwd n A B = signCl n ((r + s - n) * (n - (r + s - n))) (regressive n A B) ∧
    regressiveRev n A B = signCl n ((n - r) * (n - s)) (regressive n A B) :=
  ⟨regressiveFwd_eq_sign_regressive hr hs hrs hA hB,
   regressiveRev_eq_sign_regressive hr hs hA hB⟩

/-- Explicit 1-vector constructor `x0 e_0 + x1 e_1 + x2 e_2` in `Λ^1(R^3)`. -/
def vec3 (x0 x1 x2 : R) : Cl R 3 :=
  (((CRing.zero, x0), (x1, CRing.zero)), ((x2, CRing.zero), (CRing.zero, CRing.zero)))

/-- Explicit 2-vector constructor `b12 (e_1 ∧ e_2) + b20 (e_2 ∧ e_0) + b01 (e_0 ∧ e_1)` in `Λ^2(R^3)`. -/
def bivec3 (b12 b20 b01 : R) : Cl R 3 :=
  (((CRing.zero, CRing.zero), (CRing.zero, b01)),
   ((CRing.zero, CRing.neg b20), (b12, CRing.zero)))

def coord3_0 (v : Cl R 3) : R := v.1.1.2
def coord3_1 (v : Cl R 3) : R := v.1.2.1
def coord3_2 (v : Cl R 3) : R := v.2.1.1

def e3_0 : Cl R 3 := vec3 CRing.one CRing.zero CRing.zero
def e3_1 : Cl R 3 := vec3 CRing.zero CRing.one CRing.zero
def e3_2 : Cl R 3 := vec3 CRing.zero CRing.zero CRing.one

def E3_12 : Cl R 3 := bivec3 CRing.one CRing.zero CRing.zero
def E3_20 : Cl R 3 := bivec3 CRing.zero CRing.one CRing.zero
def E3_01 : Cl R 3 := bivec3 CRing.zero CRing.zero CRing.one
def E3_02 : Cl R 3 := bivec3 CRing.zero (CRing.neg CRing.one) CRing.zero

theorem vec3_hasGrade1 (x0 x1 x2 : R) : HasGrade 3 1 (vec3 x0 x1 x2) := by
  simp [HasGrade, vec3, zero]

theorem hasGrade1_eq_vec3 {v : Cl R 3} (hv : HasGrade 3 1 v) :
    v = vec3 (coord3_0 v) (coord3_1 v) (coord3_2 v) := by
  rcases v with ⟨⟨⟨c0, c1⟩, ⟨c2, c3⟩⟩, ⟨⟨c4, c5⟩, ⟨c6, c7⟩⟩⟩
  simp only [HasGrade, zero] at hv
  rcases hv with ⟨⟨⟨hc0, _⟩, ⟨_, hc3⟩⟩, ⟨⟨_, hc5⟩, hc67⟩⟩
  have hc6 : c6 = CRing.zero := congrArg Prod.fst hc67
  have hc7 : c7 = CRing.zero := congrArg Prod.snd hc67
  unfold vec3 coord3_0 coord3_1 coord3_2
  simp only [hc0, hc3, hc5, hc6, hc7]

theorem bivec3_hasGrade2 (b12 b20 b01 : R) : HasGrade 3 2 (bivec3 b12 b20 b01) := by
  simp [HasGrade, bivec3, zero]

theorem hasGrade2_eq_bivec3 {B : Cl R 3} (hB : HasGrade 3 2 B) :
    B = bivec3 B.2.2.1 (CRing.neg B.2.1.2) B.1.2.2 := by
  rcases B with ⟨⟨⟨c0, c1⟩, ⟨c2, c3⟩⟩, ⟨⟨c4, c5⟩, ⟨c6, c7⟩⟩⟩
  simp only [HasGrade, zero] at hB
  rcases hB with ⟨⟨⟨hc0, hc1⟩, ⟨hc2, _⟩⟩, ⟨⟨hc4, _⟩, ⟨_, hc7⟩⟩⟩
  unfold bivec3
  simp only [hc0, hc1, hc2, hc4, hc7, CRing.neg_neg]

theorem bivec3_decomp (b12 b20 b01 : R) :
    bivec3 b12 b20 b01 =
      add 3 (add 3 (smul 3 b12 E3_12) (smul 3 b20 E3_20)) (smul 3 b01 E3_01) := by
  simp [bivec3, E3_12, E3_20, E3_01, add, smul,
        CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.mul_neg, CRing.neg_zero]

/-- Exact component formula for `regressive 3` on arbitrary 2-vectors in `Λ^2(R^3)`. -/
theorem regressive3_bivec3 (a12 a20 a01 b12 b20 b01 : R) :
    regressive 3 (bivec3 a12 a20 a01) (bivec3 b12 b20 b01) =
      vec3 (CRing.sub (CRing.mul a20 b01) (CRing.mul a01 b20))
           (CRing.sub (CRing.mul a01 b12) (CRing.mul a12 b01))
           (CRing.sub (CRing.mul a12 b20) (CRing.mul a20 b12)) := by
  simp only [regressive, pStar, pStarInv, wedge, mul, zeroMetric, initMetric, lastMetric,
    bivec3, vec3, invol, add, neg, smul, CRing.sub,
    CRing.mul_zero, CRing.zero_mul, CRing.add_zero, CRing.zero_add,
    CRing.neg_zero, CRing.neg_neg, CRing.mul_neg, CRing.neg_mul]
  refine Prod.ext (Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ rfl)) (Prod.ext (Prod.ext ?_ rfl) rfl)
  · rw [CRing.add_comm]
  · change CRing.neg (CRing.add (CRing.mul a12 b01) (CRing.neg (CRing.mul a01 b12))) =
      CRing.add (CRing.mul a01 b12) (CRing.neg (CRing.mul a12 b01))
    rw [CRing.neg_add, CRing.neg_neg, CRing.add_comm]
  · rw [CRing.add_comm]

/-- Lagrange–Grassmann–Cayley Transverse Blade Identity in `R^3`:
    `(x ∧ e_0) ∨ (e_0 ∧ y) = [x ∧ e_0 ∧ y]_{ω_3} • e_0`. -/
theorem p2_lagrange_grassmann_meet (x0 x1 x2 y0 y1 y2 : R) :
    regressive 3 (wedge 3 (vec3 x0 x1 x2) e3_0) (wedge 3 e3_0 (vec3 y0 y1 y2)) =
      smul 3 (topCoeff 3 (wedge 3 (wedge 3 (vec3 x0 x1 x2) e3_0) (vec3 y0 y1 y2))) e3_0 := by
  have hA : wedge 3 (vec3 x0 x1 x2) e3_0 = bivec3 CRing.zero x2 (CRing.neg x1) := by
    simp [wedge, mul, zeroMetric, initMetric, lastMetric, vec3, e3_0, bivec3, invol, add, neg, smul,
      CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
      CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.neg_neg, CRing.mul_neg]
  have hB : wedge 3 e3_0 (vec3 y0 y1 y2) = bivec3 CRing.zero (CRing.neg y2) y1 := by
    simp [wedge, mul, zeroMetric, initMetric, lastMetric, vec3, e3_0, bivec3, invol, add, neg, smul,
      CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
      CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.neg_neg, CRing.mul_neg]
  have hdet : topCoeff 3 (wedge 3 (bivec3 CRing.zero x2 (CRing.neg x1)) (vec3 y0 y1 y2)) =
      CRing.sub (CRing.mul x2 y1) (CRing.mul x1 y2) := by
    simp only [topCoeff, wedge, mul, zeroMetric, initMetric, lastMetric, bivec3, vec3, invol, add, neg, smul,
      CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.add_zero, CRing.zero_add,
      CRing.neg_zero, CRing.neg_neg, CRing.neg_mul, CRing.mul_neg]
    rw [CRing.add_comm]
  rw [hA, hB, regressive3_bivec3, hdet]
  simp [vec3, e3_0, smul, CRing.sub,
    CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
    CRing.neg_zero, CRing.neg_mul_neg]

/-- Bilinearity predicate on `Cl R n × Cl R n → Cl R n`. -/
structure IsBilinear (n : Nat) (M : Cl R n → Cl R n → Cl R n) : Prop where
  add_left : ∀ x1 x2 y, M (add n x1 x2) y = add n (M x1 y) (M x2 y)
  add_right : ∀ x y1 y2, M x (add n y1 y2) = add n (M x y1) (M x y2)
  smul_left : ∀ r x y, M (smul n r x) y = smul n r (M x y)
  smul_right : ∀ r x y, M x (smul n r y) = smul n r (M x y)

theorem wedge3_vec3_bivec3_top (x0 x1 x2 b12 b20 b01 : R) :
    topCoeff 3 (wedge 3 (vec3 x0 x1 x2) (bivec3 b12 b20 b01)) =
      CRing.add (CRing.add (CRing.mul x0 b12) (CRing.mul x1 b20)) (CRing.mul x2 b01) := by
  simp only [topCoeff, wedge, mul, zeroMetric, initMetric, lastMetric, vec3, bivec3, invol, add, neg, smul,
    CRing.mul_zero, CRing.zero_mul, CRing.add_zero, CRing.zero_add,
    CRing.neg_zero, CRing.neg_neg, CRing.mul_neg]

private theorem in_plane_dot_eq_zero {v : Cl R 3} (hv : HasGrade 3 1 v)
    (b12 b20 b01 : R) (hw : wedge 3 v (bivec3 b12 b20 b01) = zero 3) :
    CRing.add (CRing.add (CRing.mul (coord3_0 v) b12) (CRing.mul (coord3_1 v) b20))
      (CRing.mul (coord3_2 v) b01) = CRing.zero := by
  have hv_eq := hasGrade1_eq_vec3 hv
  have ht : topCoeff 3 (wedge 3 v (bivec3 b12 b20 b01)) = CRing.zero := by
    rw [hw]; rfl
  rw [hv_eq, wedge3_vec3_bivec3_top] at ht
  exact ht

/-- Unimodular transversality condition on two 2-blades in `Λ^2(R^3)`:
    the three 2×2 Plücker dual minors generate the unit ideal in `R`. -/
def TransverseBivec3 (a12 a20 a01 b12 b20 b01 : R) : Prop :=
  let m0 := CRing.sub (CRing.mul a20 b01) (CRing.mul a01 b20)
  let m1 := CRing.sub (CRing.mul a01 b12) (CRing.mul a12 b01)
  let m2 := CRing.sub (CRing.mul a12 b20) (CRing.mul a20 b12)
  ∃ u0 u1 u2 : R,
    CRing.add (CRing.add (CRing.mul u0 m0) (CRing.mul u1 m1)) (CRing.mul u2 m2) = CRing.one

/-- **Rigidity Theorem for Transverse Bilinear Plücker Meet in `ℙ^2` (`Λ^2(R^3)`)**:
    Over EVERY commutative ring `R`, any `R`-bilinear map `M : Cl R 3 → Cl R 3 → Cl R 3`
    taking values in `Λ^1(R^3)` on 2-blades and mapping unimodularly transverse pairs
    into `U ∩ W` (`v ∧ A = 0 ∧ v ∧ B = 0`) equals `c • (A ∨ B)` on `Λ^2 × Λ^2` for the
    unique scalar `c = coord3_2 (M E3_12 E3_20)`. -/
theorem p2_transverse_bilinear_rigidity
    (M : Cl R 3 → Cl R 3 → Cl R 3)
    (hbil : IsBilinear 3 M)
    (hgrade : ∀ A B, HasGrade 3 2 A → HasGrade 3 2 B → HasGrade 3 1 (M A B))
    (htrans : ∀ a12 a20 a01 b12 b20 b01 : R,
      TransverseBivec3 a12 a20 a01 b12 b20 b01 →
      wedge 3 (M (bivec3 a12 a20 a01) (bivec3 b12 b20 b01)) (bivec3 a12 a20 a01) = zero 3 ∧
      wedge 3 (M (bivec3 a12 a20 a01) (bivec3 b12 b20 b01)) (bivec3 b12 b20 b01) = zero 3) :
    let c := coord3_2 (M E3_12 E3_20)
    (∀ A B, HasGrade 3 2 A → HasGrade 3 2 B →
      M A B = smul 3 c (regressive 3 A B)) ∧
    (∀ c' : R, (∀ A B, HasGrade 3 2 A → HasGrade 3 2 B →
      M A B = smul 3 c' (regressive 3 A B)) → c' = c) := by
  intro c
  have hpair_in : ∀ (a12 a20 a01 b12 b20 b01 : R),
      TransverseBivec3 a12 a20 a01 b12 b20 b01 →
      let v := M (bivec3 a12 a20 a01) (bivec3 b12 b20 b01)
      CRing.add (CRing.add (CRing.mul (coord3_0 v) a12) (CRing.mul (coord3_1 v) a20))
        (CRing.mul (coord3_2 v) a01) = CRing.zero ∧
      CRing.add (CRing.add (CRing.mul (coord3_0 v) b12) (CRing.mul (coord3_1 v) b20))
        (CRing.mul (coord3_2 v) b01) = CRing.zero := by
    intro a12 a20 a01 b12 b20 b01 hu
    have hw := htrans a12 a20 a01 b12 b20 b01 hu
    have hg := hgrade _ _ (bivec3_hasGrade2 a12 a20 a01) (bivec3_hasGrade2 b12 b20 b01)
    exact ⟨in_plane_dot_eq_zero hg a12 a20 a01 hw.1, in_plane_dot_eq_zero hg b12 b20 b01 hw.2⟩

  have ht_100_010 : TransverseBivec3 (R := R) CRing.one CRing.zero CRing.zero CRing.zero CRing.one CRing.zero :=
    ⟨CRing.zero, CRing.zero, CRing.one, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
  have ht_010_100 : TransverseBivec3 (R := R) CRing.zero CRing.one CRing.zero CRing.one CRing.zero CRing.zero :=
    ⟨CRing.zero, CRing.zero, CRing.neg CRing.one, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
            CRing.neg_zero, CRing.neg_mul_neg]⟩
  have ht_010_001 : TransverseBivec3 (R := R) CRing.zero CRing.one CRing.zero CRing.zero CRing.zero CRing.one :=
    ⟨CRing.one, CRing.zero, CRing.zero, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
  have ht_001_010 : TransverseBivec3 (R := R) CRing.zero CRing.zero CRing.one CRing.zero CRing.one CRing.zero :=
    ⟨CRing.neg CRing.one, CRing.zero, CRing.zero, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
            CRing.neg_zero, CRing.neg_mul_neg]⟩
  have ht_001_100 : TransverseBivec3 (R := R) CRing.zero CRing.zero CRing.one CRing.one CRing.zero CRing.zero :=
    ⟨CRing.zero, CRing.one, CRing.zero, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
  have ht_100_001 : TransverseBivec3 (R := R) CRing.one CRing.zero CRing.zero CRing.zero CRing.zero CRing.one :=
    ⟨CRing.zero, CRing.neg CRing.one, CRing.zero, by
      simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
            CRing.neg_zero, CRing.neg_mul_neg]⟩

  let c21 := coord3_2 (M E3_20 E3_12)
  let c23 := coord3_0 (M E3_20 E3_01)
  let c32 := coord3_0 (M E3_01 E3_20)
  let c31 := coord3_1 (M E3_01 E3_12)
  let c13 := coord3_1 (M E3_12 E3_01)

  have he12 : bivec3 (R := R) CRing.one CRing.zero CRing.zero = E3_12 := rfl
  have he20 : bivec3 (R := R) CRing.zero CRing.one CRing.zero = E3_20 := rfl
  have he01 : bivec3 (R := R) CRing.zero CRing.zero CRing.one = E3_01 := rfl

  have hp12 : M E3_12 E3_20 = vec3 CRing.zero CRing.zero c := by
    have h := hpair_in _ _ _ _ _ _ ht_100_010
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_12 E3_20 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_12 E3_20 = vec3 (coord3_0 (M E3_12 E3_20)) (coord3_1 (M E3_12 E3_20)) c at hg
    change coord3_0 (M E3_12 E3_20) = CRing.zero ∧ coord3_1 (M E3_12 E3_20) = CRing.zero at h
    rw [hg, h.1, h.2]
  have hp21 : M E3_20 E3_12 = vec3 CRing.zero CRing.zero c21 := by
    have h := hpair_in _ _ _ _ _ _ ht_010_100
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_20 E3_12 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_20 E3_12 = vec3 (coord3_0 (M E3_20 E3_12)) (coord3_1 (M E3_20 E3_12)) c21 at hg
    change coord3_1 (M E3_20 E3_12) = CRing.zero ∧ coord3_0 (M E3_20 E3_12) = CRing.zero at h
    rw [hg, h.2, h.1]
  have hp23 : M E3_20 E3_01 = vec3 c23 CRing.zero CRing.zero := by
    have h := hpair_in _ _ _ _ _ _ ht_010_001
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_20 E3_01 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_20 E3_01 = vec3 c23 (coord3_1 (M E3_20 E3_01)) (coord3_2 (M E3_20 E3_01)) at hg
    change coord3_1 (M E3_20 E3_01) = CRing.zero ∧ coord3_2 (M E3_20 E3_01) = CRing.zero at h
    rw [hg, h.1, h.2]
  have hp32 : M E3_01 E3_20 = vec3 c32 CRing.zero CRing.zero := by
    have h := hpair_in _ _ _ _ _ _ ht_001_010
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_01 E3_20 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_01 E3_20 = vec3 c32 (coord3_1 (M E3_01 E3_20)) (coord3_2 (M E3_01 E3_20)) at hg
    change coord3_2 (M E3_01 E3_20) = CRing.zero ∧ coord3_1 (M E3_01 E3_20) = CRing.zero at h
    rw [hg, h.2, h.1]
  have hp31 : M E3_01 E3_12 = vec3 CRing.zero c31 CRing.zero := by
    have h := hpair_in _ _ _ _ _ _ ht_001_100
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_01 E3_12 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_01 E3_12 = vec3 (coord3_0 (M E3_01 E3_12)) c31 (coord3_2 (M E3_01 E3_12)) at hg
    change coord3_2 (M E3_01 E3_12) = CRing.zero ∧ coord3_0 (M E3_01 E3_12) = CRing.zero at h
    rw [hg, h.2, h.1]
  have hp13 : M E3_12 E3_01 = vec3 CRing.zero c13 CRing.zero := by
    have h := hpair_in _ _ _ _ _ _ ht_100_001
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    have hg := hasGrade1_eq_vec3 (hgrade E3_12 E3_01 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    change M E3_12 E3_01 = vec3 (coord3_0 (M E3_12 E3_01)) c13 (coord3_2 (M E3_12 E3_01)) at hg
    change coord3_0 (M E3_12 E3_01) = CRing.zero ∧ coord3_2 (M E3_12 E3_01) = CRing.zero at h
    rw [hg, h.1, h.2]

  have hb_110 : bivec3 (R := R) CRing.one CRing.one CRing.zero = add 3 E3_12 E3_20 := by
    simp [bivec3, E3_12, E3_20, add, CRing.add_zero, CRing.zero_add, CRing.neg_zero]
  have hb_101 : bivec3 (R := R) CRing.one CRing.zero CRing.one = add 3 E3_12 E3_01 := by
    simp [bivec3, E3_12, E3_01, add, CRing.add_zero, CRing.zero_add, CRing.neg_zero]
  have hb_011 : bivec3 (R := R) CRing.zero CRing.one CRing.one = add 3 E3_20 E3_01 := by
    simp [bivec3, E3_20, E3_01, add, CRing.add_zero, CRing.zero_add, CRing.neg_zero]

  have hcoord_add : ∀ u v : Cl R 3,
      coord3_0 (add 3 u v) = CRing.add (coord3_0 u) (coord3_0 v) ∧
      coord3_1 (add 3 u v) = CRing.add (coord3_1 u) (coord3_1 v) ∧
      coord3_2 (add 3 u v) = CRing.add (coord3_2 u) (coord3_2 v) :=
    fun _ _ => ⟨rfl, rfl, rfl⟩

  -- Diagonal entries vanish:
  have hp11 : M E3_12 E3_12 = zero 3 := by
    have hA := hpair_in CRing.one CRing.one CRing.zero CRing.one CRing.zero CRing.zero
      ⟨CRing.zero, CRing.zero, CRing.neg CRing.one, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
              CRing.neg_zero, CRing.neg_mul_neg]⟩
    have hB := hpair_in CRing.one CRing.zero CRing.one CRing.one CRing.zero CRing.zero
      ⟨CRing.zero, CRing.one, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
    dsimp only at hA hB
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at hA hB
    rw [hb_110, he12, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.1, hp21] at hA
    rw [hb_101, he12, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.2, hp31] at hB
    change CRing.add (CRing.add (coord3_0 (M E3_12 E3_12)) CRing.zero)
        (CRing.add (coord3_1 (M E3_12 E3_12)) CRing.zero) = CRing.zero ∧
      CRing.add (coord3_0 (M E3_12 E3_12)) CRing.zero = CRing.zero at hA
    change CRing.add (CRing.add (coord3_0 (M E3_12 E3_12)) CRing.zero)
        (CRing.add (coord3_2 (M E3_12 E3_12)) CRing.zero) = CRing.zero ∧ _ at hB
    simp only [CRing.add_zero] at hA hB
    have h0 : coord3_0 (M E3_12 E3_12) = CRing.zero := hA.2
    have h1 : coord3_1 (M E3_12 E3_12) = CRing.zero := by
      have ha1 := hA.1; rw [h0, CRing.zero_add] at ha1; exact ha1
    have h2 : coord3_2 (M E3_12 E3_12) = CRing.zero := by
      have hb1 := hB.1; rw [h0, CRing.zero_add] at hb1; exact hb1
    have hg := hasGrade1_eq_vec3 (hgrade E3_12 E3_12 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    rw [hg, h0, h1, h2]; rfl

  have hp22 : M E3_20 E3_20 = zero 3 := by
    have hA := hpair_in CRing.one CRing.one CRing.zero CRing.zero CRing.one CRing.zero
      ⟨CRing.zero, CRing.zero, CRing.one, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
    have hB := hpair_in CRing.zero CRing.one CRing.one CRing.zero CRing.one CRing.zero
      ⟨CRing.neg CRing.one, CRing.zero, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
              CRing.neg_zero, CRing.neg_mul_neg]⟩
    dsimp only at hA hB
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at hA hB
    rw [hb_110, he20, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.1, hp12] at hA
    rw [hb_011, he20, hbil.add_left, (hcoord_add _ _).2.1, (hcoord_add _ _).2.2, hp32] at hB
    change CRing.add (CRing.add CRing.zero (coord3_0 (M E3_20 E3_20)))
        (CRing.add CRing.zero (coord3_1 (M E3_20 E3_20))) = CRing.zero ∧
      CRing.add CRing.zero (coord3_1 (M E3_20 E3_20)) = CRing.zero at hA
    change CRing.add (CRing.add (coord3_1 (M E3_20 E3_20)) CRing.zero)
        (CRing.add (coord3_2 (M E3_20 E3_20)) CRing.zero) = CRing.zero ∧ _ at hB
    simp only [CRing.zero_add, CRing.add_zero] at hA hB
    have h1 : coord3_1 (M E3_20 E3_20) = CRing.zero := hA.2
    have h0 : coord3_0 (M E3_20 E3_20) = CRing.zero := by
      have ha1 := hA.1; rw [h1, CRing.add_zero] at ha1; exact ha1
    have h2 : coord3_2 (M E3_20 E3_20) = CRing.zero := by
      have hb1 := hB.1; rw [h1, CRing.zero_add] at hb1; exact hb1
    have hg := hasGrade1_eq_vec3 (hgrade E3_20 E3_20 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    rw [hg, h0, h1, h2]; rfl

  have hp33 : M E3_01 E3_01 = zero 3 := by
    have hA := hpair_in CRing.one CRing.zero CRing.one CRing.zero CRing.zero CRing.one
      ⟨CRing.zero, CRing.neg CRing.one, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
              CRing.neg_zero, CRing.neg_mul_neg]⟩
    have hB := hpair_in CRing.zero CRing.one CRing.one CRing.zero CRing.zero CRing.one
      ⟨CRing.one, CRing.zero, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩
    dsimp only at hA hB
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at hA hB
    rw [hb_101, he01, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.2, hp13] at hA
    rw [hb_011, he01, hbil.add_left, (hcoord_add _ _).2.1, (hcoord_add _ _).2.2, hp23] at hB
    change CRing.add (CRing.add CRing.zero (coord3_0 (M E3_01 E3_01)))
        (CRing.add CRing.zero (coord3_2 (M E3_01 E3_01))) = CRing.zero ∧
      CRing.add CRing.zero (coord3_2 (M E3_01 E3_01)) = CRing.zero at hA
    change CRing.add (CRing.add CRing.zero (coord3_1 (M E3_01 E3_01)))
        (CRing.add CRing.zero (coord3_2 (M E3_01 E3_01))) = CRing.zero ∧ _ at hB
    simp only [CRing.zero_add] at hA hB
    have h2 : coord3_2 (M E3_01 E3_01) = CRing.zero := hA.2
    have h0 : coord3_0 (M E3_01 E3_01) = CRing.zero := by
      have ha1 := hA.1; rw [h2, CRing.add_zero] at ha1; exact ha1
    have h1 : coord3_1 (M E3_01 E3_01) = CRing.zero := by
      have hb1 := hB.1; rw [h2, CRing.add_zero] at hb1; exact hb1
    have hg := hasGrade1_eq_vec3 (hgrade E3_01 E3_01 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _))
    rw [hg, h0, h1, h2]; rfl

  -- 5 sheared unimodular pairs pin down all 6 off-diagonal scalars in terms of `c`:
  have hrel_c32 : c32 = CRing.neg c := by
    have h := (hpair_in CRing.one CRing.zero CRing.one CRing.zero CRing.one CRing.zero
      ⟨CRing.zero, CRing.zero, CRing.one, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩).1
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    rw [hb_101, he20, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.2, hp12, hp32] at h
    change CRing.add (CRing.add CRing.zero c32) (CRing.add c CRing.zero) = CRing.zero at h
    rw [CRing.zero_add, CRing.add_zero, CRing.add_comm] at h
    exact Eq.symm (CRing.neg_eq_of_add_eq_zero h)

  have hrel_c13_c : c13 = CRing.neg c := by
    have h := (hpair_in CRing.one CRing.one CRing.zero CRing.zero CRing.one CRing.one
      ⟨CRing.one, CRing.zero, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩).2
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    rw [hb_110, hb_011, hbil.add_left, hbil.add_right, hbil.add_right, hp22, zero_add,
        (hcoord_add _ _).2.1, (hcoord_add _ _).2.1, (hcoord_add _ _).2.2, (hcoord_add _ _).2.2,
        hp12, hp13, hp23] at h
    change CRing.add (CRing.add (CRing.add CRing.zero c13) CRing.zero)
      (CRing.add (CRing.add c CRing.zero) CRing.zero) = CRing.zero at h
    rw [CRing.zero_add, CRing.add_zero, CRing.add_zero, CRing.add_zero, CRing.add_comm] at h
    exact Eq.symm (CRing.neg_eq_of_add_eq_zero h)

  have hrel_c23 : c23 = c := by
    have h := (hpair_in CRing.one CRing.one CRing.zero CRing.zero CRing.zero CRing.one
      ⟨CRing.one, CRing.zero, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩).1
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    rw [hb_110, he01, hbil.add_left, (hcoord_add _ _).1, (hcoord_add _ _).2.1, hp13, hp23] at h
    change CRing.add (CRing.add CRing.zero c23) (CRing.add c13 CRing.zero) = CRing.zero at h
    rw [CRing.zero_add, CRing.add_zero, hrel_c13_c, CRing.add_comm] at h
    have hn := CRing.neg_eq_of_add_eq_zero h
    rw [CRing.neg_neg] at hn
    exact Eq.symm hn

  have hrel_c21 : c21 = CRing.neg c := by
    have h := (hpair_in CRing.zero CRing.one CRing.zero CRing.one CRing.zero CRing.one
      ⟨CRing.one, CRing.zero, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩).2
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    rw [he20, hb_101, hbil.add_right, (hcoord_add _ _).1, (hcoord_add _ _).2.2, hp21, hp23] at h
    change CRing.add (CRing.add CRing.zero c23) (CRing.add c21 CRing.zero) = CRing.zero at h
    rw [CRing.zero_add, CRing.add_zero, hrel_c23] at h
    exact Eq.symm (CRing.neg_eq_of_add_eq_zero h)

  have hrel_c31 : c31 = c := by
    have h := (hpair_in CRing.zero CRing.one CRing.one CRing.one CRing.zero CRing.zero
      ⟨CRing.zero, CRing.one, CRing.zero, by
        simp [CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add, CRing.neg_zero]⟩).1
    simp only [CRing.mul_one, CRing.mul_zero, CRing.add_zero, CRing.zero_add] at h
    rw [hb_011, he12, hbil.add_left, (hcoord_add _ _).2.1, (hcoord_add _ _).2.2, hp21, hp31] at h
    change CRing.add (CRing.add CRing.zero c31) (CRing.add c21 CRing.zero) = CRing.zero at h
    rw [CRing.zero_add, CRing.add_zero, hrel_c21, CRing.add_comm] at h
    have hn := CRing.neg_eq_of_add_eq_zero h
    rw [CRing.neg_neg] at hn
    exact Eq.symm hn

  rw [hrel_c21] at hp21
  rw [hrel_c23] at hp23
  rw [hrel_c32] at hp32
  rw [hrel_c31] at hp31
  rw [hrel_c13_c] at hp13

  -- Check basis agreement `M E_i E_j = smul 3 c (regressive 3 E_i E_j)` on all 9 pairs:
  have hb_eq : ∀ (E_A E_B : Cl R 3),
      (E_A = E3_12 ∨ E_A = E3_20 ∨ E_A = E3_01) →
      (E_B = E3_12 ∨ E_B = E3_20 ∨ E_B = E3_01) →
      M E_A E_B = smul 3 c (regressive 3 E_A E_B) := by
    intro EA EB hEA hEB
    rcases hEA with rfl | rfl | rfl <;> rcases hEB with rfl | rfl | rfl
    · rw [hp11]; unfold E3_12; rw [regressive3_bivec3]
      simp [vec3, zero, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_right_neg]
    · rw [hp12]; unfold E3_12 E3_20; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.neg_zero]
    · rw [hp13]; unfold E3_12 E3_01; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.mul_neg]
    · rw [hp21]; unfold E3_20 E3_12; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.mul_neg]
    · rw [hp22]; unfold E3_20; rw [regressive3_bivec3]
      simp [vec3, zero, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_right_neg]
    · rw [hp23]; unfold E3_20 E3_01; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.neg_zero]
    · rw [hp31]; unfold E3_01 E3_12; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.neg_zero]
    · rw [hp32]; unfold E3_01 E3_20; rw [regressive3_bivec3]
      simp [vec3, smul, CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.mul_neg]
    · rw [hp33]; unfold E3_01; rw [regressive3_bivec3]
      simp [vec3, zero, smul, CRing.sub, CRing.mul_zero, CRing.mul_one, CRing.add_right_neg]

  have hlin_right : ∀ (EA : Cl R 3) (b12 b20 b01 : R),
      (EA = E3_12 ∨ EA = E3_20 ∨ EA = E3_01) →
      M EA (bivec3 b12 b20 b01) = smul 3 c (regressive 3 EA (bivec3 b12 b20 b01)) := by
    intro EA b12 b20 b01 hEA
    rw [bivec3_decomp, hbil.add_right, hbil.add_right,
        hbil.smul_right, hbil.smul_right, hbil.smul_right,
        hb_eq EA E3_12 hEA (Or.inl rfl),
        hb_eq EA E3_20 hEA (Or.inr (Or.inl rfl)),
        hb_eq EA E3_01 hEA (Or.inr (Or.inr rfl)),
        regressive_add_right, regressive_add_right,
        regressive_smul_right, regressive_smul_right, regressive_smul_right,
        smul_add, smul_add,
        smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul,
        CRing.mul_comm b12 c, CRing.mul_comm b20 c, CRing.mul_comm b01 c]

  refine ⟨?_, ?_⟩
  · intro A B hA hB
    rw [hasGrade2_eq_bivec3 hA, hasGrade2_eq_bivec3 hB]
    let a12 := A.2.2.1
    let a20 := CRing.neg A.2.1.2
    let a01 := A.1.2.2
    let b12 := B.2.2.1
    let b20 := CRing.neg B.2.1.2
    let b01 := B.1.2.2
    rw [bivec3_decomp a12 a20 a01, hbil.add_left, hbil.add_left,
        hbil.smul_left, hbil.smul_left, hbil.smul_left,
        hlin_right E3_12 b12 b20 b01 (Or.inl rfl),
        hlin_right E3_20 b12 b20 b01 (Or.inr (Or.inl rfl)),
        hlin_right E3_01 b12 b20 b01 (Or.inr (Or.inr rfl)),
        regressive_add_left, regressive_add_left,
        regressive_smul_left, regressive_smul_left, regressive_smul_left,
        smul_add, smul_add,
        smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul,
        CRing.mul_comm a12 c, CRing.mul_comm a20 c, CRing.mul_comm a01 c]
  · intro c' hc'
    have hev := hc' E3_12 E3_20 (bivec3_hasGrade2 _ _ _) (bivec3_hasGrade2 _ _ _)
    have hc_def : coord3_2 (M E3_12 E3_20) = c := rfl
    rw [hev] at hc_def
    unfold E3_12 E3_20 at hc_def
    rw [regressive3_bivec3] at hc_def
    simp only [vec3, smul, coord3_2, CRing.sub,
      CRing.mul_one, CRing.mul_zero, CRing.neg_zero, CRing.add_zero] at hc_def
    exact hc_def

end PositiveRegime

/-! ### Part II: Refutation R1 — Scalar Non-Uniqueness & Non-Unit Sine/Determinant Factor -/

/-- **Refutation R1a (Bracket-Scaling Non-Uniqueness Beyond `±1`):**
    Over `ℤ`, `M_k := regressiveScaled 3 k` for `k = 2` is a bilinear transverse intersection
    operator mapping every pair of 2-blades `(A, B)` into `U ∩ W` (`v ∧ A = 0 ∧ v ∧ B = 0`)
    and nonzero on transverse coordinate blades, yet `M_2 ≠ +regressive 3` and `M_2 ≠ -regressive 3`. -/
theorem r1_bracket_scaling_nonunique :
    let M2 := regressiveScaled (R := Int) 3 (2 : Int)
    IsBilinear 3 M2 ∧
    (∀ a12 a20 a01 b12 b20 b01 : Int,
      wedge 3 (M2 (bivec3 a12 a20 a01) (bivec3 b12 b20 b01)) (bivec3 a12 a20 a01) = zero 3 ∧
      wedge 3 (M2 (bivec3 a12 a20 a01) (bivec3 b12 b20 b01)) (bivec3 b12 b20 b01) = zero 3) ∧
    M2 (E3_12 (R := Int)) (E3_20 (R := Int)) ≠ zero 3 ∧
    M2 (E3_12 (R := Int)) (E3_20 (R := Int)) ≠ regressive 3 (E3_12 (R := Int)) (E3_20 (R := Int)) ∧
    M2 (E3_12 (R := Int)) (E3_20 (R := Int)) ≠ neg 3 (regressive 3 (E3_12 (R := Int)) (E3_20 (R := Int))) := by
  intro M2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x1 x2 y; unfold M2 regressiveScaled; rw [regressive_add_left, smul_add]
    · intro x y1 y2; unfold M2 regressiveScaled; rw [regressive_add_right, smul_add]
    · intro r x y; unfold M2 regressiveScaled
      rw [regressive_smul_left, smul_smul, smul_smul, CRing.mul_comm (2 : Int) r]
    · intro r x y; unfold M2 regressiveScaled
      rw [regressive_smul_right, smul_smul, smul_smul, CRing.mul_comm (2 : Int) r]
  · intro a12 a20 a01 b12 b20 b01
    unfold M2 regressiveScaled
    rw [regressive3_bivec3]
    have hsmul_v : ∀ x0 x1 x2 : Int,
        smul 3 (2 : Int) (vec3 x0 x1 x2) = vec3 (2 * x0) (2 * x1) (2 * x2) :=
      fun _ _ _ => rfl
    rw [hsmul_v]
    have hvan : ∀ x0 x1 x2 c1 c2 c3 : Int,
        wedge 3 (vec3 x0 x1 x2) (bivec3 c1 c2 c3) =
        ((((0 : Int), 0), (0, 0)), (((0, 0), (0, x0 * c1 + x1 * c2 + x2 * c3)))) := by
      intro x0 x1 x2 c1 c2 c3
      simp only [wedge, mul, zeroMetric, initMetric, lastMetric, vec3, bivec3, invol, add, neg, smul,
        CRing.mul_zero, CRing.zero_mul, CRing.add_zero, CRing.zero_add,
        CRing.neg_zero, CRing.neg_neg, CRing.mul_neg]
      rfl
    have hdetA : 2 * (a20 * b01 + -(a01 * b20)) * a12 +
        2 * (a01 * b12 + -(a12 * b01)) * a20 +
        2 * (a12 * b20 + -(a20 * b12)) * a01 = 0 := by
      rw [Int.mul_assoc 2, Int.mul_assoc 2, Int.mul_assoc 2, ← Int.mul_add, ← Int.mul_add, Int.add_assoc]
      have hd : (a20 * b01 + -(a01 * b20)) * a12 +
          ((a01 * b12 + -(a12 * b01)) * a20 + (a12 * b20 + -(a20 * b12)) * a01) = 0 := by
        simp only [Int.add_mul, Int.neg_mul]
        have p1 : a20 * b01 * a12 = a12 * b01 * a20 := by
          rw [Int.mul_comm a20 b01, Int.mul_comm (b01 * a20) a12, ← Int.mul_assoc]
        have p2 : a01 * b20 * a12 = a12 * b20 * a01 := by
          rw [Int.mul_comm a01 b20, Int.mul_comm (b20 * a01) a12, ← Int.mul_assoc]
        have p3 : a01 * b12 * a20 = a20 * b12 * a01 := by
          rw [Int.mul_comm a01 b12, Int.mul_comm (b12 * a01) a20, ← Int.mul_assoc]
        rw [p1, p2, p3]
        omega
      rw [hd]; rfl
    have hdetB : 2 * (a20 * b01 + -(a01 * b20)) * b12 +
        2 * (a01 * b12 + -(a12 * b01)) * b20 +
        2 * (a12 * b20 + -(a20 * b12)) * b01 = 0 := by
      rw [Int.mul_assoc 2, Int.mul_assoc 2, Int.mul_assoc 2, ← Int.mul_add, ← Int.mul_add, Int.add_assoc]
      have hd : (a20 * b01 + -(a01 * b20)) * b12 +
          ((a01 * b12 + -(a12 * b01)) * b20 + (a12 * b20 + -(a20 * b12)) * b01) = 0 := by
        simp only [Int.add_mul, Int.neg_mul]
        have q1 : a20 * b01 * b12 = a20 * b12 * b01 := by
          rw [Int.mul_assoc a20, Int.mul_comm b01 b12, ← Int.mul_assoc]
        have q2 : a01 * b20 * b12 = a01 * b12 * b20 := by
          rw [Int.mul_assoc a01, Int.mul_comm b20 b12, ← Int.mul_assoc]
        have q3 : a12 * b01 * b20 = a12 * b20 * b01 := by
          rw [Int.mul_assoc a12, Int.mul_comm b01 b20, ← Int.mul_assoc]
        rw [q1, q2, q3]
        omega
      rw [hd]; rfl
    constructor
    · rw [hvan _ _ _ a12 a20 a01]
      change ((((0 : Int), 0), (0, 0)), (((0, 0), (0,
        2 * (a20 * b01 + -(a01 * b20)) * a12 +
        2 * (a01 * b12 + -(a12 * b01)) * a20 +
        2 * (a12 * b20 + -(a20 * b12)) * a01)))) = zero 3
      rw [hdetA]; rfl
    · rw [hvan _ _ _ b12 b20 b01]
      change ((((0 : Int), 0), (0, 0)), (((0, 0), (0,
        2 * (a20 * b01 + -(a01 * b20)) * b12 +
        2 * (a01 * b12 + -(a12 * b01)) * b20 +
        2 * (a12 * b20 + -(a20 * b12)) * b01)))) = zero 3
      rw [hdetB]; rfl
  · intro hz
    have hc : coord3_2 (M2 (E3_12 (R := Int)) (E3_20 (R := Int))) = coord3_2 (zero 3) :=
      congrArg coord3_2 hz
    revert hc; decide
  · intro heq
    have hc : coord3_2 (M2 (E3_12 (R := Int)) (E3_20 (R := Int))) =
        coord3_2 (regressive 3 (E3_12 (R := Int)) (E3_20 (R := Int))) :=
      congrArg coord3_2 heq
    revert hc; decide
  · intro hneg
    have hc : coord3_2 (M2 (E3_12 (R := Int)) (E3_20 (R := Int))) =
        coord3_2 (neg 3 (regressive 3 (E3_12 (R := Int)) (E3_20 (R := Int)))) :=
      congrArg coord3_2 hneg
    revert hc; decide

/-- Rational 3-4-5 unit-blade definitions in `Λ^2(ℚ^3)`. -/
def q3_5 : QRat := QRat.mk 3 5 (by decide)
def q4_5 : QRat := QRat.mk 4 5 (by decide)
def q8_5 : QRat := QRat.mk 8 5 (by decide)
def q16_25 : QRat := QRat.mk 16 25 (by decide)

/-- **Refutation R1b (Unit-Normalized Rational Plücker Blades Have Non-Sign Meet Factor `4/5`):**
    Over `ℚ` (`QRat`), the two transverse unit-norm Plücker 2-blades
      `A = e_0 ∧ e_1` (`⟨A, A⟩ = 1`) and `B = (3/5)(e_0 ∧ e_1) + (4/5)(e_0 ∧ e_2)` (`⟨B, B⟩ = 1`)
    have meet `A ∨ B = (4/5) e_0` with squared norm `16/25 ≠ 1`, which differs from both
    unit Plücker 1-blades `± e_0` of `U ∩ W = span{e_0}` by `4/5 ∉ {+1, -1}`! -/
theorem r1_unit_plucker_blades_non_sign_factor :
    let A : Cl QRat 3 := E3_01
    let B : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) q3_5
    inner (euclidMetric 3) A A = QRat.one ∧
    inner (euclidMetric 3) B B = QRat.one ∧
    regressive 3 A B = smul 3 q4_5 e3_0 ∧
    inner (euclidMetric 3) (regressive 3 A B) (regressive 3 A B) = q16_25 ∧
    inner (euclidMetric 3) (regressive 3 A B) (regressive 3 A B) ≠ QRat.one ∧
    regressive 3 A B ≠ e3_0 ∧
    regressive 3 A B ≠ neg 3 e3_0 := by
  intro A B
  have hmeet : regressive 3 A B = smul 3 q4_5 e3_0 := by
    unfold A B E3_01
    rw [regressive3_bivec3]
    have hz : QRat.zero = (CRing.zero : QRat) := rfl
    rw [hz]
    simp [vec3, e3_0, smul, CRing.sub,
      CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
      CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.neg_neg]
  refine ⟨?_, ?_, hmeet, ?_, ?_, ?_, ?_⟩
  · apply Quot.sound; unfold RawRat.Rel; decide
  · apply Quot.sound; unfold RawRat.Rel; decide
  · rw [hmeet]; apply Quot.sound; unfold RawRat.Rel; decide
  · rw [hmeet]
    apply QRat.ne_of_eqFracBool_diff 1 1
    decide
  · intro heq
    rw [hmeet] at heq
    have hc : coord3_0 (smul 3 q4_5 (e3_0 (R := QRat))) = coord3_0 (e3_0 (R := QRat)) :=
      congrArg coord3_0 heq
    exact QRat.ne_of_eqFracBool_diff 1 1 (by decide) hc
  · intro hneg
    rw [hmeet] at hneg
    have hc : coord3_0 (smul 3 q4_5 (e3_0 (R := QRat))) = coord3_0 (neg 3 (e3_0 (R := QRat))) :=
      congrArg coord3_0 hneg
    exact QRat.ne_of_eqFracBool_diff (-1) 1 (by decide) hc

/-- **Refutation R1c (Universal Bilinear Unit-Norm Impossibility Theorem over `ℚ`):**
    NO `ℚ`-bilinear map `M : Cl QRat 3 → Cl QRat 3 → Cl QRat 3` can map all transverse
    pairs of unit-norm Plücker 2-blades `(A, B)` into unit-norm Plücker 1-blades `± e_0`
    of their intersection `span{e_0}` (`5(±1 ± 1) ≠ ±8`). -/
theorem r1_no_unit_preserving_bilinear_meet :
    ¬ ∃ M : Cl QRat 3 → Cl QRat 3 → Cl QRat 3,
      IsBilinear 3 M ∧
      let A : Cl QRat 3 := E3_01
      let B1 : Cl QRat 3 := E3_02
      let B2 : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) q3_5
      let B3 : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) (CRing.neg q3_5)
      (M A B1 = e3_0 ∨ M A B1 = neg 3 e3_0) ∧
      (M A B2 = e3_0 ∨ M A B2 = neg 3 e3_0) ∧
      (M A B3 = e3_0 ∨ M A B3 = neg 3 e3_0) := by
  rintro ⟨M, hbil, h1, h2, h3⟩
  let A : Cl QRat 3 := E3_01
  let B1 : Cl QRat 3 := E3_02
  let B2 : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) q3_5
  let B3 : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) (CRing.neg q3_5)
  have hlin : add 3 B2 B3 = smul 3 q8_5 B1 := by
    have hz : QRat.zero = (CRing.zero : QRat) := rfl
    unfold B1 B2 B3 E3_02 bivec3
    rw [hz]
    simp only [add, smul, CRing.mul_zero, CRing.add_zero]
    refine Prod.ext (Prod.ext rfl (Prod.ext rfl ?_)) (Prod.ext (Prod.ext rfl ?_) rfl)
    · apply Quot.sound; unfold RawRat.Rel; decide
    · apply Quot.sound; unfold RawRat.Rel; decide
  have hm : add 3 (M A B2) (M A B3) = smul 3 q8_5 (M A B1) := by
    rw [← hbil.add_right, hlin, hbil.smul_right]
  have hc : CRing.add (coord3_0 (M A B2)) (coord3_0 (M A B3)) =
      CRing.mul q8_5 (coord3_0 (M A B1)) :=
    congrArg coord3_0 hm
  rcases h1 with h1p | h1n <;> rcases h2 with h2p | h2n <;> rcases h3 with h3p | h3n
  · rw [h1p, h2p, h3p] at hc
    exact QRat.ne_of_eqFracBool_diff 2 1 (by decide) hc
  · rw [h1p, h2p, h3n] at hc
    exact QRat.ne_of_eqFracBool_diff 0 1 (by decide) hc
  · rw [h1p, h2n, h3p] at hc
    exact QRat.ne_of_eqFracBool_diff 0 1 (by decide) hc
  · rw [h1p, h2n, h3n] at hc
    exact QRat.ne_of_eqFracBool_diff (-2) 1 (by decide) hc
  · rw [h1n, h2p, h3p] at hc
    exact QRat.ne_of_eqFracBool_diff 2 1 (by decide) hc
  · rw [h1n, h2p, h3n] at hc
    exact QRat.ne_of_eqFracBool_diff 0 1 (by decide) hc
  · rw [h1n, h2n, h3p] at hc
    exact QRat.ne_of_eqFracBool_diff 0 1 (by decide) hc
  · rw [h1n, h2n, h3n] at hc
    exact QRat.ne_of_eqFracBool_diff (-2) 1 (by decide) hc

/-! ### Part III: Refutation R2 — Identical Vanishing on Non-Transverse Intersections
    and Polynomial / Incident-Only Impossibility -/

/-- **Refutation R2a (General Non-Transverse Basis-Blade Vanishing):**
    In every dimension `n`, whenever `coversAll I J = false` (`U_I + U_J ⊊ R^n`),
    `e_I ∨ e_J = 0` identically. -/
theorem r2_nontransverse_basis_vanish {R : Type} [CRing R] {n : Nat}
    (I J : Fin n → Bool) (hnt : coversAll I J = false) :
    regressive n (basisBlade (R := R) n I) (basisBlade n J) = zero n := by
  have h := regressive_basisBlade (R := R) I J
  rw [hnt] at h
  exact h

/-- **Refutation R2b (Coinciding Lines in `ℙ^2`, `n = 3`):**
    For `U = W = span{e_0, e_1}` (`A = e_0 ∧ e_1 ≠ 0`), `U ∩ W = U ≠ {0}`, yet
    `A ∨ A = 0` (`A ∨_fwd A = 0`, `A ∨_rev A = 0`), and no scalar `c` recovers `A`. -/
theorem r2_coinciding_lines_p2_vanish {R : Type} [IDomain R] :
    let A : Cl R 3 := E3_01
    A ≠ zero 3 ∧
    regressive 3 A A = zero 3 ∧
    regressiveFwd 3 A A = zero 3 ∧
    regressiveRev 3 A A = zero 3 ∧
    (∀ c : R, smul 3 c (regressive 3 A A) ≠ A) := by
  intro A
  have hA_ne : A ≠ zero 3 := by
    intro hz
    have hc : A.1.2.2 = (zero (R := R) 3).1.2.2 := congrArg (fun z => z.1.2.2) hz
    exact IDomain.one_ne_zero hc
  have hgA : HasGrade 3 2 A := bivec3_hasGrade2 CRing.zero CRing.zero CRing.one
  have hreg : regressive 3 A A = zero 3 := by
    unfold A E3_01
    rw [regressive3_bivec3]
    simp [vec3, zero, CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.add_right_neg]
  have hfwd : regressiveFwd 3 A A = zero 3 := by
    rw [regressiveFwd_eq_sign_regressive (r := 2) (s := 2) (by decide) (by decide) (by decide) hgA hgA,
        hreg, signCl_zero_elem]
  have hrev : regressiveRev 3 A A = zero 3 := by
    rw [regressiveRev_eq_sign_regressive (r := 2) (s := 2) (by decide) (by decide) hgA hgA,
        hreg, signCl_zero_elem]
  refine ⟨hA_ne, hreg, hfwd, hrev, ?_⟩
  intro c hc
  rw [hreg, smul_zero] at hc
  exact hA_ne (Eq.symm hc)

/-! #### Explicit 4D Helpers for `Λ(R^4)` (`ℙ^3`) -/

section Dim4Helpers
variable {R : Type} [CRing R]

/-- Explicit 1-vector `x0 e_0 + x1 e_1 + x2 e_2 + x3 e_3` in `Λ^1(R^4)`. -/
def vec4 (x0 x1 x2 x3 : R) : Cl R 4 :=
  (vec3 x0 x1 x2, (((x3, CRing.zero), (CRing.zero, CRing.zero)), ((CRing.zero, CRing.zero), (CRing.zero, CRing.zero))))

def coord4_0 (v : Cl R 4) : R := v.1.1.1.2
def coord4_1 (v : Cl R 4) : R := v.1.1.2.1
def coord4_2 (v : Cl R 4) : R := v.1.2.1.1
def coord4_3 (v : Cl R 4) : R := v.2.1.1.1

def e4_0 : Cl R 4 := vec4 CRing.one CRing.zero CRing.zero CRing.zero
def e4_1 : Cl R 4 := vec4 CRing.zero CRing.one CRing.zero CRing.zero
def e4_2 : Cl R 4 := vec4 CRing.zero CRing.zero CRing.one CRing.zero
def e4_3 : Cl R 4 := vec4 CRing.zero CRing.zero CRing.zero CRing.one

theorem vec4_hasGrade1 (x0 x1 x2 x3 : R) : HasGrade 4 1 (vec4 x0 x1 x2 x3) := by
  simp [HasGrade, vec4, vec3, zero]

theorem hasGrade1_eq_vec4 {v : Cl R 4} (hv : HasGrade 4 1 v) :
    v = vec4 (coord4_0 v) (coord4_1 v) (coord4_2 v) (coord4_3 v) := by
  have h1 := hasGrade1_eq_vec3 hv.1
  rcases v with ⟨vL, ⟨⟨⟨d0, d1⟩, d23⟩, d47⟩⟩
  have hv2 := hv.2
  simp only [HasGrade] at hv2
  rcases hv2 with ⟨⟨⟨_, hd1⟩, hd23⟩, hd47⟩
  have hd1' : d1 = CRing.zero := hd1
  have hd23' : d23 = (CRing.zero, CRing.zero) := hd23
  have hd47' : d47 = ((CRing.zero, CRing.zero), (CRing.zero, CRing.zero)) := hd47
  unfold vec4 coord4_0 coord4_1 coord4_2 coord4_3
  refine Prod.ext h1 ?_
  change (((d0, d1), d23), d47) =
    (((d0, CRing.zero), (CRing.zero, CRing.zero)), ((CRing.zero, CRing.zero), (CRing.zero, CRing.zero)))
  rw [hd1', hd23', hd47']

end Dim4Helpers

def mask4_01 : Fin 4 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => true
  | _ => false

def mask4_02 : Fin 4 → Bool
  | ⟨0, _⟩ => true
  | ⟨2, _⟩ => true
  | _ => false

def mask4_012 : Fin 4 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true
  | _ => false

/-- **Refutation R2c (Distinct Coplanar Lines in `ℙ^3` / 2-Planes in `R^4` Meeting in `span{e_0}`):**
    In `R^4`, `A = e_0 ∧ e_1` and `B = e_0 ∧ e_2` are linearly independent 2-blades (`A ≠ c • B`)
    whose subspaces intersect in the nonzero 1D line `U ∩ W = span{e_0}` (`e_0 ∧ A = e_0 ∧ B = 0`),
    yet `A ∨ B = 0` (`A ∨_fwd B = 0`); likewise `(e_0 ∧ e_1 ∧ e_2) ∨ (e_0 ∧ e_1) = 0` at `r + s - n = 1`. -/
theorem r2_distinct_planes_k4_vanish {R : Type} [IDomain R] :
    let A : Cl R 4 := wedge 4 e4_0 e4_1
    let B : Cl R 4 := wedge 4 e4_0 e4_2
    let H : Cl R 4 := wedge 4 (wedge 4 e4_0 e4_1) e4_2
    e4_0 (R := R) ≠ zero 4 ∧
    wedge 4 e4_0 A = zero 4 ∧
    wedge 4 e4_0 B = zero 4 ∧
    (∀ c : R, A ≠ smul 4 c B) ∧
    regressive 4 A B = zero 4 ∧
    regressiveFwd 4 A B = zero 4 ∧
    regressive 4 H A = zero 4 ∧
    (∀ c : R, smul 4 c (regressive 4 A B) ≠ e4_0) := by
  intro A B H
  have he0_ne : e4_0 (R := R) ≠ zero 4 := by
    intro hz
    exact IDomain.one_ne_zero (congrArg (coord4_0 (R := R)) hz)
  have h_e0_A : wedge 4 e4_0 A = zero 4 := by
    change mul (zeroMetric 4) e4_0 (mul (zeroMetric 4) e4_0 e4_1) = zero 4
    rw [← mul_assoc (zeroMetric 4)]
    change mul (zeroMetric 4) (wedge 4 e4_0 e4_0) e4_1 = zero 4
    have hg0 : HasGrade 4 1 (e4_0 (R := R)) := vec4_hasGrade1 _ _ _ _
    rw [wedge_vec_self_eq_zero hg0]
    exact zero_mul (zeroMetric 4) e4_1
  have h_e0_B : wedge 4 e4_0 B = zero 4 := by
    change mul (zeroMetric 4) e4_0 (mul (zeroMetric 4) e4_0 e4_2) = zero 4
    rw [← mul_assoc (zeroMetric 4)]
    change mul (zeroMetric 4) (wedge 4 e4_0 e4_0) e4_2 = zero 4
    have hg0 : HasGrade 4 1 (e4_0 (R := R)) := vec4_hasGrade1 _ _ _ _
    rw [wedge_vec_self_eq_zero hg0]
    exact zero_mul (zeroMetric 4) e4_2
  have hA_pair : A = (E3_01, zero 3) := by
    change wedge 4 (e3_0, zero 3) (e3_1, zero 3) = (E3_01, zero 3)
    rw [wedge_eq]
    refine Prod.ext ?_ ?_
    · simp [e3_0, e3_1, E3_01, vec3, bivec3, wedge, mul, zeroMetric, initMetric, lastMetric,
            invol, add, neg, smul, CRing.mul_zero, CRing.zero_mul, CRing.mul_one,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero]
    · unfold wedge; rw [mul_zero, zero_mul, add_zero]
  have hB_pair : B = (E3_02, zero 3) := by
    change wedge 4 (e3_0, zero 3) (e3_2, zero 3) = (E3_02, zero 3)
    rw [wedge_eq]
    refine Prod.ext ?_ ?_
    · simp [e3_0, e3_2, E3_02, vec3, bivec3, wedge, mul, zeroMetric, initMetric, lastMetric,
            invol, add, neg, smul, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.neg_neg]
    · unfold wedge; rw [mul_zero, zero_mul, add_zero]
  have hindep : ∀ c : R, A ≠ smul 4 c B := by
    intro c hAB
    rw [hA_pair, hB_pair] at hAB
    have hc : (E3_01 (R := R)).1.2.2 = (smul 3 c (E3_02 (R := R))).1.2.2 :=
      congrArg (fun z : Cl R 4 => z.1.1.2.2) hAB
    simp only [E3_01, E3_02, bivec3, smul, CRing.mul_zero] at hc
    exact IDomain.one_ne_zero hc
  have hA_bb : A = basisBlade 4 mask4_01 := by
    rw [hA_pair]
    simp [E3_01, bivec3, basisBlade, mask4_01, zero, CRing.neg_zero]
  have hB_bb : B = basisBlade 4 mask4_02 := by
    rw [hB_pair]
    simp [E3_02, bivec3, basisBlade, mask4_02, zero, CRing.neg_neg]
  have hH_bb : H = basisBlade 4 mask4_012 := by
    change wedge 4 A (e3_2, zero 3) = basisBlade 4 mask4_012
    rw [hA_pair, wedge_eq]
    refine Prod.ext ?_ ?_
    · simp [E3_01, e3_2, bivec3, vec3, basisBlade, mask4_012, zero, wedge, mul, zeroMetric,
            initMetric, lastMetric, invol, add, neg, smul,
            CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero]
    · unfold wedge
      rw [mul_zero, zero_mul, add_zero]
      rfl
  have hregAB : regressive 4 A B = zero 4 := by
    rw [hA_bb, hB_bb]
    exact r2_nontransverse_basis_vanish mask4_01 mask4_02 rfl
  have hfwdAB : regressiveFwd 4 A B = zero 4 := by
    have hgA : HasGrade 4 2 A := by rw [hA_bb]; exact basisBlade_hasGrade mask4_01
    have hgB : HasGrade 4 2 B := by rw [hB_bb]; exact basisBlade_hasGrade mask4_02
    rw [regressiveFwd_eq_sign_regressive (r := 2) (s := 2) (by decide) (by decide) (by decide) hgA hgB,
        hregAB, signCl_zero_elem]
  have hregHA : regressive 4 H A = zero 4 := by
    rw [hH_bb, hA_bb]
    exact r2_nontransverse_basis_vanish mask4_012 mask4_01 rfl
  refine ⟨he0_ne, h_e0_A, h_e0_B, hindep, hregAB, hfwdAB, hregHA, ?_⟩
  intro c hc
  rw [hregAB, smul_zero] at hc
  exact he0_ne (Eq.symm hc)

/-- Core Intersection Lemma in `R^4`: along `A = e_0 ∧ e_1` and `B_t = (e_0 + t e_3) ∧ e_2`,
    for EVERY nonzero `t ≠ 0` in an integral domain `R`, the intersection `U ∩ W_t` is `{0}`! -/
theorem skew_pencil_intersection_zero {R : Type} [IDomain R]
    {t : R} (ht : t ≠ CRing.zero) {v : Cl R 4} (hv : HasGrade 4 1 v)
    (hU : wedge 4 v (wedge 4 e4_0 e4_1) = zero 4)
    (hWt : wedge 4 v (wedge 4 (add 4 e4_0 (smul 4 t e4_3)) e4_2) = zero 4) :
    v = zero 4 := by
  have hv_eq := hasGrade1_eq_vec4 hv
  let x0 := coord4_0 v
  let x1 := coord4_1 v
  let x2 := coord4_2 v
  let x3 := coord4_3 v
  have hv_pair : v = (vec3 x0 x1 x2, smul 3 x3 (one 3)) := by
    rw [hv_eq]
    simp only [vec4, smul, one, zero, CRing.mul_one, CRing.mul_zero]
    rfl
  have hA_pair : wedge 4 (e4_0 (R := R)) e4_1 = (E3_01, zero 3) := by
    change wedge 4 (e3_0, zero 3) (e3_1, zero 3) = (E3_01, zero 3)
    rw [wedge_eq]
    refine Prod.ext ?_ (by unfold wedge; rw [mul_zero, zero_mul, add_zero])
    simp [e3_0, e3_1, E3_01, vec3, bivec3, wedge, mul, zeroMetric, initMetric, lastMetric,
          invol, add, neg, smul, CRing.mul_zero, CRing.zero_mul, CRing.mul_one,
          CRing.add_zero, CRing.zero_add, CRing.neg_zero]
  have hBt_pair : wedge 4 (add 4 (e4_0 (R := R)) (smul 4 t e4_3)) e4_2 =
      (E3_02, smul 3 (CRing.neg t) e3_2) := by
    have hsum : add 4 (e4_0 (R := R)) (smul 4 t e4_3) = (e3_0, smul 3 t (one 3)) := by
      simp [e4_0, e4_3, vec4, e3_0, vec3, add, smul, one, zero,
            CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.zero_add]
    rw [hsum]
    change wedge 4 (e3_0, smul 3 t (one 3)) (e3_2, zero 3) = (E3_02, smul 3 (CRing.neg t) e3_2)
    rw [wedge_eq]
    refine Prod.ext ?_ ?_
    · simp [e3_0, e3_2, E3_02, vec3, bivec3, wedge, mul, zeroMetric, initMetric, lastMetric,
            invol, add, neg, smul, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
            CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.neg_neg]
    · change add 3 (wedge 3 e3_0 (zero 3)) (wedge 3 (smul 3 t (one 3)) (invol 3 e3_2)) =
        smul 3 (CRing.neg t) e3_2
      have hg2 : HasGrade 3 1 (e3_2 (R := R)) := vec3_hasGrade1 _ _ _
      unfold wedge
      rw [mul_zero, zero_add, smul_mul, one_mul, invol_on_grade hg2]
      simp [signCl, smul_neg, neg_smul]
  rw [hv_pair, hA_pair, wedge_eq] at hU
  have hx2 : x2 = CRing.zero := by
    have h1 : topCoeff 3 (wedge 3 (vec3 x0 x1 x2) E3_01) = CRing.zero := by
      have hf := congrArg Prod.fst hU
      change wedge 3 (vec3 x0 x1 x2) E3_01 = zero 3 at hf
      rw [hf]; rfl
    unfold E3_01 at h1
    rw [wedge3_vec3_bivec3_top] at h1
    simp only [CRing.mul_zero, CRing.mul_one, CRing.add_zero, CRing.zero_add] at h1
    exact h1
  have hx3 : x3 = CRing.zero := by
    have hs := congrArg Prod.snd hU
    change add 3 (wedge 3 (vec3 x0 x1 x2) (zero 3))
      (wedge 3 (smul 3 x3 (one 3)) (invol 3 E3_01)) = zero 3 at hs
    have hg01 : HasGrade 3 2 (E3_01 (R := R)) := bivec3_hasGrade2 _ _ _
    have hi : invol 3 (E3_01 (R := R)) = E3_01 := by
      rw [invol_on_grade hg01, signCl_even 3 1]
    unfold wedge at hs
    rw [mul_zero, zero_add, hi, smul_mul, one_mul] at hs
    have hc := congrArg (fun z : Cl R 3 => z.1.2.2) hs
    simp only [E3_01, bivec3, smul, zero, CRing.mul_one] at hc
    exact hc
  have hv_red : v = (vec3 x0 x1 CRing.zero, zero 3) := by
    rw [hv_pair, hx2, hx3, zero_smul]
  rw [hv_red, hBt_pair, wedge_eq] at hWt
  have hx1 : x1 = CRing.zero := by
    have h1 : topCoeff 3 (wedge 3 (vec3 x0 x1 CRing.zero) E3_02) = CRing.zero := by
      have hf := congrArg Prod.fst hWt
      change wedge 3 (vec3 x0 x1 CRing.zero) E3_02 = zero 3 at hf
      rw [hf]; rfl
    unfold E3_02 at h1
    rw [wedge3_vec3_bivec3_top] at h1
    simp only [CRing.mul_zero, CRing.mul_neg, CRing.mul_one, CRing.add_zero, CRing.zero_add] at h1
    have hnn := congrArg CRing.neg h1
    rw [CRing.neg_neg, CRing.neg_zero] at hnn
    exact hnn
  have hx0 : x0 = CRing.zero := by
    have hs := congrArg Prod.snd hWt
    change add 3 (wedge 3 (vec3 x0 x1 CRing.zero) (smul 3 (CRing.neg t) e3_2))
      (wedge 3 (zero 3) (invol 3 E3_02)) = zero 3 at hs
    rw [hx1] at hs
    unfold wedge at hs
    rw [zero_mul, add_zero, mul_smul] at hs
    have hc := congrArg (fun z : Cl R 3 => z.2.1.2) hs
    simp only [vec3, e3_2, mul, zeroMetric, initMetric, lastMetric, invol, add, neg, smul, zero,
      CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.add_zero, CRing.zero_add,
      CRing.neg_zero, CRing.neg_mul] at hc
    -- `hc` is `(-t) * x0 = 0` or `-((-t) * x0) = 0`:
    have hmul : CRing.mul t x0 = CRing.zero := by
      -- Notice `vec3 x0 0 0 ∧ e3_2` has `.2.1.2` equal to `x0`!
      -- Wait: let's check `(x0 e_0) ∧ e_2`: `( ((0, x0), (0, 0)), ((0, 0), (0, 0)) ) ∧ ( ((0,0),(0,0)), ((1,0),(0,0)) )`
      -- `.2` is `((0, x0), (0, 0)) ∧ ((1, 0), (0, 0)) = ((0, x0 * 1), (0, 0))`, so `.2.1.2` IS `+x0`!
      -- Multiplying by `neg t` gives `CRing.mul (CRing.neg t) x0 = 0` (`-(t * x0) = 0`)!
      have hnn := congrArg CRing.neg hc
      rw [CRing.neg_neg, CRing.neg_zero] at hnn
      exact hnn
    cases IDomain.mul_eq_zero hmul with
    | inl hbad => exact absurd hbad ht
    | inr h0 => exact h0
  rw [hv_red, hx0, hx1]
  rfl

/-- **Refutation R2d (Arbitrary-Degree Polynomial Intersection Impossibility in `R^4`):**
    Over ANY integral domain `R` (`ℤ`, `ℚ`, `ℝ`, `ℂ`), let `F : Cl R 4 → Cl R 4 → Cl R 4`
    be ANY map whose coordinates along the pencil `B_t = (e_0 + t e_3) ∧ e_2` are polynomials
    in `t` of degree `≤ D` (`length ≤ D + 1`), and suppose `F(A, B_t) ∈ U ∩ W_t` for `D + 1`
    pairwise distinct nonzero scalars `roots : List R`. Then `F(e_0 ∧ e_1, e_0 ∧ e_2) = 0`! -/
theorem r2_no_polynomial_intersection_k4 {R : Type} [IDomain R]
    (F : Cl R 4 → Cl R 4 → Cl R 4)
    (p0 p1 p2 p3 : List R)
    (roots : List R)
    (hnd : PairwiseNe roots)
    (hnz : ∀ s, s ∈ roots → s ≠ CRing.zero)
    (hlen0 : p0.length ≤ roots.length)
    (hlen1 : p1.length ≤ roots.length)
    (hlen2 : p2.length ≤ roots.length)
    (hlen3 : p3.length ≤ roots.length)
    (hpoly : ∀ t : R,
      F (wedge 4 e4_0 e4_1) (wedge 4 (add 4 e4_0 (smul 4 t e4_3)) e4_2) =
        vec4 (evalPoly p0 t) (evalPoly p1 t) (evalPoly p2 t) (evalPoly p3 t))
    (hsub : ∀ s, s ∈ roots →
      let Bt := wedge 4 (add 4 e4_0 (smul 4 s e4_3)) e4_2
      let v := F (wedge 4 e4_0 e4_1) Bt
      wedge 4 v (wedge 4 e4_0 e4_1) = zero 4 ∧ wedge 4 v Bt = zero 4) :
    F (wedge 4 e4_0 e4_1) (wedge 4 e4_0 e4_2) = zero 4 := by
  have hvan_all : ∀ s, s ∈ roots →
      evalPoly p0 s = CRing.zero ∧ evalPoly p1 s = CRing.zero ∧
      evalPoly p2 s = CRing.zero ∧ evalPoly p3 s = CRing.zero := by
    intro s hs
    have hs_nz : s ≠ CRing.zero := hnz s hs
    have hmem := hsub s hs
    have hg : HasGrade 4 1 (F (wedge 4 e4_0 e4_1) (wedge 4 (add 4 e4_0 (smul 4 s e4_3)) e4_2)) := by
      rw [hpoly s]; exact vec4_hasGrade1 _ _ _ _
    have hv0 : F (wedge 4 e4_0 e4_1) (wedge 4 (add 4 e4_0 (smul 4 s e4_3)) e4_2) = zero 4 :=
      skew_pencil_intersection_zero hs_nz hg hmem.1 hmem.2
    rw [hpoly s] at hv0
    exact ⟨congrArg coord4_0 hv0, congrArg coord4_1 hv0, congrArg coord4_2 hv0, congrArg coord4_3 hv0⟩
  have z0 := evalPoly_eq_zero_of_roots roots p0 hnd hlen0 (fun s hs => (hvan_all s hs).1) CRing.zero
  have z1 := evalPoly_eq_zero_of_roots roots p1 hnd hlen1 (fun s hs => (hvan_all s hs).2.1) CRing.zero
  have z2 := evalPoly_eq_zero_of_roots roots p2 hnd hlen2 (fun s hs => (hvan_all s hs).2.2.1) CRing.zero
  have z3 := evalPoly_eq_zero_of_roots roots p3 hnd hlen3 (fun s hs => (hvan_all s hs).2.2.2) CRing.zero
  have hB0 : wedge 4 (add 4 (e4_0 (R := R)) (smul 4 CRing.zero e4_3)) e4_2 = wedge 4 e4_0 e4_2 := by
    rw [zero_smul, add_zero]
  have hp0 := hpoly CRing.zero
  rw [hB0, z0, z1, z2, z3] at hp0
  exact hp0

/-- Explicit Bilinear Corollary over `ℚ` (via `t = 1, 2`): NO `ℚ`-bilinear map `F` on `Λ^2(ℚ^4)`
    satisfying `F(A, B) ∈ U ∩ W` can be nonzero on `(e_0 ∧ e_1, e_0 ∧ e_2)`! -/
theorem r2_no_bilinear_intersection_q4
    (F : Cl QRat 4 → Cl QRat 4 → Cl QRat 4)
    (hbil : IsBilinear 4 F)
    (hgrade : ∀ A B, HasGrade 4 2 A → HasGrade 4 2 B → HasGrade 4 1 (F A B))
    (hsub : ∀ A B, HasGrade 4 2 A → HasGrade 4 2 B →
      wedge 4 (F A B) A = zero 4 ∧ wedge 4 (F A B) B = zero 4) :
    F (wedge 4 e4_0 e4_1) (wedge 4 e4_0 e4_2) = zero 4 := by
  let A := wedge 4 (e4_0 (R := QRat)) e4_1
  let B0 := wedge 4 (e4_0 (R := QRat)) e4_2
  let D := wedge 4 (e4_3 (R := QRat)) e4_2
  have hgA : HasGrade 4 2 A := wedge_hasGrade (vec4_hasGrade1 _ _ _ _) (vec4_hasGrade1 _ _ _ _)
  have hgB0 : HasGrade 4 2 B0 := wedge_hasGrade (vec4_hasGrade1 _ _ _ _) (vec4_hasGrade1 _ _ _ _)
  have hgD : HasGrade 4 2 D := wedge_hasGrade (vec4_hasGrade1 _ _ _ _) (vec4_hasGrade1 _ _ _ _)
  let v0 := F A B0
  let v1 := F A D
  have hv0_eq := hasGrade1_eq_vec4 (hgrade A B0 hgA hgB0)
  have hv1_eq := hasGrade1_eq_vec4 (hgrade A D hgA hgD)
  have hnd : PairwiseNe [QRat.ofInt 1, QRat.ofInt 2] := by
    refine And.intro ?_ (And.intro (fun _ h => nomatch h) trivial)
    intro s hs
    cases hs with
    | head => exact QRat.ne_of_eqFracBool_diff 2 1 (by decide)
    | tail _ h => nomatch h
  have hnz : ∀ s, s ∈ [QRat.ofInt 1, QRat.ofInt 2] → s ≠ CRing.zero := by
    intro s hs
    cases hs with
    | head => exact QRat.ne_of_eqFracBool_diff 1 1 (by decide)
    | tail _ hs2 =>
        cases hs2 with
        | head => exact QRat.ne_of_eqFracBool_diff 2 1 (by decide)
        | tail _ h => nomatch h
  apply r2_no_polynomial_intersection_k4 F
    [coord4_0 v0, coord4_0 v1] [coord4_1 v0, coord4_1 v1]
    [coord4_2 v0, coord4_2 v1] [coord4_3 v0, coord4_3 v1]
    [QRat.ofInt 1, QRat.ofInt 2] hnd hnz
    (Nat.le_refl 2) (Nat.le_refl 2) (Nat.le_refl 2) (Nat.le_refl 2)
  · intro t
    have hBt : wedge 4 (add 4 e4_0 (smul 4 t e4_3)) e4_2 = add 4 B0 (smul 4 t D) := by
      unfold B0 D wedge
      rw [right_distrib, smul_mul]
    change F A (wedge 4 (add 4 e4_0 (smul 4 t e4_3)) e4_2) = _
    rw [hBt, hbil.add_right, hbil.smul_right]
    change add 4 (F A B0) (smul 4 t (F A D)) = _
    rw [hv0_eq, hv1_eq]
    unfold v0 v1
    simp [vec4, vec3, evalPoly, add, smul, CRing.mul_zero, CRing.add_zero]
  · intro s _
    have hgBs : HasGrade 4 2 (wedge 4 (add 4 e4_0 (smul 4 s e4_3)) e4_2) :=
      wedge_hasGrade (hasGrade_add (vec4_hasGrade1 _ _ _ _) (hasGrade_smul s (vec4_hasGrade1 _ _ _ _)))
        (vec4_hasGrade1 _ _ _ _)
    exact hsub _ _ hgA hgBs

/-- **Refutation R2e (Incident-Only Bilinear Impossibility in `R^4` — Zero Assumption on Skew Pairs!):**
    Over ANY integral domain `R`, even with ZERO condition on skew pairs (`U ∩ W = {0}`),
    NO `R`-bilinear map `F : Cl R 4 → Cl R 4 → Cl R 4` can output a nonzero vector in `span{e_0}`
    for every incident 2-plane `W_w = span{e_0, α e_2 + β e_3}` (`(α, β) ≠ (0, 0)`) meeting
    `U = span{e_0, e_1}` in the 1D line `span{e_0}`! -/
theorem r2_no_incident_only_bilinear_intersection_k4 {R : Type} [IDomain R] :
    ¬ ∃ F : Cl R 4 → Cl R 4 → Cl R 4,
      IsBilinear 4 F ∧
      (∀ α β : R, (α ≠ CRing.zero ∨ β ≠ CRing.zero) →
        ∃ c : R, c ≠ CRing.zero ∧
          F (wedge 4 e4_0 e4_1)
            (wedge 4 e4_0 (add 4 (smul 4 α e4_2) (smul 4 β e4_3))) = smul 4 c e4_0) := by
  rintro ⟨F, hbil, hinc⟩
  obtain ⟨c2, hc2_ne, hF2⟩ := hinc CRing.one CRing.zero (Or.inl IDomain.one_ne_zero)
  obtain ⟨c3, _, hF3⟩ := hinc CRing.zero CRing.one (Or.inr IDomain.one_ne_zero)
  rw [one_smul, zero_smul, add_zero] at hF2
  rw [zero_smul, one_smul, zero_add] at hF3
  obtain ⟨c_star, hc_star_ne, hF_star⟩ :=
    hinc (CRing.neg c3) c2 (Or.inr hc2_ne)
  have hexpand :
      wedge 4 e4_0 (add 4 (smul 4 (CRing.neg c3) e4_2) (smul 4 c2 e4_3)) =
      add 4 (smul 4 (CRing.neg c3) (wedge 4 e4_0 e4_2))
            (smul 4 c2 (wedge 4 e4_0 e4_3)) := by
    unfold wedge
    rw [left_distrib, mul_smul, mul_smul]
  rw [hexpand, hbil.add_right, hbil.smul_right, hbil.smul_right, hF2, hF3,
      smul_smul, smul_smul, ← add_smul] at hF_star
  have hzero_coeff : CRing.add (CRing.mul (CRing.neg c3) c2) (CRing.mul c2 c3) = CRing.zero := by
    rw [CRing.neg_mul, CRing.mul_comm c3 c2, CRing.add_left_neg]
  rw [hzero_coeff, zero_smul] at hF_star
  have hcoord := congrArg coord4_0 hF_star
  simp only [e4_0, vec4, vec3, smul, zero, coord4_0, CRing.mul_one] at hcoord
  exact hc_star_ne (Eq.symm hcoord)

/-! ### Part IV: Refutation R3 — Degenerate PGA Metric (`e_0^2 = 0`) Obstructions -/

section DegeneratePGA
variable {R : Type} [CRing R]

/-- Metric Clifford Hodge dual `⋆_q(x) := x̃ ·_q ω` in Euclidean PGA `Cl_{m, 0, 1}`. -/
def pgaMetricStar (n : Nat) (x : Cl R n) : Cl R n :=
  mul (pgaMetric n) (rev n x) (omega n)

/-- Naive metric-duality regressive product `⋆_q(⋆_q(A) ∧ ⋆_q(B))` in `Cl_{m, 0, 1}`. -/
def pgaMetricMeet (n : Nat) (A B : Cl R n) : Cl R n :=
  pgaMetricStar n (wedge n (pgaMetricStar n A) (pgaMetricStar n B))

theorem omega_inNullIdeal (m : Nat) : inNullIdeal m (omega (R := R) (m + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ⟨inNullIdeal_zero m, ih⟩

theorem pgaMetric_zero_at_zero (m : Nat) :
    pgaMetric (R := R) (m + 1) ⟨0, Nat.zero_lt_succ m⟩ = CRing.zero := rfl

/-- In `Cl_{m, 0, 1}` (`e_0^2 = 0`), the metric Hodge dual `⋆_q(x)` lands inside the null
    ideal `(e_0)` for EVERY multivector `x`! -/
theorem r3_pga_metricStar_in_nullIdeal (m : Nat) (x : Cl R (m + 1)) :
    inNullIdeal m (pgaMetricStar (m + 1) x) :=
  inNullIdeal_mul_right m (pgaMetric (m + 1)) (pgaMetric_zero_at_zero m)
    (rev (m + 1) x) (omega_inNullIdeal m)

/-- **Refutation R3a (Identical Vanishing of `⋆_q ∘ ⋆_q` Across ALL of `Cl_{m, 0, 1}`):**
    For EVERY `m ≥ 0` and EVERY `x ∈ Cl_{m, 0, 1}`, `⋆_q(⋆_q(x)) = 0`! -/
theorem r3_pga_metricStar_sq_eq_zero (m : Nat) (x : Cl R (m + 1)) :
    pgaMetricStar (m + 1) (pgaMetricStar (m + 1) x) = zero (m + 1) := by
  unfold pgaMetricStar
  exact inNullIdeal_mul_nilpotent m (pgaMetric (m + 1)) (pgaMetric_zero_at_zero m)
    (inNullIdeal_rev m (r3_pga_metricStar_in_nullIdeal m x))
    (omega_inNullIdeal m)

/-- **Refutation R3b (Identical Vanishing of Metric-Dual Wedge & Meet Across ALL of `Cl_{m, 0, 1}`):**
    For EVERY `m ≥ 0` and ALL `A, B ∈ Cl_{m, 0, 1}`, `⋆_q(A) ∧ ⋆_q(B) = 0` and
    `pgaMetricMeet (m + 1) A B = 0` identically! -/
theorem r3_pga_metricStar_wedge_eq_zero (m : Nat) (A B : Cl R (m + 1)) :
    wedge (m + 1) (pgaMetricStar (m + 1) A) (pgaMetricStar (m + 1) B) = zero (m + 1) ∧
    pgaMetricMeet (m + 1) A B = zero (m + 1) := by
  have hw : wedge (m + 1) (pgaMetricStar (m + 1) A) (pgaMetricStar (m + 1) B) = zero (m + 1) :=
    inNullIdeal_mul_nilpotent m (zeroMetric (m + 1)) rfl
      (r3_pga_metricStar_in_nullIdeal m A)
      (r3_pga_metricStar_in_nullIdeal m B)
  refine ⟨hw, ?_⟩
  unfold pgaMetricMeet
  rw [hw]
  unfold pgaMetricStar
  rw [rev_zero, zero_mul]

end DegeneratePGA

/-- **Refutation R3c (2D PGA `Cl_{2, 0, 1}` Origin-Lines Obstruction):**
    In 2D PGA `Cl_{2, 0, 1}` (`n = 3`), the two orthogonal lines through the origin
    `A = e_0 ∧ e_1` and `B = e_0 ∧ e_2` meet transversely at `e_0` under non-metric Poincaré
    duality (`A ∨ B = e_0 ≠ 0`), YET `⋆_q(A) = 0`, `⋆_q(B) = 0`, and for ALL two-sided
    Clifford multipliers `L1, R1, L2, R2 ∈ Cl_{2, 0, 1}`,
      `(L1 ·_q A ·_q R1) ∧ (L2 ·_q B ·_q R2) = 0`! -/
theorem r3_pga_origin_lines_obstruction {R : Type} [IDomain R] :
    let A : Cl R 3 := E3_01
    let B : Cl R 3 := E3_02
    regressive 3 A B = e3_0 ∧
    e3_0 (R := R) ≠ zero 3 ∧
    pgaMetricStar 3 A = zero 3 ∧
    pgaMetricStar 3 B = zero 3 ∧
    (∀ c : R, smul 3 c (pgaMetricMeet 3 A B) ≠ e3_0) ∧
    (∀ L1 R1 L2 R2 : Cl R 3,
      wedge 3 (mul (pgaMetric 3) (mul (pgaMetric 3) L1 A) R1)
              (mul (pgaMetric 3) (mul (pgaMetric 3) L2 B) R2) = zero 3) := by
  intro A B
  have hmeet : regressive 3 A B = e3_0 := by
    unfold A B E3_01 E3_02
    rw [regressive3_bivec3]
    simp [vec3, e3_0, CRing.sub, CRing.mul_zero, CRing.zero_mul, CRing.mul_one, CRing.one_mul,
          CRing.add_zero, CRing.zero_add, CRing.neg_zero, CRing.mul_neg, CRing.neg_neg]
  have he0_ne : e3_0 (R := R) ≠ zero 3 := by
    intro hz
    exact IDomain.one_ne_zero (congrArg (coord3_0 (R := R)) hz)
  have hA_ideal : inNullIdeal 2 A := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  have hB_ideal : inNullIdeal 2 B := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  have hsA : pgaMetricStar 3 A = zero 3 :=
    inNullIdeal_mul_nilpotent 2 (pgaMetric 3) rfl (inNullIdeal_rev 2 hA_ideal) (omega_inNullIdeal 2)
  have hsB : pgaMetricStar 3 B = zero 3 :=
    inNullIdeal_mul_nilpotent 2 (pgaMetric 3) rfl (inNullIdeal_rev 2 hB_ideal) (omega_inNullIdeal 2)
  refine ⟨hmeet, he0_ne, hsA, hsB, ?_, ?_⟩
  · intro c hc
    rw [(r3_pga_metricStar_wedge_eq_zero 2 A B).2, smul_zero] at hc
    exact he0_ne (Eq.symm hc)
  · intro L1 R1 L2 R2
    have h1 : inNullIdeal 2 (mul (pgaMetric 3) (mul (pgaMetric 3) L1 A) R1) :=
      inNullIdeal_mul_left 2 (pgaMetric 3) rfl
        (inNullIdeal_mul_right 2 (pgaMetric 3) rfl L1 hA_ideal) R1
    have h2 : inNullIdeal 2 (mul (pgaMetric 3) (mul (pgaMetric 3) L2 B) R2) :=
      inNullIdeal_mul_left 2 (pgaMetric 3) rfl
        (inNullIdeal_mul_right 2 (pgaMetric 3) rfl L2 hB_ideal) R2
    exact inNullIdeal_mul_nilpotent 2 (zeroMetric 3) rfl h1 h2

/-! ### Part V: Master Negation of Unqualified Conjecture 00000007617 -/

/-- **Master Refutation Theorem (`conjecture_00000007617_false`):**
    Simultaneously packages all three independent refutations of the unqualified conjecture. -/
theorem conjecture_00000007617_false :
    (let A : Cl QRat 3 := E3_01
     let B : Cl QRat 3 := bivec3 QRat.zero (CRing.neg q4_5) q3_5
     inner (euclidMetric 3) A A = QRat.one ∧
     inner (euclidMetric 3) B B = QRat.one ∧
     regressive 3 A B ≠ e3_0 ∧ regressive 3 A B ≠ neg 3 e3_0) ∧
    (∀ F : Cl QRat 4 → Cl QRat 4 → Cl QRat 4,
      IsBilinear 4 F →
      (∀ A B, HasGrade 4 2 A → HasGrade 4 2 B → HasGrade 4 1 (F A B)) →
      (∀ A B, HasGrade 4 2 A → HasGrade 4 2 B →
        wedge 4 (F A B) A = zero 4 ∧ wedge 4 (F A B) B = zero 4) →
      F (wedge 4 e4_0 e4_1) (wedge 4 e4_0 e4_2) = zero 4) ∧
    (∀ A B : Cl QRat 3, pgaMetricMeet 3 A B = zero 3) := by
  refine ⟨?_, r2_no_bilinear_intersection_q4, fun A B => (r3_pga_metricStar_wedge_eq_zero 2 A B).2⟩
  have hr1 := r1_unit_plucker_blades_non_sign_factor
  exact ⟨hr1.1, hr1.2.1, hr1.2.2.2.2.2.1, hr1.2.2.2.2.2.2⟩

end Cl
end Conjecture00000007617

/-! ### Kernel Axiom Audit on All Major Formalized Theorems -/

#print axioms Conjecture00000007617.Cl.topCoeff_wedge_pStar
#print axioms Conjecture00000007617.Cl.positive_transverse_basis_meet
#print axioms Conjecture00000007617.Cl.positive_convention_sign_corrections
#print axioms Conjecture00000007617.Cl.p2_lagrange_grassmann_meet
#print axioms Conjecture00000007617.Cl.p2_transverse_bilinear_rigidity
#print axioms Conjecture00000007617.Cl.r1_bracket_scaling_nonunique
#print axioms Conjecture00000007617.Cl.r1_unit_plucker_blades_non_sign_factor
#print axioms Conjecture00000007617.Cl.r1_no_unit_preserving_bilinear_meet
#print axioms Conjecture00000007617.Cl.r2_coinciding_lines_p2_vanish
#print axioms Conjecture00000007617.Cl.r2_distinct_planes_k4_vanish
#print axioms Conjecture00000007617.Cl.r2_no_polynomial_intersection_k4
#print axioms Conjecture00000007617.Cl.r2_no_bilinear_intersection_q4
#print axioms Conjecture00000007617.Cl.r2_no_incident_only_bilinear_intersection_k4
#print axioms Conjecture00000007617.Cl.r3_pga_metricStar_sq_eq_zero
#print axioms Conjecture00000007617.Cl.r3_pga_origin_lines_obstruction
#print axioms Conjecture00000007617.Cl.conjecture_00000007617_false
