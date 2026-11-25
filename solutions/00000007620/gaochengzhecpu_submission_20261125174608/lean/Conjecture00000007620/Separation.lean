/-
  Conjecture 00000007620 — Explicit Same-Group Different-Signature Separation
  Proves both:
  1. Minimal odd-dimensional conformal separation: (1, 0) vs (0, 1) -> ambient (2, 1) vs (1, 2)
     (central idempotent & central pseudoscalar spectrum separation, Cl_{2,1}(F) ≇ Cl_{1,2}(F)).
  2. Lorentzian even-dimensional conformal separation: (2, 0) vs (0, 2) -> ambient (3, 1) vs (1, 3)
     (Pierce idempotent & quaternionic spinor rank separation with trivial centers, Cl_{3,1}(F) ≇ Cl_{1,3}(F)).
  Universal over any `FormallyRealField F` (including ℝ and ℚ), and unconditionally instantiated on `RatField`.
  Pure Core Lean 4.19.0 (zero external dependencies, zero sorry, zero axioms).
-/
import Conjecture00000007620.Clifford

namespace Conjecture00000007620

universe u

/-! ### General Induction and Center Tools on `CliffordAlg` -/

theorem anticomm_swap {A : Type u} [AssocRing A] {u v : A} (h : u * v + v * u = 0) :
    u * v = -(v * u) := by
  have h1 : -(u * v) = v * u := neg_eq_of_add_eq_zero h
  rw [← neg_neg_ring (u * v), h1]

section CliffordTools

variable {F : Type u} [FormallyRealField F]

@[simp] private theorem clZero_zero : (clZero 0 : CliffordCarrier F 0) = 0 := rfl
@[simp] private theorem clOne_zero : (clOne 0 : CliffordCarrier F 0) = 1 := rfl
@[simp] private theorem clAdd_zero_dim (x y : F) : clAdd (n := 0) x y = x + y := rfl
@[simp] private theorem clNeg_zero_dim (x : F) : clNeg (n := 0) x = -x := rfl
@[simp] private theorem clScale_zero_dim (c x : F) : clScale (n := 0) c x = c * x := rfl
@[simp] private theorem clInvol_zero_dim (x : F) : clInvol (n := 0) x = x := rfl
@[simp] private theorem clMul_zero_dim (q : Fin 0 → F) (x y : F) :
    clMul (n := 0) q x y = x * y := rfl
@[simp] private theorem clLiftAux_zero_dim {A : Type u} [AssocRing A]
    (φ : RingHom F A) (g : Fin 0 → A) (c : F) :
    CliffordAlg.clLiftAux (n := 0) φ g c = φ.toFun c := rfl

private theorem CliffordAlg.raw_zero {n : Nat} {q : Fin n → F} :
    (0 : CliffordAlg F n q).raw = clZero n := rfl
private theorem CliffordAlg.raw_one {n : Nat} {q : Fin n → F} :
    (1 : CliffordAlg F n q).raw = clOne n := rfl
private theorem CliffordAlg.raw_add {n : Nat} {q : Fin n → F} (x y : CliffordAlg F n q) :
    (x + y).raw = clAdd x.raw y.raw := rfl
private theorem CliffordAlg.raw_neg {n : Nat} {q : Fin n → F} (x : CliffordAlg F n q) :
    (-x).raw = clNeg x.raw := rfl
private theorem CliffordAlg.raw_mul {n : Nat} {q : Fin n → F} (x y : CliffordAlg F n q) :
    (x * y).raw = clMul q x.raw y.raw := rfl
private theorem CliffordAlg.raw_ofScalar {n : Nat} {q : Fin n → F} (c : F) :
    (CliffordAlg.ofScalar c : CliffordAlg F n q).raw = clScale c (clOne n) := rfl
private theorem CliffordAlg.raw_smul {n : Nat} {q : Fin n → F} (c : F) (x : CliffordAlg F n q) :
    (CliffordAlg.smul c x).raw = clScale c x.raw := rfl
omit [FormallyRealField F] in
private theorem CliffordAlg.scalarPart_fst {m : Nat} (z : CliffordCarrier F (m + 1)) :
    CliffordAlg.scalarPart z = CliffordAlg.scalarPart z.1 := by
  rcases z with ⟨a, b⟩
  rfl
private theorem CliffordAlg.scalarPart_add {m : Nat} (x y : CliffordCarrier F m) :
    CliffordAlg.scalarPart (clAdd x y) = CliffordAlg.scalarPart x + CliffordAlg.scalarPart y := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    exact ih x1 y1

/-- Structural induction principle for `CliffordAlg F n q`: any predicate containing
    scalars and basis generators `γ_i` and closed under `+` and `*` holds everywhere. -/
theorem CliffordAlg.ind_on {n : Nat} {q : Fin n → F}
    {P : CliffordAlg F n q → Prop}
    (hscalar : ∀ c : F, P (CliffordAlg.ofScalar c))
    (hgamma : ∀ i : Fin n, P (CliffordAlg.gamma i))
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → P y → P (x * y)) :
    ∀ x : CliffordAlg F n q, P x := by
  induction n with
  | zero =>
    intro x
    rcases x with ⟨r⟩
    have hs := hscalar r
    have heq : (CliffordAlg.ofScalar r : CliffordAlg F 0 q) = ⟨r⟩ := by
      apply CliffordAlg.ext
      show r * 1 = r
      exact AssocRing.mul_one r
    rw [heq] at hs
    exact hs
  | succ m ih =>
    intro x
    rcases x with ⟨⟨a, b⟩⟩
    let qi : Fin m → F := fun j => q (finCastSucc j)
    let incl : CliffordAlg F m qi → CliffordAlg F (m + 1) q :=
      fun y => ⟨(y.raw, clZero m)⟩
    have incl_add : ∀ y1 y2 : CliffordAlg F m qi, incl (y1 + y2) = incl y1 + incl y2 := by
      intro y1 y2
      apply CliffordAlg.ext
      exact Prod.ext rfl (clAdd_zero (clZero m)).symm
    have incl_mul : ∀ y1 y2 : CliffordAlg F m qi, incl (y1 * y2) = incl y1 * incl y2 := by
      intro y1 y2
      apply CliffordAlg.ext
      show (clMul qi y1.raw y2.raw, clZero m) = clMul q (y1.raw, clZero m) (y2.raw, clZero m)
      simp only [clMul_succ, clInvol_zero, clMul_zero_left, clMul_zero_right,
                 clScale_zero, clAdd_zero, clZero_add]
      rfl
    have hP_incl : ∀ y : CliffordAlg F m qi, P (incl y) := by
      apply ih (q := qi) (P := fun y => P (incl y))
      · intro c
        have hinc : incl (CliffordAlg.ofScalar c) = CliffordAlg.ofScalar c := by
          apply CliffordAlg.ext
          show (clScale c (clOne m), clZero m) = (clScale c (clOne m), clScale c (clZero m))
          rw [clScale_zero]
        rw [hinc]
        exact hscalar c
      · intro j
        have hinc : incl (CliffordAlg.gamma j) = CliffordAlg.gamma (finCastSucc j) := by
          apply CliffordAlg.ext
          unfold CliffordAlg.gamma
          exact (CliffordAlg.clGamma_castSucc j).symm
        rw [hinc]
        exact hgamma (finCastSucc j)
      · intro y1 y2 hy1 hy2
        rw [incl_add]
        exact hadd _ _ hy1 hy2
      · intro y1 y2 hy1 hy2
        rw [incl_mul]
        exact hmul _ _ hy1 hy2
    have hdecomp :
        (⟨(a, b)⟩ : CliffordAlg F (m + 1) q) =
        incl ⟨a⟩ + CliffordAlg.gamma (finLast m) * incl ⟨b⟩ := by
      apply CliffordAlg.ext
      show (a, b) = clAdd (n := m + 1) (a, clZero m)
        (clMul q (CliffordAlg.clGamma (finLast m)) (b, clZero m))
      simp only [CliffordAlg.clGamma_last, clMul_succ, clAdd_succ,
                 clInvol_zero, clInvol_one, clMul_zero_left, clMul_zero_right,
                 clOne_mul, clScale_zero, clAdd_zero, clZero_add]
    rw [hdecomp]
    exact hadd _ _ (hP_incl ⟨a⟩) (hmul _ _ (hgamma (finLast m)) (hP_incl ⟨b⟩))

/-- An element of `CliffordAlg F n q` is central iff it commutes with all generators `γ_i`. -/
theorem central_of_comm_gamma {n : Nat} {q : Fin n → F}
    (z : CliffordAlg F n q)
    (hcomm : ∀ i : Fin n, z * CliffordAlg.gamma i = CliffordAlg.gamma i * z) :
    IsCentral z := by
  apply CliffordAlg.ind_on (P := fun x => z * x = x * z)
  · intro c
    exact (CliffordAlg.ofScalar_central c z).symm
  · exact hcomm
  · intro x y hx hy
    rw [AssocRing.left_distrib, AssocRing.right_distrib, hx, hy]
  · intro x y hx hy
    rw [← AssocRing.mul_assoc z x y, hx, AssocRing.mul_assoc x z y,
        hy, ← AssocRing.mul_assoc x y z]

theorem self_eq_neg_eq_zero {a : F} (h : a = -a) : a = 0 := by
  have h2 : (1 + 1) * a = 0 := by
    rw [AssocRing.right_distrib, AssocRing.one_mul]
    calc
      a + a = a + -a := congrArg (fun t => a + t) h
      _ = 0 := add_neg_cancel_right_ring a
  cases mul_eq_zero_field h2 with
  | inl ht => exact False.elim (two_ne_zero_field ht)
  | inr ha => exact ha

end CliffordTools

/-! ### Separation Witness 1: Conformal Signature Pair `(1, 0)` vs `(0, 1)` (`n = 3`) -/

section OddConformalSeparation

variable {F : Type u} [FormallyRealField F]

/-- Base signature `(1, 0)` on `F¹`. -/
def sig10 : Sig 1 := fun _ => .pos

/-- Conformal model 1: Euclidean line `(1, 0)` in ambient conformal signature `(2, 1)`. -/
def confModel10 : ConformalModel F 1 := stdConformalModel sig10

/-- Conformal model 2: Negative-definite line `(0, 1)` in ambient conformal signature `(1, 2)`. -/
def confModel01 : ConformalModel F 1 := dualConformalModel sig10

theorem confModel10_signatures :
    signatureCount (confModel10 (F := F)).baseSig = (1, 0) ∧
    signatureCount (confModel10 (F := F)).ambSig = (2, 1) := ⟨rfl, rfl⟩

theorem confModel01_signatures :
    signatureCount (confModel01 (F := F)).baseSig = (0, 1) ∧
    signatureCount (confModel01 (F := F)).ambSig = (1, 2) := ⟨rfl, rfl⟩

private def idx3_0 : Fin 3 := ⟨0, by decide⟩
private def idx3_1 : Fin 3 := ⟨1, by decide⟩
private def idx3_2 : Fin 3 := ⟨2, by decide⟩

/-- Volume / pseudoscalar element `ω = γ₀ γ₁ γ₂` in 3D Clifford algebras. -/
def pseudoscalar3 (q : Fin 3 → F) : CliffordAlg F 3 q :=
  CliffordAlg.gamma idx3_0 * CliffordAlg.gamma idx3_1 * CliffordAlg.gamma idx3_2

theorem pseudoscalar3_central (q : Fin 3 → F) : IsCentral (pseudoscalar3 q) := by
  apply central_of_comm_gamma
  intro i
  let g0 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_0
  let g1 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_1
  let g2 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_2
  have a01 : g0 * g1 = -(g1 * g0) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_0 ≠ idx3_1))
  have a10 : g1 * g0 = -(g0 * g1) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_1 ≠ idx3_0))
  have a02 : g0 * g2 = -(g2 * g0) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_0 ≠ idx3_2))
  have a20 : g2 * g0 = -(g0 * g2) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_2 ≠ idx3_0))
  have a12 : g1 * g2 = -(g2 * g1) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_1 ≠ idx3_2))
  have a21 : g2 * g1 = -(g1 * g2) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_2 ≠ idx3_1))
  match i with
  | ⟨0, _⟩ =>
    show (g0 * g1 * g2) * g0 = g0 * (g0 * g1 * g2)
    calc
      (g0 * g1 * g2) * g0
          = (g0 * g1) * (g2 * g0) := AssocRing.mul_assoc (g0 * g1) g2 g0
      _ = -((g0 * g1) * (g0 * g2)) := by rw [a20, mul_neg_ring]
      _ = -(g0 * (g1 * g0) * g2) := by
            rw [← AssocRing.mul_assoc (g0 * g1) g0 g2, AssocRing.mul_assoc g0 g1 g0]
      _ = -(-(g0 * (g0 * g1)) * g2) := by rw [a10, mul_neg_ring]
      _ = g0 * (g0 * g1 * g2) := by
            rw [neg_mul_ring, neg_neg_ring, AssocRing.mul_assoc g0 (g0 * g1) g2]
  | ⟨1, _⟩ =>
    show (g0 * g1 * g2) * g1 = g1 * (g0 * g1 * g2)
    calc
      (g0 * g1 * g2) * g1
          = g0 * (g1 * (g2 * g1)) := by
            rw [AssocRing.mul_assoc (g0 * g1) g2 g1, AssocRing.mul_assoc g0 g1 (g2 * g1)]
      _ = -(g0 * (g1 * (g1 * g2))) := by rw [a21, mul_neg_ring, mul_neg_ring]
      _ = -((g0 * g1) * (g1 * g2)) := by rw [← AssocRing.mul_assoc g0 g1 (g1 * g2)]
      _ = (g1 * g0) * (g1 * g2) := by rw [a01, neg_mul_ring, neg_neg_ring]
      _ = g1 * (g0 * g1 * g2) := by
            rw [AssocRing.mul_assoc g1 g0 (g1 * g2), ← AssocRing.mul_assoc g0 g1 g2]
  | ⟨2, _⟩ =>
    show (g0 * g1 * g2) * g2 = g2 * (g0 * g1 * g2)
    have comm2 : (g0 * g1) * g2 = g2 * (g0 * g1) := by
      calc
        (g0 * g1) * g2 = g0 * (g1 * g2) := AssocRing.mul_assoc g0 g1 g2
        _ = -(g0 * (g2 * g1)) := by rw [a12, mul_neg_ring]
        _ = -((g0 * g2) * g1) := by rw [← AssocRing.mul_assoc g0 g2 g1]
        _ = g2 * (g0 * g1) := by
              rw [a02, neg_mul_ring, neg_neg_ring, AssocRing.mul_assoc g2 g0 g1]
    calc
      (g0 * g1 * g2) * g2 = (g2 * (g0 * g1)) * g2 := congrArg (fun t => t * g2) comm2
      _ = g2 * (g0 * g1 * g2) := AssocRing.mul_assoc g2 (g0 * g1) g2

theorem pseudoscalar3_sq (q : Fin 3 → F) :
    pseudoscalar3 q * pseudoscalar3 q =
      CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1 * q idx3_2)) := by
  let g0 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_0
  let g1 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_1
  let g2 : CliffordAlg F 3 q := CliffordAlg.gamma idx3_2
  have a10 : g1 * g0 = -(g0 * g1) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_1 ≠ idx3_0))
  have a02 : g0 * g2 = -(g2 * g0) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_0 ≠ idx3_2))
  have a12 : g1 * g2 = -(g2 * g1) :=
    anticomm_swap (CliffordAlg.gamma_anticomm q (by decide : idx3_1 ≠ idx3_2))
  have comm2 : (g0 * g1) * g2 = g2 * (g0 * g1) := by
    calc
      (g0 * g1) * g2 = g0 * (g1 * g2) := AssocRing.mul_assoc g0 g1 g2
      _ = -(g0 * (g2 * g1)) := by rw [a12, mul_neg_ring]
      _ = -((g0 * g2) * g1) := by rw [← AssocRing.mul_assoc g0 g2 g1]
      _ = g2 * (g0 * g1) := by
            rw [a02, neg_mul_ring, neg_neg_ring, AssocRing.mul_assoc g2 g0 g1]
  have neg_one_mul_ofScalar_helper :
      -(CliffordAlg.ofScalar (q idx3_0 * q idx3_1) : CliffordAlg F 3 q) =
      CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1)) := by
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_neg, CliffordAlg.raw_ofScalar, CliffordAlg.raw_ofScalar]
    exact (clNeg_scale _ _).symm
  have sq01 : (g0 * g1) * (g0 * g1) = CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1)) := by
    calc
      (g0 * g1) * (g0 * g1)
          = g0 * ((g1 * g0) * g1) := by
            rw [AssocRing.mul_assoc g0 g1 (g0 * g1), ← AssocRing.mul_assoc g1 g0 g1]
      _ = -((g0 * g0) * (g1 * g1)) := by
            rw [a10, neg_mul_ring, mul_neg_ring,
                ← AssocRing.mul_assoc g0 (g0 * g1) g1,
                ← AssocRing.mul_assoc g0 g0 g1,
                AssocRing.mul_assoc (g0 * g0) g1 g1]
      _ = -(CliffordAlg.ofScalar (q idx3_0) * CliffordAlg.ofScalar (q idx3_1)) := by
            rw [CliffordAlg.gamma_sq, CliffordAlg.gamma_sq]
      _ = CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1)) := by
            rw [← CliffordAlg.ofScalar_mul, neg_one_mul_ofScalar_helper]
  show (g0 * g1 * g2) * (g0 * g1 * g2) = _
  calc
    (g0 * g1 * g2) * (g0 * g1 * g2)
        = (g0 * g1) * (g2 * ((g0 * g1) * g2)) := by
          rw [AssocRing.mul_assoc (g0 * g1) g2 _]
    _ = (g0 * g1) * ((g0 * g1) * (g2 * g2)) := by
          rw [← AssocRing.mul_assoc g2 (g0 * g1) g2, ← comm2,
              AssocRing.mul_assoc (g0 * g1) g2 g2]
    _ = ((g0 * g1) * (g0 * g1)) * (g2 * g2) :=
          (AssocRing.mul_assoc (g0 * g1) (g0 * g1) (g2 * g2)).symm
    _ = CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1)) * CliffordAlg.ofScalar (q idx3_2) := by
          rw [sq01, CliffordAlg.gamma_sq]
    _ = CliffordAlg.ofScalar (-(q idx3_0 * q idx3_1 * q idx3_2)) := by
          rw [← CliffordAlg.ofScalar_mul, neg_mul_ring]

theorem pseudoscalar3_raw (q : Fin 3 → F) :
    (pseudoscalar3 q).raw = (((0, 0), (0, 0)), ((0, 0), (0, -1))) := by
  unfold pseudoscalar3
  rw [CliffordAlg.raw_mul, CliffordAlg.raw_mul]
  have g0_eq : (CliffordAlg.gamma idx3_0 : CliffordAlg F 3 q).raw =
      (((0, 1), (0, 0)), clZero 2) := rfl
  have g1_eq : (CliffordAlg.gamma idx3_1 : CliffordAlg F 3 q).raw =
      (((0, 0), (1, 0)), clZero 2) := rfl
  have g2_eq : (CliffordAlg.gamma idx3_2 : CliffordAlg F 3 q).raw =
      (clZero 2, clOne 2) := CliffordAlg.clGamma_last 2
  rw [g0_eq, g1_eq, g2_eq]
  have h01 : clMul q (((0, 1), (0, 0)), clZero 2) (((0, 0), (1, 0)), clZero 2) =
      (((0, 0), (0, -1)), clZero 2) := by
    rw [clMul_succ]
    apply Prod.ext
    · dsimp only
      rw [clMul_zero_right, clScale_zero, clAdd_zero]
      rw [clMul_succ (m := 1), clInvol_succ (m := 0), clInvol_succ (m := 0),
          clMul_succ (m := 0), clMul_succ (m := 0),
          clMul_succ (m := 0), clMul_succ (m := 0),
          clScale_succ (m := 0), clAdd_succ (m := 0), clAdd_succ (m := 0)]
      dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                   AssocRing.one_mul, AssocRing.mul_one, neg_zero_ring, neg_mul_ring,
                   mul_neg_ring, neg_neg_ring]
    · dsimp only
      rw [clMul_zero_right, clMul_zero_left, clAdd_zero]
  rw [h01, clMul_succ]
  apply Prod.ext
  · dsimp only
    rw [clMul_zero_right, clInvol_zero, clMul_zero_left, clScale_zero, clAdd_zero]
    rfl
  · dsimp only
    rw [clMul_one, clMul_zero_right, clAdd_zero,
        clInvol_succ (m := 1), clInvol_succ (m := 0), clInvol_succ (m := 0),
        clNeg_succ (m := 0)]
    dsimp only [clInvol, clNeg]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [neg_zero_ring, neg_neg_ring]

/-- Model 1 (`Cl_{2,1}(F)`) has both a nontrivial central involution and a nontrivial central idempotent! -/
theorem cl21_has_nontrivial_central_spectra :
    HasNontrivialCentralInvolution
      (CliffordAlg F 3 (Sig.toVec (confModel10 (F := F)).ambSig)) ∧
    HasNontrivialCentralIdem
      (CliffordAlg F 3 (Sig.toVec (confModel10 (F := F)).ambSig)) := by
  let q21 : Fin 3 → F := Sig.toVec (confModel10 (F := F)).ambSig
  let ω : CliffordAlg F 3 q21 := pseudoscalar3 q21
  have hq0 : q21 idx3_0 = 1 := rfl
  have hq1 : q21 idx3_1 = 1 := rfl
  have hq2 : q21 idx3_2 = -1 := rfl
  have hωC : IsCentral ω := pseudoscalar3_central q21
  have hω2 : ω * ω = 1 := by
    rw [pseudoscalar3_sq, hq0, hq1, hq2, AssocRing.one_mul, AssocRing.one_mul,
        neg_neg_ring, CliffordAlg.ofScalar_one]
  have hsc_ω : CliffordAlg.scalarPart ω.raw = 0 := by
    rw [pseudoscalar3_raw]; rfl
  have hω_ne_1 : ω ≠ 1 := by
    intro h
    have hs := congrArg (fun x : CliffordAlg F 3 q21 => CliffordAlg.scalarPart x.raw) h
    dsimp only at hs
    rw [hsc_ω] at hs
    exact one_ne_zero_field hs.symm
  have hω_ne_neg1 : ω ≠ -1 := by
    intro h
    have hs := congrArg (fun x : CliffordAlg F 3 q21 => CliffordAlg.scalarPart x.raw) h
    dsimp only at hs
    rw [hsc_ω] at hs
    change (0 : F) = -1 at hs
    have h1 : (1 : F) = 0 := by
      rw [← neg_neg_ring (1 : F), ← hs, neg_zero_ring]
    exact one_ne_zero_field h1
  refine ⟨⟨ω, hωC, hω2, hω_ne_1, hω_ne_neg1⟩, ?_⟩
  -- Construct e_+ = (1/2) * (1 + ω)
  let h : CliffordAlg F 3 q21 := CliffordAlg.ofScalar (halfField F)
  let e : CliffordAlg F 3 q21 := h * (1 + ω)
  have heC : IsCentral e := by
    intro x
    have hc1 : (1 + ω) * x = x * (1 + ω) := by
      rw [AssocRing.right_distrib, AssocRing.left_distrib,
          AssocRing.one_mul, AssocRing.mul_one, hωC x]
    calc
      (h * (1 + ω)) * x = h * ((1 + ω) * x) := AssocRing.mul_assoc h (1 + ω) x
      _ = h * (x * (1 + ω)) := by rw [hc1]
      _ = (x * h) * (1 + ω) := by
            rw [← AssocRing.mul_assoc h x (1 + ω), CliffordAlg.ofScalar_central (halfField F) x]
      _ = x * (h * (1 + ω)) := AssocRing.mul_assoc x h (1 + ω)
  have heI : e * e = e := by
    have sq1ω : (1 + ω) * (1 + ω) = CliffordAlg.ofScalar (1 + 1) * (1 + ω) := by
      rw [CliffordAlg.ofScalar_add, CliffordAlg.ofScalar_one]
      calc
        (1 + ω) * (1 + ω) = 1 * (1 + ω) + ω * (1 + ω) := AssocRing.right_distrib 1 ω (1 + ω)
        _ = (1 + ω) + (ω * 1 + ω * ω) := by rw [AssocRing.one_mul, AssocRing.left_distrib]
        _ = (1 + ω) + (1 + ω) := by rw [AssocRing.mul_one, hω2, AssocRing.add_comm ω 1]
        _ = 1 * (1 + ω) + 1 * (1 + ω) := by rw [AssocRing.one_mul]
        _ = (1 + 1) * (1 + ω) := (AssocRing.right_distrib 1 1 (1 + ω)).symm
    calc
      (h * (1 + ω)) * (h * (1 + ω))
          = h * (((1 + ω) * h) * (1 + ω)) := by
            rw [AssocRing.mul_assoc h (1 + ω) (h * (1 + ω)),
                ← AssocRing.mul_assoc (1 + ω) h (1 + ω)]
      _ = (h * h) * ((1 + ω) * (1 + ω)) := by
            rw [← CliffordAlg.ofScalar_central (halfField F) (1 + ω),
                AssocRing.mul_assoc h (1 + ω) (1 + ω),
                ← AssocRing.mul_assoc h h _]
      _ = (h * (h * CliffordAlg.ofScalar (1 + 1))) * (1 + ω) := by
            rw [sq1ω, ← AssocRing.mul_assoc (h * h) _ (1 + ω),
                AssocRing.mul_assoc h h _]
      _ = e := by
            have hh2 : h * CliffordAlg.ofScalar (1 + 1) = 1 := by
              rw [← CliffordAlg.ofScalar_mul, half_mul_two_field, CliffordAlg.ofScalar_one]
            rw [hh2, AssocRing.mul_one]
  have hsc_e : CliffordAlg.scalarPart e.raw = halfField F := by
    show CliffordAlg.scalarPart (CliffordAlg.ofScalar (halfField F) * (1 + ω)).raw = halfField F
    rw [CliffordAlg.ofScalar_mul_eq_smul, CliffordAlg.raw_smul, CliffordAlg.scalarPart_scale,
        CliffordAlg.raw_add, CliffordAlg.raw_one, CliffordAlg.scalarPart_add,
        CliffordAlg.scalarPart_one, hsc_ω, AssocRing.add_zero, AssocRing.mul_one]
  have he_ne_0 : e ≠ 0 := by
    intro h0
    have hs := congrArg (fun x : CliffordAlg F 3 q21 => CliffordAlg.scalarPart x.raw) h0
    dsimp only at hs
    rw [hsc_e] at hs
    exact half_ne_zero_field hs
  have he_ne_1 : e ≠ 1 := by
    intro h1
    have hs := congrArg (fun x : CliffordAlg F 3 q21 => CliffordAlg.scalarPart x.raw) h1
    dsimp only at hs
    rw [hsc_e] at hs
    change halfField F = 1 at hs
    have htwo : (1 : F) + 1 = 1 := by
      calc
        (1 : F) + 1 = halfField F + halfField F := by rw [hs]
        _ = 1 := half_add_half_field
    have hz : (1 : F) = 0 := add_left_cancel_ring (a := (1 : F)) (by rw [htwo, AssocRing.add_zero])
    exact one_ne_zero_field hz
  exact ⟨e, ⟨heC, heI⟩, he_ne_0, he_ne_1⟩

/-- Complete Center Characterization of `Cl(3, q)` for unit signatures `s : Sig 3`:
    every central element equals `ofScalar a + ofScalar b * pseudoscalar3`! -/
theorem center_cl3_decomp (s : Sig 3) (z : CliffordAlg F 3 (Sig.toVec s))
    (hz : IsCentral z) :
    ∃ a b : F,
      z = CliffordAlg.ofScalar a + CliffordAlg.ofScalar b * pseudoscalar3 (Sig.toVec s) := by
  let q : Fin 3 → F := Sig.toVec s
  rcases z with ⟨⟨⟨⟨x00, x01⟩, ⟨x10, x11⟩⟩, ⟨⟨y00, y01⟩, ⟨y10, y11⟩⟩⟩⟩
  -- Step 1: Commuting with γ₂ = (0, 1) forces clInvol x = x and clInvol y = y
  have hc2 := congrArg CliffordAlg.raw (hz (CliffordAlg.gamma idx3_2))
  have g2_eq : (CliffordAlg.gamma idx3_2 : CliffordAlg F 3 q).raw = (clZero 2, clOne 2) :=
    CliffordAlg.clGamma_last 2
  rw [CliffordAlg.raw_mul, CliffordAlg.raw_mul, g2_eq] at hc2
  dsimp only at hc2
  have lhs2 : clMul q (((x00, x01), (x10, x11)), ((y00, y01), (y10, y11))) (clZero 2, clOne 2) =
      (clScale (q (finLast 2)) (clInvol (n := 2) ((y00, y01), (y10, y11))),
       clInvol (n := 2) ((x00, x01), (x10, x11))) := by
    rw [clMul_succ, clMul_zero_right, clZero_add, clMul_one, clMul_one, clMul_zero_right, clAdd_zero]
  have rhs2 : clMul q (clZero 2, clOne 2) (((x00, x01), (x10, x11)), ((y00, y01), (y10, y11))) =
      (clScale (q (finLast 2)) ((y00, y01), (y10, y11)), ((x00, x01), (x10, x11))) := by
    rw [clMul_succ, clMul_zero_left, clZero_add, clInvol_one, clOne_mul,
        clInvol_zero, clMul_zero_left, clZero_add, clOne_mul]
  rw [lhs2, rhs2] at hc2
  have hx_inv : clInvol (F := F) (n := 2) ((x00, x01), (x10, x11)) = ((x00, x01), (x10, x11)) :=
    congrArg Prod.snd hc2
  have hx01 : x01 = 0 := self_eq_neg_eq_zero (congrArg (fun p => p.1.2) hx_inv).symm
  have hx10 : x10 = 0 := self_eq_neg_eq_zero (congrArg (fun p => p.2.1) hx_inv).symm
  subst hx01; subst hx10
  have hy_inv : clInvol (F := F) (n := 2) ((y00, y01), (y10, y11)) = ((y00, y01), (y10, y11)) := by
    have p1 := congrArg Prod.fst hc2
    dsimp only at p1
    have p1s := congrArg (clScale (q (finLast 2))) p1
    have hsq2 : q (finLast 2) * q (finLast 2) = 1 := Sign.toScalar_sq (s (finLast 2))
    rw [clScale_scale, clScale_scale, hsq2, clOne_scale, clOne_scale] at p1s
    exact p1s
  have hy01 : y01 = 0 := self_eq_neg_eq_zero (congrArg (fun p => p.1.2) hy_inv).symm
  have hy10 : y10 = 0 := self_eq_neg_eq_zero (congrArg (fun p => p.2.1) hy_inv).symm
  subst hy01; subst hy10
  -- Step 2: Commuting with γ₀ = (((0, 1), (0, 0)), 0) forces x11 = 0 and y00 = 0!
  have hc0 := congrArg CliffordAlg.raw (hz (CliffordAlg.gamma idx3_0))
  have g0_eq : (CliffordAlg.gamma idx3_0 : CliffordAlg F 3 q).raw =
      (((0, 1), (0, 0)), ((0, 0), (0, 0))) := rfl
  rw [CliffordAlg.raw_mul, CliffordAlg.raw_mul, g0_eq] at hc0
  dsimp only at hc0
  have hx11 : x11 = 0 := by
    have p := congrArg (fun t => t.1.2.1) hc0
    repeat rw [clMul_succ] at p
    repeat rw [clInvol_succ] at p
    repeat rw [clNeg_succ] at p
    repeat rw [clScale_succ] at p
    repeat rw [clAdd_succ] at p
    dsimp only [clMul, clInvol, clNeg, clScale, clAdd] at p
    simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
               AssocRing.one_mul, AssocRing.mul_one, neg_zero_ring, mul_neg_ring,
               neg_mul_ring, neg_neg_ring] at p
    have h0 := self_eq_neg_eq_zero p
    cases mul_eq_zero_field h0 with
    | inl hq =>
      have hsq : (s.toVec (finCastSucc (finCastSucc (finLast 0))) : F) *
                 s.toVec (finCastSucc (finCastSucc (finLast 0))) = 1 :=
        Sign.toScalar_sq _
      rw [hq, zero_mul_ring] at hsq
      exact False.elim (one_ne_zero_field hsq.symm)
    | inr hx => exact hx
  have hy00 : y00 = 0 := by
    have p := congrArg (fun t => t.2.1.2) hc0
    repeat rw [clMul_succ] at p
    repeat rw [clInvol_succ] at p
    repeat rw [clNeg_succ] at p
    repeat rw [clScale_succ] at p
    repeat rw [clAdd_succ] at p
    dsimp only [clMul, clInvol, clNeg, clScale, clAdd] at p
    simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
               AssocRing.one_mul, AssocRing.mul_one, neg_zero_ring, mul_neg_ring,
               neg_mul_ring, neg_neg_ring] at p
    exact self_eq_neg_eq_zero p
  subst hx11; subst hy00
  -- Now z = ⟨(((x00, 0), (0, 0)), ((0, 0), (0, y11)))⟩ = ofScalar x00 + ofScalar (-y11) * ω!
  refine ⟨x00, -y11, ?_⟩
  apply CliffordAlg.ext
  rw [CliffordAlg.raw_add, CliffordAlg.raw_ofScalar, CliffordAlg.raw_mul,
      CliffordAlg.raw_ofScalar, clMul_scale_left, clOne_mul, pseudoscalar3_raw]
  repeat rw [clOne_succ]
  repeat rw [clZero_succ]
  repeat rw [clScale_succ]
  repeat rw [clAdd_succ]
  dsimp only [clOne, clZero, clScale, clAdd]
  apply Prod.ext <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [mul_zero_ring, AssocRing.mul_one, AssocRing.add_zero, AssocRing.zero_add,
               neg_mul_neg_ring]

/-- Model 2 (`Cl_{1,2}(F)`) has NO nontrivial central idempotent and NO nontrivial central involution! -/
theorem cl12_no_nontrivial_central_spectra :
    ¬ HasNontrivialCentralInvolution
        (CliffordAlg F 3 (Sig.toVec (confModel01 (F := F)).ambSig)) ∧
    ¬ HasNontrivialCentralIdem
        (CliffordAlg F 3 (Sig.toVec (confModel01 (F := F)).ambSig)) := by
  let q12 : Fin 3 → F := Sig.toVec (confModel01 (F := F)).ambSig
  let ω : CliffordAlg F 3 q12 := pseudoscalar3 q12
  have hω2 : ω * ω = -(1 : CliffordAlg F 3 q12) := by
    have hq0 : q12 idx3_0 = -1 := rfl
    have hq1 : q12 idx3_1 = -1 := rfl
    have hq2 : q12 idx3_2 = 1 := rfl
    rw [pseudoscalar3_sq, hq0, hq1, hq2, neg_mul_neg_ring, AssocRing.one_mul, AssocRing.mul_one]
    apply CliffordAlg.ext
    show clScale (-1) (clOne 3) = clNeg (clOne 3)
    rw [clNeg_scale, clOne_scale]
  -- Helper computing (ofScalar a + ofScalar b * ω)^2
  have sq_ab : ∀ a b : F,
      (CliffordAlg.ofScalar a + CliffordAlg.ofScalar b * ω) *
      (CliffordAlg.ofScalar a + CliffordAlg.ofScalar b * ω) =
      CliffordAlg.ofScalar (a * a - b * b) +
      CliffordAlg.ofScalar ((1 + 1) * a * b) * ω := by
    intro a b
    let sa : CliffordAlg F 3 q12 := CliffordAlg.ofScalar a
    let sb : CliffordAlg F 3 q12 := CliffordAlg.ofScalar b
    have t_aa : sa * sa = CliffordAlg.ofScalar (a * a) := (CliffordAlg.ofScalar_mul a a).symm
    have t_ab : sa * (sb * ω) = CliffordAlg.ofScalar (a * b) * ω := by
      rw [← AssocRing.mul_assoc, ← CliffordAlg.ofScalar_mul]
    have t_ba : (sb * ω) * sa = CliffordAlg.ofScalar (a * b) * ω := by
      rw [AssocRing.mul_assoc sb ω sa, ← CliffordAlg.ofScalar_central a ω,
          ← AssocRing.mul_assoc sb sa ω, ← CliffordAlg.ofScalar_mul,
          FormallyRealField.mul_comm b a]
    have t_bb : (sb * ω) * (sb * ω) = CliffordAlg.ofScalar (-(b * b)) := by
      calc
        (sb * ω) * (sb * ω)
            = sb * ((ω * sb) * ω) := by
              rw [AssocRing.mul_assoc sb ω (sb * ω), ← AssocRing.mul_assoc ω sb ω]
        _ = (sb * sb) * (ω * ω) := by
              rw [← CliffordAlg.ofScalar_central b ω,
                  AssocRing.mul_assoc sb ω ω, ← AssocRing.mul_assoc sb sb _]
        _ = -(CliffordAlg.ofScalar (b * b)) := by
              rw [← CliffordAlg.ofScalar_mul, hω2, mul_neg_ring, AssocRing.mul_one]
        _ = CliffordAlg.ofScalar (-(b * b)) := by
              apply CliffordAlg.ext
              show clNeg (clScale (b * b) (clOne 3)) = clScale (-(b * b)) (clOne 3)
              exact (clNeg_scale _ _).symm
    rw [AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib,
        t_aa, t_ab, t_ba, t_bb]
    have sum2 : CliffordAlg.ofScalar (a * b) * ω + CliffordAlg.ofScalar (a * b) * ω =
        CliffordAlg.ofScalar ((1 + 1) * a * b) * ω := by
      rw [AssocRing.mul_assoc (1 + 1) a b, CliffordAlg.ofScalar_mul (1 + 1) (a * b),
          CliffordAlg.ofScalar_add, CliffordAlg.ofScalar_one,
          AssocRing.right_distrib (1 : CliffordAlg F 3 q12) 1 _, AssocRing.one_mul,
          AssocRing.right_distrib]
    -- Rearrange (sa2 + abω) + (abω + (-sb2)) = (sa2 - sb2) + 2abω
    rw [AssocRing.add_assoc (CliffordAlg.ofScalar (a * a)) _ _,
        ← AssocRing.add_assoc (CliffordAlg.ofScalar (a * b) * ω) _ _,
        sum2,
        AssocRing.add_comm (CliffordAlg.ofScalar ((1 + 1) * a * b) * ω) _,
        ← AssocRing.add_assoc,
        ← CliffordAlg.ofScalar_add, ← AssocRing.sub_eq_add_neg]
  have coord_ab : ∀ a1 b1 a2 b2 : F,
      (CliffordAlg.ofScalar a1 + CliffordAlg.ofScalar b1 * ω : CliffordAlg F 3 q12) =
      CliffordAlg.ofScalar a2 + CliffordAlg.ofScalar b2 * ω →
      a1 = a2 ∧ b1 = b2 := by
    intro a1 b1 a2 b2 heq
    have hr := congrArg CliffordAlg.raw heq
    have raw_form0 : ∀ a b : F,
        ((CliffordAlg.ofScalar a + CliffordAlg.ofScalar b * ω : CliffordAlg F 3 q12).raw).1.1.1 = a := by
      intro a b
      rw [CliffordAlg.raw_add, CliffordAlg.raw_ofScalar, CliffordAlg.raw_mul,
          CliffordAlg.raw_ofScalar, clMul_scale_left, clOne_mul, pseudoscalar3_raw]
      show a * 1 + b * 0 = a
      rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero]
    have raw_form7 : ∀ a b : F,
        ((CliffordAlg.ofScalar a + CliffordAlg.ofScalar b * ω : CliffordAlg F 3 q12).raw).2.2.2 = -b := by
      intro a b
      rw [CliffordAlg.raw_add, CliffordAlg.raw_ofScalar, CliffordAlg.raw_mul,
          CliffordAlg.raw_ofScalar, clMul_scale_left, clOne_mul, pseudoscalar3_raw]
      show a * 0 + b * -1 = -b
      rw [mul_zero_ring, AssocRing.zero_add, mul_neg_ring, AssocRing.mul_one]
    have hs : a1 = a2 := by
      have p0 := congrArg (fun t : CliffordCarrier F 3 => t.1.1.1) hr
      dsimp only at p0
      rw [raw_form0 a1 b1, raw_form0 a2 b2] at p0
      exact p0
    have hb : b1 = b2 := by
      have p2 := congrArg (fun t : CliffordCarrier F 3 => t.2.2.2) hr
      dsimp only at p2
      rw [raw_form7 a1 b1, raw_form7 a2 b2] at p2
      rw [← neg_neg_ring b1, p2, neg_neg_ring]
    exact ⟨hs, hb⟩
  refine ⟨?_, ?_⟩
  · -- No nontrivial central involution
    rintro ⟨z, hzC, hz2, hz1, hzn1⟩
    rcases center_cl3_decomp (confModel01 (F := F)).ambSig z hzC with ⟨a, b, rfl⟩
    rw [sq_ab a b] at hz2
    have h1_form : (1 : CliffordAlg F 3 q12) =
        CliffordAlg.ofScalar 1 + CliffordAlg.ofScalar 0 * ω := by
      rw [CliffordAlg.ofScalar_one, CliffordAlg.ofScalar_zero, zero_mul_ring, AssocRing.add_zero]
    rw [h1_form] at hz2
    rcases coord_ab _ _ _ _ hz2 with ⟨hre, him⟩
    rw [AssocRing.mul_assoc (1 + 1) a b] at him
    cases mul_eq_zero_field him with
    | inl ht => exact False.elim (two_ne_zero_field ht)
    | inr hab =>
      cases mul_eq_zero_field hab with
      | inl ha0 =>
        rw [ha0, zero_mul_ring, AssocRing.sub_eq_add_neg, AssocRing.zero_add] at hre
        have h4 : b * b + 1 * 1 + 0 * 0 + 0 * 0 = 0 := by
          have hb1 : b * b + 1 = 0 := by
            rw [← hre, add_neg_cancel_right_ring]
          rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero, AssocRing.add_zero, hb1]
        exact one_ne_zero_field (FormallyRealField.sum_four_sq_eq_zero b 1 0 0 h4).2.1
      | inr hb0 =>
        subst hb0
        rw [CliffordAlg.ofScalar_zero, zero_mul_ring, AssocRing.add_zero] at hz1 hzn1
        rw [mul_zero_ring, AssocRing.sub_eq_add_neg, neg_zero_ring, AssocRing.add_zero] at hre
        have hprod : (a - 1) * (a + 1) = 0 := by
          rw [sub_mul_ring, AssocRing.left_distrib, AssocRing.one_mul, AssocRing.mul_one,
              hre, AssocRing.sub_eq_add_neg (1 + a), neg_add_distrib_ring,
              AssocRing.add_comm 1 a, AssocRing.add_assoc a 1 (-a + -1),
              ← AssocRing.add_assoc 1 (-a) (-1), AssocRing.add_comm 1 (-a),
              AssocRing.add_assoc (-a) 1 (-1), add_neg_cancel_right_ring,
              AssocRing.add_zero, add_neg_cancel_right_ring]
        cases mul_eq_zero_field hprod with
        | inl hm1 =>
          have ha1 : a = 1 := sub_eq_zero_iff_eq.mp hm1
          rw [ha1, CliffordAlg.ofScalar_one] at hz1
          exact hz1 rfl
        | inr hp1 =>
          have han1 : a = -1 := (neg_eq_of_add_eq_zero (by rw [AssocRing.add_comm]; exact hp1)).symm
          have hofn1 : (CliffordAlg.ofScalar (-1) : CliffordAlg F 3 q12) = -1 := by
            apply CliffordAlg.ext
            show clScale (-1) (clOne 3) = clNeg (clOne 3)
            rw [clNeg_scale, clOne_scale]
          rw [han1, hofn1] at hzn1
          exact hzn1 rfl
  · -- No nontrivial central idempotent
    rintro ⟨z, ⟨hzC, hzI⟩, hz0, hz1⟩
    rcases center_cl3_decomp (confModel01 (F := F)).ambSig z hzC with ⟨a, b, rfl⟩
    have hzI' := hzI
    rw [sq_ab a b] at hzI'
    rcases coord_ab _ _ _ _ hzI' with ⟨hre, him⟩
    by_cases hb0 : b = 0
    · subst hb0
      rw [CliffordAlg.ofScalar_zero, zero_mul_ring, AssocRing.add_zero] at hz0 hz1
      rw [mul_zero_ring, AssocRing.sub_eq_add_neg, neg_zero_ring, AssocRing.add_zero] at hre
      have hprod : a * (a - 1) = 0 := by
        rw [mul_sub_ring, AssocRing.mul_one, hre, sub_self_ring]
      cases mul_eq_zero_field hprod with
      | inl ha0 =>
        rw [ha0, CliffordAlg.ofScalar_zero] at hz0
        exact hz0 rfl
      | inr ha1 =>
        rw [sub_eq_zero_iff_eq.mp ha1, CliffordAlg.ofScalar_one] at hz1
        exact hz1 rfl
    · -- b ≠ 0 => (1 + 1) * a = 1 => ((1 + 1)*b)^2 + 1 = 0, impossible!
      have h2a : (1 + 1) * a = 1 := by
        have hsub : ((1 + 1) * a - 1) * b = 0 := by
          rw [sub_mul_ring, AssocRing.one_mul, him, sub_self_ring]
        cases mul_eq_zero_field hsub with
        | inl h => exact sub_eq_zero_iff_eq.mp h
        | inr hb => exact False.elim (hb0 hb)
      -- Multiply a*a - b*b = a by (1+1)*(1+1)
      let t : F := 1 + 1
      have hmul4 : (t * a) * (t * a) - (t * b) * (t * b) = t * (t * a) := by
        have sq_ta : ∀ x : F, (t * x) * (t * x) = (t * t) * (x * x) := by
          intro x
          rw [AssocRing.mul_assoc t x (t * x), ← AssocRing.mul_assoc x t x,
              FormallyRealField.mul_comm x t, AssocRing.mul_assoc t x x,
              ← AssocRing.mul_assoc t t (x * x)]
        rw [sq_ta a, sq_ta b, ← mul_sub_ring, hre, AssocRing.mul_assoc]
      rw [h2a, AssocRing.mul_one, AssocRing.mul_one] at hmul4
      -- hmul4 : 1 - (t * b) * (t * b) = t
      have h4 : (t * b) * (t * b) + 1 * 1 + 0 * 0 + 0 * 0 = 0 := by
        have htb1 : (t * b) * (t * b) + 1 = 0 := by
          let s : F := (t * b) * (t * b)
          have h1 : (1 : F) = (1 + 1) + s := by
            have hadd : (1 - s) + s = t + s := congrArg (fun x => x + s) hmul4
            rw [AssocRing.sub_eq_add_neg, AssocRing.add_assoc (1 : F) (-s) s,
                AssocRing.neg_add_cancel, AssocRing.add_zero] at hadd
            exact hadd
          apply add_left_cancel_ring (a := (1 : F))
          calc
            (1 : F) + (s + 1) = (1 + 1) + s := by
              rw [AssocRing.add_comm s 1, ← AssocRing.add_assoc (1 : F) 1 s]
            _ = 1 := h1.symm
            _ = 1 + 0 := (AssocRing.add_zero 1).symm
        rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero, AssocRing.add_zero, htb1]
      exact one_ne_zero_field (FormallyRealField.sum_four_sq_eq_zero (t * b) 1 0 0 h4).2.1

/-- Genuine Unital Ring Non-Isomorphism: `Cl_{2,1}(F) ≇ Cl_{1,2}(F)`! -/
theorem clifford_21_not_iso_12 :
    ¬ Nonempty (RingIso
        (CliffordAlg F 3 (Sig.toVec (confModel10 (F := F)).ambSig))
        (CliffordAlg F 3 (Sig.toVec (confModel01 (F := F)).ambSig))) := by
  rintro ⟨e⟩
  exact (cl12_no_nontrivial_central_spectra (F := F)).2
    (e.preserve_centralIdem (cl21_has_nontrivial_central_spectra (F := F)).2)

end OddConformalSeparation

/-! ### Separation Witness 2: Lorentzian Conformal Pair `(2, 0)` vs `(0, 2)` (`n = 4`) -/

private theorem idem_pair_laws {A : Type u} [AssocRing A]
    (h : A) (hhC : IsCentral h) (h2 : h * (1 + 1) = 1)
    (u : A) (hu2 : u * u = 1) :
    let ep := h * (1 + u)
    let em := h * (1 - u)
    ep * ep = ep ∧ em * em = em ∧ ep * em = 0 ∧ em * ep = 0 := by
  intro ep em
  have squp_gen : ∀ v : A, v * v = 1 → (1 + v) * (1 + v) = (1 + 1) * (1 + v) := by
    intro v hv2
    calc
      (1 + v) * (1 + v) = 1 * (1 + v) + v * (1 + v) := AssocRing.right_distrib 1 v (1 + v)
      _ = (1 + v) + (v * 1 + v * v) := by rw [AssocRing.one_mul, AssocRing.left_distrib]
      _ = (1 + v) + (1 + v) := by rw [AssocRing.mul_one, hv2, AssocRing.add_comm v 1]
      _ = 1 * (1 + v) + 1 * (1 + v) := by rw [AssocRing.one_mul]
      _ = (1 + 1) * (1 + v) := (AssocRing.right_distrib 1 1 (1 + v)).symm
  have squp : (1 + u) * (1 + u) = (1 + 1) * (1 + u) := squp_gen u hu2
  have squm : (1 - u) * (1 - u) = (1 + 1) * (1 - u) := by
    rw [AssocRing.sub_eq_add_neg (1 : A) u]
    exact squp_gen (-u) (by rw [neg_mul_neg_ring, hu2])
  have orth_pm : (1 + u) * (1 - u) = 0 := by
    calc
      (1 + u) * (1 - u) = (1 + u) * 1 - (1 + u) * u := mul_sub_ring (1 + u) 1 u
      _ = (1 + u) - (1 * u + u * u) := by rw [AssocRing.mul_one, AssocRing.right_distrib]
      _ = (1 + u) - (1 + u) := by rw [AssocRing.one_mul, hu2, AssocRing.add_comm u 1]
      _ = 0 := sub_self_ring (1 + u)
  have orth_mp : (1 - u) * (1 + u) = 0 := by
    calc
      (1 - u) * (1 + u) = (1 - u) * 1 + (1 - u) * u := AssocRing.left_distrib (1 - u) 1 u
      _ = (1 - u) + (1 * u - u * u) := by rw [AssocRing.mul_one, sub_mul_ring]
      _ = (1 + -u) + (u + -1) := by
            rw [AssocRing.one_mul, hu2, AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg]
      _ = 1 + ((-u + u) + -1) := by
            rw [AssocRing.add_assoc 1 (-u) (u + -1), AssocRing.add_assoc (-u) u (-1)]
      _ = 0 := by
            rw [AssocRing.neg_add_cancel, AssocRing.zero_add, add_neg_cancel_right_ring]
  have mul_h : ∀ x y : A, (h * x) * (h * y) = (h * h) * (x * y) := by
    intro x y
    rw [AssocRing.mul_assoc h x (h * y), ← AssocRing.mul_assoc x h y,
        ← hhC x, AssocRing.mul_assoc h x y, ← AssocRing.mul_assoc h h (x * y)]
  have hh_two : ∀ x : A, (h * h) * ((1 + 1) * x) = h * x := by
    intro x
    rw [← AssocRing.mul_assoc (h * h) (1 + 1) x,
        AssocRing.mul_assoc h h (1 + 1), h2, AssocRing.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (h * (1 + u)) * (h * (1 + u)) = h * (1 + u)
    rw [mul_h, squp, hh_two]
  · show (h * (1 - u)) * (h * (1 - u)) = h * (1 - u)
    rw [mul_h, squm, hh_two]
  · show (h * (1 + u)) * (h * (1 - u)) = 0
    rw [mul_h, orth_pm, mul_zero_ring]
  · show (h * (1 - u)) * (h * (1 + u)) = 0
    rw [mul_h, orth_mp, mul_zero_ring]

section EvenLorentzianSeparation

variable {F : Type u} [FormallyRealField F]

/-- Base signature `(2, 0)` on `F²`. -/
def sig20 : Sig 2 := fun _ => .pos

/-- Conformal model 1: Euclidean plane `(2, 0)` in East-Coast Lorentzian signature `(3, 1)`. -/
def confModel20 : ConformalModel F 2 := stdConformalModel sig20

/-- Conformal model 2: Negative-definite plane `(0, 2)` in West-Coast Lorentzian signature `(1, 3)`. -/
def confModel02 : ConformalModel F 2 := dualConformalModel sig20

theorem confModel20_signatures :
    signatureCount (confModel20 (F := F)).baseSig = (2, 0) ∧
    signatureCount (confModel20 (F := F)).ambSig = (3, 1) := ⟨rfl, rfl⟩

theorem confModel02_signatures :
    signatureCount (confModel02 (F := F)).baseSig = (0, 2) ∧
    signatureCount (confModel02 (F := F)).ambSig = (1, 3) := ⟨rfl, rfl⟩

/-! #### Part A: `Cl_{3,1}(F)` has 4 mutually orthogonal nonzero idempotents -/

private def idx4_0 : Fin 4 := ⟨0, by decide⟩
private def idx4_1 : Fin 4 := ⟨1, by decide⟩
private def idx4_2 : Fin 4 := ⟨2, by decide⟩
private def idx4_3 : Fin 4 := ⟨3, by decide⟩

theorem cl31_has_four_orthogonal_idempotents :
    HasOrthogonalIdempotents
      (CliffordAlg F 4 (Sig.toVec (confModel20 (F := F)).ambSig)) 4 := by
  let q31 : Fin 4 → F := Sig.toVec (confModel20 (F := F)).ambSig
  let h : CliffordAlg F 4 q31 := CliffordAlg.ofScalar (halfField F)
  let α : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_0
  let β : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_1 * CliffordAlg.gamma idx4_3
  have hhC : IsCentral h := CliffordAlg.ofScalar_central (halfField F)
  have hh2 : h * (1 + 1) = 1 := by
    have h11 : (1 + 1 : CliffordAlg F 4 q31) = CliffordAlg.ofScalar (1 + 1) := by
      rw [CliffordAlg.ofScalar_add, CliffordAlg.ofScalar_one]
    rw [h11, ← CliffordAlg.ofScalar_mul, half_mul_two_field, CliffordAlg.ofScalar_one]
  have hα2 : α * α = 1 := by
    have hq0 : q31 idx4_0 = 1 := rfl
    rw [CliffordAlg.gamma_sq, hq0, CliffordAlg.ofScalar_one]
  have hβ2 : β * β = 1 := by
    let g1 : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_1
    let g3 : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_3
    have a31 : g3 * g1 = -(g1 * g3) :=
      anticomm_swap (CliffordAlg.gamma_anticomm q31 (by decide : idx4_3 ≠ idx4_1))
    show (g1 * g3) * (g1 * g3) = 1
    calc
      (g1 * g3) * (g1 * g3)
          = g1 * ((g3 * g1) * g3) := by
            rw [AssocRing.mul_assoc g1 g3 (g1 * g3), ← AssocRing.mul_assoc g3 g1 g3]
      _ = -((g1 * g1) * (g3 * g3)) := by
            rw [a31, neg_mul_ring, mul_neg_ring,
                ← AssocRing.mul_assoc g1 (g1 * g3) g3,
                ← AssocRing.mul_assoc g1 g1 g3,
                AssocRing.mul_assoc (g1 * g1) g3 g3]
      _ = -(CliffordAlg.ofScalar (q31 idx4_1) * CliffordAlg.ofScalar (q31 idx4_3)) := by
            rw [CliffordAlg.gamma_sq, CliffordAlg.gamma_sq]
      _ = 1 := by
            have hq1 : q31 idx4_1 = 1 := rfl
            have hq3 : q31 idx4_3 = -1 := rfl
            rw [hq1, hq3, ← CliffordAlg.ofScalar_mul, AssocRing.one_mul]
            apply CliffordAlg.ext
            show clNeg (clScale (-1) (clOne 4)) = clOne 4
            rw [clNeg_scale, clOne_scale, clNeg_neg]
  have hαβ : α * β = β * α := by
    let g0 : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_0
    let g1 : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_1
    let g3 : CliffordAlg F 4 q31 := CliffordAlg.gamma idx4_3
    have a01 : g0 * g1 = -(g1 * g0) :=
      anticomm_swap (CliffordAlg.gamma_anticomm q31 (by decide : idx4_0 ≠ idx4_1))
    have a03 : g0 * g3 = -(g3 * g0) :=
      anticomm_swap (CliffordAlg.gamma_anticomm q31 (by decide : idx4_0 ≠ idx4_3))
    show g0 * (g1 * g3) = (g1 * g3) * g0
    calc
      g0 * (g1 * g3) = (g0 * g1) * g3 := (AssocRing.mul_assoc g0 g1 g3).symm
      _ = -(g1 * (g0 * g3)) := by
            rw [a01, neg_mul_ring, AssocRing.mul_assoc g1 g0 g3]
      _ = (g1 * g3) * g0 := by
            rw [a03, mul_neg_ring, neg_neg_ring, ← AssocRing.mul_assoc g1 g3 g0]
  let up := h * (1 + α)
  let um := h * (1 - α)
  let vp := h * (1 + β)
  let vm := h * (1 - β)
  rcases idem_pair_laws h hhC hh2 α hα2 with ⟨hup2, hum2, hupm, hump⟩
  rcases idem_pair_laws h hhC hh2 β hβ2 with ⟨hvp2, hvm2, hvpm, hvmp⟩
  -- Commutativity of u_{±} with v_{±}
  have comm_1α_1β : ∀ (s1 s2 : F),
      (1 + CliffordAlg.ofScalar s1 * α) * (1 + CliffordAlg.ofScalar s2 * β) =
      (1 + CliffordAlg.ofScalar s2 * β) * (1 + CliffordAlg.ofScalar s1 * α) := by
    intro s1 s2
    let A1 := CliffordAlg.ofScalar s1 * α
    let B1 := CliffordAlg.ofScalar s2 * β
    have cAB : A1 * B1 = B1 * A1 := by
      calc
        (CliffordAlg.ofScalar s1 * α) * (CliffordAlg.ofScalar s2 * β)
            = CliffordAlg.ofScalar s1 * ((α * CliffordAlg.ofScalar s2) * β) := by
              rw [AssocRing.mul_assoc _ α _, ← AssocRing.mul_assoc α _ β]
        _ = (CliffordAlg.ofScalar s1 * CliffordAlg.ofScalar s2) * (α * β) := by
              rw [← CliffordAlg.ofScalar_central s2 α,
                  AssocRing.mul_assoc (CliffordAlg.ofScalar s2) α β,
                  ← AssocRing.mul_assoc (CliffordAlg.ofScalar s1) _ _]
        _ = (CliffordAlg.ofScalar s2 * CliffordAlg.ofScalar s1) * (β * α) := by
              rw [← CliffordAlg.ofScalar_mul, ← CliffordAlg.ofScalar_mul,
                  FormallyRealField.mul_comm s1 s2, hαβ]
        _ = (CliffordAlg.ofScalar s2 * β) * (CliffordAlg.ofScalar s1 * α) := by
              rw [AssocRing.mul_assoc (CliffordAlg.ofScalar s2) (CliffordAlg.ofScalar s1) (β * α),
                  ← AssocRing.mul_assoc (CliffordAlg.ofScalar s1) β α,
                  CliffordAlg.ofScalar_central s1 β,
                  AssocRing.mul_assoc β _ α,
                  ← AssocRing.mul_assoc (CliffordAlg.ofScalar s2) β _]
    show (1 + A1) * (1 + B1) = (1 + B1) * (1 + A1)
    calc
      (1 + A1) * (1 + B1)
          = 1 * (1 + B1) + A1 * (1 + B1) := AssocRing.right_distrib 1 A1 (1 + B1)
      _ = (1 + B1) + (A1 + A1 * B1) := by
            rw [AssocRing.one_mul, AssocRing.left_distrib, AssocRing.mul_one]
      _ = 1 + (B1 + A1) + B1 * A1 := by
            rw [cAB, ← AssocRing.add_assoc (1 + B1) A1 (B1 * A1),
                AssocRing.add_assoc 1 B1 A1]
      _ = 1 + (A1 + B1) + B1 * A1 := by rw [AssocRing.add_comm B1 A1]
      _ = (1 + A1) + (B1 + B1 * A1) := by
            rw [← AssocRing.add_assoc 1 A1 B1,
                AssocRing.add_assoc (1 + A1) B1 (B1 * A1)]
      _ = 1 * (1 + A1) + B1 * (1 + A1) := by
            rw [AssocRing.one_mul, AssocRing.left_distrib, AssocRing.mul_one]
      _ = (1 + B1) * (1 + A1) := (AssocRing.right_distrib 1 B1 (1 + A1)).symm
  have neg_as_ofScalar : ∀ x : CliffordAlg F 4 q31, 1 - x = 1 + CliffordAlg.ofScalar (-1) * x := by
    intro x
    rw [AssocRing.sub_eq_add_neg]
    apply congrArg (fun t => 1 + t)
    apply CliffordAlg.ext
    show clNeg x.raw = clMul q31 (clScale (-1) (clOne 4)) x.raw
    rw [clMul_scale_left, clOne_mul, clNeg_scale, clOne_scale]
  have one_as_ofScalar : ∀ x : CliffordAlg F 4 q31, 1 + x = 1 + CliffordAlg.ofScalar 1 * x := by
    intro x
    rw [CliffordAlg.ofScalar_one, AssocRing.one_mul]
  have comm_uv : ∀ u ∈ [up, um], ∀ v ∈ [vp, vm], u * v = v * u := by
    -- Prove explicit 4 commutators directly
    intro u hu v hv
    have comm_core : ∀ a b : CliffordAlg F 4 q31, a * b = b * a →
        (h * a) * (h * b) = (h * b) * (h * a) := by
      intro a b hab
      calc
        (h * a) * (h * b) = (h * h) * (a * b) := by
          rw [AssocRing.mul_assoc h a (h * b), ← AssocRing.mul_assoc a h b,
              ← hhC a, AssocRing.mul_assoc h a b, ← AssocRing.mul_assoc h h (a * b)]
        _ = (h * h) * (b * a) := by rw [hab]
        _ = (h * b) * (h * a) := by
          rw [AssocRing.mul_assoc h b (h * a), ← AssocRing.mul_assoc b h a,
              ← hhC b, AssocRing.mul_assoc h b a, ← AssocRing.mul_assoc h h (b * a)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · apply comm_core; rw [one_as_ofScalar α, one_as_ofScalar β]; exact comm_1α_1β 1 1
    · apply comm_core; rw [one_as_ofScalar α, neg_as_ofScalar β]; exact comm_1α_1β 1 (-1)
    · apply comm_core; rw [neg_as_ofScalar α, one_as_ofScalar β]; exact comm_1α_1β (-1) 1
    · apply comm_core; rw [neg_as_ofScalar α, neg_as_ofScalar β]; exact comm_1α_1β (-1) (-1)
  -- Define p : Fin 4 → CliffordAlg F 4 q31
  let p : Fin 4 → CliffordAlg F 4 q31 := fun i =>
    match i.val with
    | 0 => up * vp
    | 1 => up * vm
    | 2 => um * vp
    | _ => um * vm
  -- Check scalarPart of each p i equals halfField * halfField ≠ 0!
  have hhh_ne : halfField F * halfField F ≠ 0 := by
    intro h0
    cases mul_eq_zero_field h0 with
    | inl hh => exact half_ne_zero_field hh
    | inr hh => exact half_ne_zero_field hh
  have scalar_p : ∀ s1 s2 : F,
      CliffordAlg.scalarPart
        ((h * (1 + CliffordAlg.ofScalar s1 * α)) *
         (h * (1 + CliffordAlg.ofScalar s2 * β))).raw =
      halfField F * halfField F := by
    intro s1 s2
    let X : CliffordAlg F 4 q31 := 1 + CliffordAlg.ofScalar s1 * α
    let Y : CliffordAlg F 4 q31 := 1 + CliffordAlg.ofScalar s2 * β
    have hX_raw : X.raw = clAdd (clOne 4) (clScale s1 α.raw) := by
      show (1 + CliffordAlg.ofScalar s1 * α).raw = _
      rw [CliffordAlg.raw_add, CliffordAlg.raw_one, CliffordAlg.ofScalar_mul_eq_smul,
          CliffordAlg.raw_smul]
    have hY_raw : Y.raw = clAdd (clOne 4) (clScale s2 β.raw) := by
      show (1 + CliffordAlg.ofScalar s2 * β).raw = _
      rw [CliffordAlg.raw_add, CliffordAlg.raw_one, CliffordAlg.ofScalar_mul_eq_smul,
          CliffordAlg.raw_smul]
    have hα_snd : α.raw.2 = clZero 3 := rfl
    have hα_sc : CliffordAlg.scalarPart α.raw.1 = 0 := rfl
    have hX_snd : X.raw.2 = clZero 3 := by
      rw [hX_raw]
      rcases hαr : α.raw with ⟨a1, a2⟩
      have ha2 : a2 = clZero 3 := by rw [← hα_snd, hαr]
      rw [clOne_succ, clScale_succ, clAdd_succ]
      dsimp only
      rw [ha2, clScale_zero, clAdd_zero]
    have hX_sc : CliffordAlg.scalarPart X.raw.1 = 1 := by
      rw [hX_raw]
      rcases hαr : α.raw with ⟨a1, a2⟩
      have ha1_sc : CliffordAlg.scalarPart a1 = 0 := by rw [← hα_sc, hαr]
      rw [clOne_succ, clScale_succ, clAdd_succ]
      dsimp only
      rw [CliffordAlg.scalarPart_add, CliffordAlg.scalarPart_one,
          CliffordAlg.scalarPart_scale, ha1_sc, mul_zero_ring, AssocRing.add_zero]
    have hβ_fst : β.raw.1 = clZero 3 := by
      have hβ_r : β.raw = clMul q31 (CliffordAlg.clGamma idx4_1) (CliffordAlg.clGamma idx4_3) := rfl
      rw [hβ_r]
      rcases hg1 : (CliffordAlg.clGamma idx4_1 : CliffordCarrier F 4) with ⟨g1a, g1b⟩
      rcases hg3 : (CliffordAlg.clGamma idx4_3 : CliffordCarrier F 4) with ⟨g3a, g3b⟩
      have hg1b : g1b = clZero 3 := (congrArg Prod.snd hg1).symm
      have hg3a : g3a = clZero 3 := (congrArg Prod.fst hg3).symm
      rw [clMul_succ]
      dsimp only
      rw [hg3a, hg1b, clInvol_zero, clMul_zero_right, clMul_zero_left, clScale_zero, clAdd_zero]
    have hY_fst : Y.raw.1 = clOne 3 := by
      rw [hY_raw]
      rcases hβr : β.raw with ⟨b1, b2⟩
      have hb1 : b1 = clZero 3 := by rw [← hβ_fst, hβr]
      rw [clOne_succ, clScale_succ, clAdd_succ]
      dsimp only
      rw [hb1, clScale_zero, clAdd_zero]
    have hXY_fst : (X * Y).raw.1 = X.raw.1 := by
      rw [CliffordAlg.raw_mul]
      rcases hXr : X.raw with ⟨x1, x2⟩
      rcases hYr : Y.raw with ⟨y1, y2⟩
      have hx2 : x2 = clZero 3 := by rw [← hX_snd, hXr]
      have hy1 : y1 = clOne 3 := by rw [← hY_fst, hYr]
      rw [clMul_succ]
      dsimp only
      rw [hx2, hy1, clInvol_zero, clMul_zero_left, clScale_zero, clAdd_zero, clMul_one]
    have mul_h2 : (h * X) * (h * Y) =
        CliffordAlg.smul (halfField F * halfField F) (X * Y) := by
      rw [← CliffordAlg.ofScalar_mul_eq_smul, CliffordAlg.ofScalar_mul,
          AssocRing.mul_assoc h X (h * Y),
          ← AssocRing.mul_assoc X h Y,
          ← hhC X,
          AssocRing.mul_assoc h X Y,
          ← AssocRing.mul_assoc h h (X * Y)]
    show CliffordAlg.scalarPart ((h * X) * (h * Y)).raw = halfField F * halfField F
    rw [mul_h2, CliffordAlg.raw_smul, CliffordAlg.scalarPart_scale,
        CliffordAlg.scalarPart_fst (X * Y).raw, hXY_fst, hX_sc, AssocRing.mul_one]
  refine ⟨p, ?_, ?_⟩
  · intro i
    have prod_idem : ∀ u v : CliffordAlg F 4 q31,
        u * u = u → v * v = v → u * v = v * u → (u * v) * (u * v) = u * v := by
      intro u v hu hv huv
      calc
        (u * v) * (u * v) = u * ((v * u) * v) := by
          rw [AssocRing.mul_assoc u v (u * v), ← AssocRing.mul_assoc v u v]
        _ = (u * u) * (v * v) := by
          rw [← huv, AssocRing.mul_assoc u v v, ← AssocRing.mul_assoc u u (v * v)]
        _ = u * v := by rw [hu, hv]
    have hsc0 : CliffordAlg.scalarPart (0 : CliffordAlg F 4 q31).raw = 0 := by
      rw [CliffordAlg.raw_zero, CliffordAlg.scalarPart_zero]
    have hup_eq : up = h * (1 + CliffordAlg.ofScalar 1 * α) := by
      show h * (1 + α) = _; rw [← one_as_ofScalar α]
    have hum_eq : um = h * (1 + CliffordAlg.ofScalar (-1) * α) := by
      show h * (1 - α) = _; rw [← neg_as_ofScalar α]
    have hvp_eq : vp = h * (1 + CliffordAlg.ofScalar 1 * β) := by
      show h * (1 + β) = _; rw [← one_as_ofScalar β]
    have hvm_eq : vm = h * (1 + CliffordAlg.ofScalar (-1) * β) := by
      show h * (1 - β) = _; rw [← neg_as_ofScalar β]
    match i with
    | ⟨0, _⟩ =>
      refine ⟨?_, prod_idem up vp hup2 hvp2 (comm_uv up (by simp) vp (by simp))⟩
      intro h0
      dsimp only [p] at h0
      have hs := congrArg (fun x : CliffordAlg F 4 q31 => CliffordAlg.scalarPart x.raw) h0
      dsimp only at hs
      rw [hsc0, hup_eq, hvp_eq, scalar_p 1 1] at hs
      exact hhh_ne hs
    | ⟨1, _⟩ =>
      refine ⟨?_, prod_idem up vm hup2 hvm2 (comm_uv up (by simp) vm (by simp))⟩
      intro h0
      dsimp only [p] at h0
      have hs := congrArg (fun x : CliffordAlg F 4 q31 => CliffordAlg.scalarPart x.raw) h0
      dsimp only at hs
      rw [hsc0, hup_eq, hvm_eq, scalar_p 1 (-1)] at hs
      exact hhh_ne hs
    | ⟨2, _⟩ =>
      refine ⟨?_, prod_idem um vp hum2 hvp2 (comm_uv um (by simp) vp (by simp))⟩
      intro h0
      dsimp only [p] at h0
      have hs := congrArg (fun x : CliffordAlg F 4 q31 => CliffordAlg.scalarPart x.raw) h0
      dsimp only at hs
      rw [hsc0, hum_eq, hvp_eq, scalar_p (-1) 1] at hs
      exact hhh_ne hs
    | ⟨3, _⟩ =>
      refine ⟨?_, prod_idem um vm hum2 hvm2 (comm_uv um (by simp) vm (by simp))⟩
      intro h0
      dsimp only [p] at h0
      have hs := congrArg (fun x : CliffordAlg F 4 q31 => CliffordAlg.scalarPart x.raw) h0
      dsimp only at hs
      rw [hsc0, hum_eq, hvm_eq, scalar_p (-1) (-1)] at hs
      exact hhh_ne hs
  · intro i j hij
    have orth_helper : ∀ u1 v1 u2 v2 : CliffordAlg F 4 q31,
        v1 * u2 = u2 * v1 → (u1 * u2 = 0 ∨ v1 * v2 = 0) → (u1 * v1) * (u2 * v2) = 0 := by
      intro u1 v1 u2 v2 hc hor
      have rearrange : (u1 * v1) * (u2 * v2) = (u1 * u2) * (v1 * v2) := by
        rw [AssocRing.mul_assoc u1 v1 (u2 * v2),
            ← AssocRing.mul_assoc v1 u2 v2, hc,
            AssocRing.mul_assoc u2 v1 v2,
            ← AssocRing.mul_assoc u1 u2 (v1 * v2)]
      rw [rearrange]
      cases hor with
      | inl hu0 => rw [hu0, zero_mul_ring]
      | inr hv0 => rw [hv0, mul_zero_ring]
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => exact False.elim (hij rfl)
    | ⟨0, _⟩, ⟨1, _⟩ => exact orth_helper up vp up vm (comm_uv up (by simp) vp (by simp)).symm (Or.inr hvpm)
    | ⟨0, _⟩, ⟨2, _⟩ => exact orth_helper up vp um vp (comm_uv um (by simp) vp (by simp)).symm (Or.inl hupm)
    | ⟨0, _⟩, ⟨3, _⟩ => exact orth_helper up vp um vm (comm_uv um (by simp) vp (by simp)).symm (Or.inl hupm)
    | ⟨1, _⟩, ⟨0, _⟩ => exact orth_helper up vm up vp (comm_uv up (by simp) vm (by simp)).symm (Or.inr hvmp)
    | ⟨1, _⟩, ⟨1, _⟩ => exact False.elim (hij rfl)
    | ⟨1, _⟩, ⟨2, _⟩ => exact orth_helper up vm um vp (comm_uv um (by simp) vm (by simp)).symm (Or.inl hupm)
    | ⟨1, _⟩, ⟨3, _⟩ => exact orth_helper up vm um vm (comm_uv um (by simp) vm (by simp)).symm (Or.inl hupm)
    | ⟨2, _⟩, ⟨0, _⟩ => exact orth_helper um vp up vp (comm_uv up (by simp) vp (by simp)).symm (Or.inl hump)
    | ⟨2, _⟩, ⟨1, _⟩ => exact orth_helper um vp up vm (comm_uv up (by simp) vp (by simp)).symm (Or.inl hump)
    | ⟨2, _⟩, ⟨2, _⟩ => exact False.elim (hij rfl)
    | ⟨2, _⟩, ⟨3, _⟩ => exact orth_helper um vp um vm (comm_uv um (by simp) vp (by simp)).symm (Or.inr hvpm)
    | ⟨3, _⟩, ⟨0, _⟩ => exact orth_helper um vm up vp (comm_uv up (by simp) vm (by simp)).symm (Or.inl hump)
    | ⟨3, _⟩, ⟨1, _⟩ => exact orth_helper um vm up vm (comm_uv up (by simp) vm (by simp)).symm (Or.inl hump)
    | ⟨3, _⟩, ⟨2, _⟩ => exact orth_helper um vm um vp (comm_uv um (by simp) vm (by simp)).symm (Or.inr hvmp)
    | ⟨3, _⟩, ⟨3, _⟩ => exact False.elim (hij rfl)

/-! #### Part B: Hamilton's Quaternions `ℍ_F = Cl_{0,2}(F)` as a Division Ring & `M₂(ℍ_F)` Pierce Bound -/

/-- Hamilton's quaternion algebra `ℍ_F`, realized as `Cl_{0,2}(F)`. -/
abbrev QuatAlg (F : Type u) [FormallyRealField F] : Type u :=
  CliffordAlg F 2 (fun _ => (-1 : F))

def quatConj (x : QuatAlg F) : QuatAlg F :=
  ⟨((x.raw.1.1, -(x.raw.1.2)), (-(x.raw.2.1), -(x.raw.2.2)))⟩

def quatNormSq (x : QuatAlg F) : F :=
  x.raw.1.1 * x.raw.1.1 + x.raw.1.2 * x.raw.1.2 +
  x.raw.2.1 * x.raw.2.1 + x.raw.2.2 * x.raw.2.2

private theorem cpxMul_comm (u v : F × F) :
    clMul (fun _ : Fin 1 => (-1 : F)) u v = clMul (fun _ : Fin 1 => (-1 : F)) v u := by
  rcases u with ⟨u1, u2⟩; rcases v with ⟨v1, v2⟩
  rw [clMul_succ, clMul_succ]
  dsimp only [clMul, clAdd, clScale, clInvol]
  apply Prod.ext
  · show u1 * v1 + (-1) * (u2 * v2) = v1 * u1 + (-1) * (v2 * u2)
    rw [FormallyRealField.mul_comm u1 v1, FormallyRealField.mul_comm u2 v2]
  · show u1 * v2 + u2 * v1 = v1 * u2 + v2 * u1
    rw [FormallyRealField.mul_comm u1 v2, FormallyRealField.mul_comm u2 v1,
        AssocRing.add_comm]

private theorem cpxMul_conj_right (u : F × F) :
    clMul (fun _ : Fin 1 => (-1 : F)) u (clInvol (n := 1) u) = (u.1 * u.1 + u.2 * u.2, 0) := by
  rcases u with ⟨a, b⟩
  rw [clInvol_succ (m := 0), clMul_succ]
  dsimp only [clMul, clAdd, clScale, clInvol, clNeg]
  apply Prod.ext
  · show a * a + (-1) * (b * -b) = a * a + b * b
    rw [mul_neg_ring b b, neg_mul_neg_ring 1 (b * b), AssocRing.one_mul]
  · show a * -b + b * a = 0
    rw [mul_neg_ring a b, FormallyRealField.mul_comm b a, AssocRing.neg_add_cancel]

private theorem cpxMul_conj_left (u : F × F) :
    clMul (fun _ : Fin 1 => (-1 : F)) (clInvol (n := 1) u) u = (u.1 * u.1 + u.2 * u.2, 0) := by
  rw [cpxMul_comm, cpxMul_conj_right]

theorem quat_mul_conj (x : QuatAlg F) :
    x * quatConj x = CliffordAlg.ofScalar (quatNormSq x) := by
  rcases x with ⟨⟨u, w⟩⟩
  apply CliffordAlg.ext
  unfold quatConj quatNormSq CliffordAlg.ofScalar
  change clMul (fun _ => (-1 : F)) (u, w) (clInvol (n := 1) u, clNeg (n := 1) w) =
    clScale (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) (clOne 2)
  rw [clMul_succ]
  let q1 : Fin 1 → F := fun _ => (-1 : F)
  apply Prod.ext
  · dsimp only
    rw [cpxMul_conj_right u, clMul_neg_right q1 (clInvol w) w,
        cpxMul_conj_left w, clScale_neg, clNeg_scale, clOne_scale, clNeg_neg]
    show (u.1 * u.1 + u.2 * u.2 + (w.1 * w.1 + w.2 * w.2), (0 : F) + 0) =
      ((u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 1,
       (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0)
    rw [AssocRing.add_zero, AssocRing.mul_one, mul_zero_ring,
        ← AssocRing.add_assoc (u.1 * u.1 + u.2 * u.2) (w.1 * w.1) (w.2 * w.2)]
  · dsimp only
    rw [clMul_neg_right q1 (clInvol u) w, cpxMul_comm w (clInvol u), clNeg_add_cancel]
    show ((0 : F), (0 : F)) =
      ((u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0,
       (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0)
    rw [mul_zero_ring]

theorem quat_conj_mul (x : QuatAlg F) :
    quatConj x * x = CliffordAlg.ofScalar (quatNormSq x) := by
  rcases x with ⟨⟨u, w⟩⟩
  apply CliffordAlg.ext
  unfold quatConj quatNormSq CliffordAlg.ofScalar
  change clMul (fun _ => (-1 : F)) (clInvol (n := 1) u, clNeg (n := 1) w) (u, w) =
    clScale (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) (clOne 2)
  rw [clMul_succ]
  let q1 : Fin 1 → F := fun _ => (-1 : F)
  apply Prod.ext
  · dsimp only
    rw [cpxMul_conj_left u, clInvol_neg, clMul_neg_left q1 (clInvol w) w,
        cpxMul_conj_left w, clScale_neg, clNeg_scale, clOne_scale, clNeg_neg]
    show (u.1 * u.1 + u.2 * u.2 + (w.1 * w.1 + w.2 * w.2), (0 : F) + 0) =
      ((u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 1,
       (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0)
    rw [AssocRing.add_zero, AssocRing.mul_one, mul_zero_ring,
        ← AssocRing.add_assoc (u.1 * u.1 + u.2 * u.2) (w.1 * w.1) (w.2 * w.2)]
  · dsimp only
    rw [clInvol_invol, clMul_neg_left q1 w u, cpxMul_comm w u,
        clAdd_comm, clNeg_add_cancel]
    show ((0 : F), (0 : F)) =
      ((u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0,
       (u.1 * u.1 + u.2 * u.2 + w.1 * w.1 + w.2 * w.2) * 0)
    rw [mul_zero_ring]

/-- Every nonzero quaternion in `QuatAlg F` over a `FormallyRealField F` has a two-sided inverse! -/
theorem quat_is_division_ring (x : QuatAlg F) (hx : x ≠ 0) :
    ∃ y : QuatAlg F, x * y = 1 ∧ y * x = 1 := by
  have hnorm_ne : quatNormSq x ≠ 0 := by
    intro hn
    rcases FormallyRealField.sum_four_sq_eq_zero
      x.raw.1.1 x.raw.1.2 x.raw.2.1 x.raw.2.2 hn with ⟨h1, h2, h3, h4⟩
    apply hx
    apply CliffordAlg.ext
    rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
    dsimp only at h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    rfl
  let invN : QuatAlg F := CliffordAlg.ofScalar (FormallyRealField.inv (quatNormSq x))
  refine ⟨invN * quatConj x, ?_, ?_⟩
  · rw [← AssocRing.mul_assoc x invN (quatConj x),
        ← CliffordAlg.ofScalar_central (FormallyRealField.inv (quatNormSq x)) x,
        AssocRing.mul_assoc invN x (quatConj x),
        quat_mul_conj, ← CliffordAlg.ofScalar_mul,
        inv_mul_cancel_field hnorm_ne, CliffordAlg.ofScalar_one]
  · rw [AssocRing.mul_assoc invN (quatConj x) x,
        quat_conj_mul, ← CliffordAlg.ofScalar_mul,
        inv_mul_cancel_field hnorm_ne, CliffordAlg.ofScalar_one]

end EvenLorentzianSeparation

/-! #### Part C: `2 × 2` Matrices over Any Associative / Division Ring -/

structure Mat2 (R : Type u) : Type u where
  m00 : R
  m01 : R
  m10 : R
  m11 : R

namespace Mat2

@[ext]
theorem ext {R : Type u} {A B : Mat2 R}
    (h00 : A.m00 = B.m00) (h01 : A.m01 = B.m01)
    (h10 : A.m10 = B.m10) (h11 : A.m11 = B.m11) : A = B := by
  cases A; cases B
  dsimp only at h00 h01 h10 h11
  subst h00; subst h01; subst h10; subst h11
  rfl

section RingInst

variable {R : Type u} [AssocRing R]

private theorem mat2_mul_entry_assoc (a00 a01 b00 b01 b10 b11 c0 c1 : R) :
    (a00 * b00 + a01 * b10) * c0 + (a00 * b01 + a01 * b11) * c1 =
    a00 * (b00 * c0 + b01 * c1) + a01 * (b10 * c0 + b11 * c1) := by
  rw [AssocRing.right_distrib, AssocRing.right_distrib,
      AssocRing.left_distrib, AssocRing.left_distrib,
      AssocRing.mul_assoc, AssocRing.mul_assoc, AssocRing.mul_assoc, AssocRing.mul_assoc]
  let u1 := a00 * (b00 * c0)
  let u2 := a01 * (b10 * c0)
  let v1 := a00 * (b01 * c1)
  let v2 := a01 * (b11 * c1)
  show (u1 + u2) + (v1 + v2) = (u1 + v1) + (u2 + v2)
  rw [AssocRing.add_assoc u1 u2 (v1 + v2),
      ← AssocRing.add_assoc u2 v1 v2,
      AssocRing.add_comm u2 v1,
      AssocRing.add_assoc v1 u2 v2,
      ← AssocRing.add_assoc u1 v1 (u2 + v2)]

private theorem sum4_rearrange_ring (u1 u2 v1 v2 : R) :
    (u1 + u2) + (v1 + v2) = (u1 + v1) + (u2 + v2) := by
  rw [AssocRing.add_assoc u1 u2 (v1 + v2),
      ← AssocRing.add_assoc u2 v1 v2,
      AssocRing.add_comm u2 v1,
      AssocRing.add_assoc v1 u2 v2,
      ← AssocRing.add_assoc u1 v1 (u2 + v2)]

instance : AssocRing (Mat2 R) where
  zero := ⟨0, 0, 0, 0⟩
  ofNat := ⟨1, 0, 0, 1⟩
  add := fun A B => ⟨A.m00 + B.m00, A.m01 + B.m01, A.m10 + B.m10, A.m11 + B.m11⟩
  neg := fun A => ⟨-A.m00, -A.m01, -A.m10, -A.m11⟩
  sub := fun A B => ⟨A.m00 + -B.m00, A.m01 + -B.m01, A.m10 + -B.m10, A.m11 + -B.m11⟩
  mul := fun A B =>
    ⟨A.m00 * B.m00 + A.m01 * B.m10, A.m00 * B.m01 + A.m01 * B.m11,
     A.m10 * B.m00 + A.m11 * B.m10, A.m10 * B.m01 + A.m11 * B.m11⟩
  add_assoc := fun A B C => ext
    (AssocRing.add_assoc A.m00 B.m00 C.m00) (AssocRing.add_assoc A.m01 B.m01 C.m01)
    (AssocRing.add_assoc A.m10 B.m10 C.m10) (AssocRing.add_assoc A.m11 B.m11 C.m11)
  add_comm := fun A B => ext
    (AssocRing.add_comm A.m00 B.m00) (AssocRing.add_comm A.m01 B.m01)
    (AssocRing.add_comm A.m10 B.m10) (AssocRing.add_comm A.m11 B.m11)
  zero_add := fun A => ext
    (AssocRing.zero_add A.m00) (AssocRing.zero_add A.m01)
    (AssocRing.zero_add A.m10) (AssocRing.zero_add A.m11)
  add_zero := fun A => ext
    (AssocRing.add_zero A.m00) (AssocRing.add_zero A.m01)
    (AssocRing.add_zero A.m10) (AssocRing.add_zero A.m11)
  neg_add_cancel := fun A => ext
    (AssocRing.neg_add_cancel A.m00) (AssocRing.neg_add_cancel A.m01)
    (AssocRing.neg_add_cancel A.m10) (AssocRing.neg_add_cancel A.m11)
  sub_eq_add_neg := fun _ _ => rfl
  mul_assoc := fun A B C => ext
    (mat2_mul_entry_assoc A.m00 A.m01 B.m00 B.m01 B.m10 B.m11 C.m00 C.m10)
    (mat2_mul_entry_assoc A.m00 A.m01 B.m00 B.m01 B.m10 B.m11 C.m01 C.m11)
    (mat2_mul_entry_assoc A.m10 A.m11 B.m00 B.m01 B.m10 B.m11 C.m00 C.m10)
    (mat2_mul_entry_assoc A.m10 A.m11 B.m00 B.m01 B.m10 B.m11 C.m01 C.m11)
  one_mul := fun A => ext
    (by show 1 * A.m00 + 0 * A.m10 = A.m00; rw [AssocRing.one_mul, zero_mul_ring, AssocRing.add_zero])
    (by show 1 * A.m01 + 0 * A.m11 = A.m01; rw [AssocRing.one_mul, zero_mul_ring, AssocRing.add_zero])
    (by show 0 * A.m00 + 1 * A.m10 = A.m10; rw [zero_mul_ring, AssocRing.one_mul, AssocRing.zero_add])
    (by show 0 * A.m01 + 1 * A.m11 = A.m11; rw [zero_mul_ring, AssocRing.one_mul, AssocRing.zero_add])
  mul_one := fun A => ext
    (by show A.m00 * 1 + A.m01 * 0 = A.m00; rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero])
    (by show A.m00 * 0 + A.m01 * 1 = A.m01; rw [mul_zero_ring, AssocRing.mul_one, AssocRing.zero_add])
    (by show A.m10 * 1 + A.m11 * 0 = A.m10; rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero])
    (by show A.m10 * 0 + A.m11 * 1 = A.m11; rw [mul_zero_ring, AssocRing.mul_one, AssocRing.zero_add])
  left_distrib := fun A B C => ext
    (by show A.m00 * (B.m00 + C.m00) + A.m01 * (B.m10 + C.m10) = (A.m00 * B.m00 + A.m01 * B.m10) + (A.m00 * C.m00 + A.m01 * C.m10)
        rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring])
    (by show A.m00 * (B.m01 + C.m01) + A.m01 * (B.m11 + C.m11) = (A.m00 * B.m01 + A.m01 * B.m11) + (A.m00 * C.m01 + A.m01 * C.m11)
        rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring])
    (by show A.m10 * (B.m00 + C.m00) + A.m11 * (B.m10 + C.m10) = (A.m10 * B.m00 + A.m11 * B.m10) + (A.m10 * C.m00 + A.m11 * C.m10)
        rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring])
    (by show A.m10 * (B.m01 + C.m01) + A.m11 * (B.m11 + C.m11) = (A.m10 * B.m01 + A.m11 * B.m11) + (A.m10 * C.m01 + A.m11 * C.m11)
        rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring])
  right_distrib := fun A B C => ext
    (by show (A.m00 + B.m00) * C.m00 + (A.m01 + B.m01) * C.m10 = (A.m00 * C.m00 + A.m01 * C.m10) + (B.m00 * C.m00 + B.m01 * C.m10)
        rw [AssocRing.right_distrib, AssocRing.right_distrib, sum4_rearrange_ring])
    (by show (A.m00 + B.m00) * C.m01 + (A.m01 + B.m01) * C.m11 = (A.m00 * C.m01 + A.m01 * C.m11) + (B.m00 * C.m01 + B.m01 * C.m11)
        rw [AssocRing.right_distrib, AssocRing.right_distrib, sum4_rearrange_ring])
    (by show (A.m10 + B.m10) * C.m00 + (A.m11 + B.m11) * C.m10 = (A.m10 * C.m00 + A.m11 * C.m10) + (B.m10 * C.m00 + B.m11 * C.m10)
        rw [AssocRing.right_distrib, AssocRing.right_distrib, sum4_rearrange_ring])
    (by show (A.m10 + B.m10) * C.m01 + (A.m11 + B.m11) * C.m11 = (A.m10 * C.m01 + A.m11 * C.m11) + (B.m10 * C.m01 + B.m11 * C.m11)
        rw [AssocRing.right_distrib, AssocRing.right_distrib, sum4_rearrange_ring])

def act (M : Mat2 R) (v : R × R) : R × R :=
  (M.m00 * v.1 + M.m01 * v.2, M.m10 * v.1 + M.m11 * v.2)

def rsmul (v : R × R) (c : R) : R × R := (v.1 * c, v.2 * c)
def vadd (u v : R × R) : R × R := (u.1 + v.1, u.2 + v.2)
def vsub (u v : R × R) : R × R := (u.1 - v.1, u.2 - v.2)

theorem act_mul (M N : Mat2 R) (v : R × R) :
    act (M * N) v = act M (act N v) := by
  apply Prod.ext
  · exact mat2_mul_entry_assoc M.m00 M.m01 N.m00 N.m01 N.m10 N.m11 v.1 v.2
  · exact mat2_mul_entry_assoc M.m10 M.m11 N.m00 N.m01 N.m10 N.m11 v.1 v.2

theorem act_zero (v : R × R) : act (0 : Mat2 R) v = (0, 0) := by
  unfold act
  show (0 * v.1 + 0 * v.2, 0 * v.1 + 0 * v.2) = (0, 0)
  rw [zero_mul_ring, zero_mul_ring, AssocRing.add_zero]

theorem act_zero_vec (M : Mat2 R) : act M (0, 0) = (0, 0) := by
  unfold act
  show (M.m00 * 0 + M.m01 * 0, M.m10 * 0 + M.m11 * 0) = (0, 0)
  rw [mul_zero_ring, mul_zero_ring, mul_zero_ring, mul_zero_ring, AssocRing.add_zero]

theorem act_rsmul (M : Mat2 R) (v : R × R) (c : R) :
    act M (rsmul v c) = rsmul (act M v) c := by
  apply Prod.ext
  · dsimp only [act, rsmul]
    rw [AssocRing.right_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]
  · dsimp only [act, rsmul]
    rw [AssocRing.right_distrib, AssocRing.mul_assoc, AssocRing.mul_assoc]

theorem act_vadd (M : Mat2 R) (u v : R × R) :
    act M (vadd u v) = vadd (act M u) (act M v) := by
  apply Prod.ext
  · dsimp only [act, vadd]
    rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring]
  · dsimp only [act, vadd]
    rw [AssocRing.left_distrib, AssocRing.left_distrib, sum4_rearrange_ring]

theorem act_vsub (M : Mat2 R) (u v : R × R) :
    act M (vsub u v) = vsub (act M u) (act M v) := by
  apply Prod.ext
  · dsimp only [act, vsub]
    rw [mul_sub_ring, mul_sub_ring,
        AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg,
        neg_add_distrib_ring, sum4_rearrange_ring]
  · dsimp only [act, vsub]
    rw [mul_sub_ring, mul_sub_ring,
        AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg,
        neg_add_distrib_ring, sum4_rearrange_ring]

/-- Division-Ring Pierce Rank Bound: `M₂(D)` over any division ring `D` has at most 2
    mutually orthogonal nonzero idempotents (cannot have 3)! -/
theorem no_three_orthogonal_idempotents_of_divRing
    (hdiv : ∀ x : R, x ≠ 0 → ∃ y : R, x * y = 1 ∧ y * x = 1) :
    ¬ HasOrthogonalIdempotents (Mat2 R) 3 := by
  rintro ⟨P, hP, horth⟩
  -- For each r ∈ Fin 3, pick a nonzero column vector e_r ∈ {(1,0), (0,1)} with act (P r) e_r ≠ (0,0)
  have hex_vec : ∀ r : Fin 3, ∃ v : R × R,
      v ≠ (0, 0) ∧ act (P r) v = v ∧ (∀ s : Fin 3, s ≠ r → act (P s) v = (0, 0)) := by
    intro r
    by_cases hc1 : act (P r) (1, 0) = (0, 0)
    · -- Then column 2 must be nonzero!
      have hc2 : act (P r) (0, 1) ≠ (0, 0) := by
        intro hc2_0
        apply (hP r).1
        unfold act at hc1 hc2_0
        have h00 : (P r).m00 = 0 := by
          have p := congrArg Prod.fst hc1
          dsimp only at p
          rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero] at p
          exact p
        have h10 : (P r).m10 = 0 := by
          have p := congrArg Prod.snd hc1
          dsimp only at p
          rw [AssocRing.mul_one, mul_zero_ring, AssocRing.add_zero] at p
          exact p
        have h01 : (P r).m01 = 0 := by
          have p := congrArg Prod.fst hc2_0
          dsimp only at p
          rw [mul_zero_ring, AssocRing.mul_one, AssocRing.zero_add] at p
          exact p
        have h11 : (P r).m11 = 0 := by
          have p := congrArg Prod.snd hc2_0
          dsimp only at p
          rw [mul_zero_ring, AssocRing.mul_one, AssocRing.zero_add] at p
          exact p
        exact ext h00 h01 h10 h11
      refine ⟨act (P r) (0, 1), hc2, ?_, ?_⟩
      · rw [← act_mul, (hP r).2]
      · intro s hsr
        rw [← act_mul, horth s r hsr, act_zero]
    · refine ⟨act (P r) (1, 0), hc1, ?_, ?_⟩
      · rw [← act_mul, (hP r).2]
      · intro s hsr
        rw [← act_mul, horth s r hsr, act_zero]
  let i0 : Fin 3 := ⟨0, by decide⟩
  let i1 : Fin 3 := ⟨1, by decide⟩
  let i2 : Fin 3 := ⟨2, by decide⟩
  rcases hex_vec i0 with ⟨v0, hv0_ne, _, hv0_orth⟩
  rcases hex_vec i1 with ⟨v1, hv1_ne, hv1_fix, hv1_orth⟩
  rcases hex_vec i2 with ⟨v2, hv2_ne, hv2_fix, _⟩
  -- Kernel predicates of P1 and P2
  let K2 : R × R → Prop := fun u => act (P i2) u = (0, 0)
  have K2_rsmul : ∀ u c, K2 u → K2 (rsmul u c) := by
    intro u c hu; unfold K2 at *; rw [act_rsmul, hu]; exact Prod.ext (zero_mul_ring c) (zero_mul_ring c)
  have K2_vadd : ∀ u w, K2 u → K2 w → K2 (vadd u w) := by
    intro u w hu hw; unfold K2 at *; rw [act_vadd, hu, hw]; exact Prod.ext (AssocRing.add_zero 0) (AssocRing.add_zero 0)
  have K2_vsub : ∀ u w, K2 u → K2 w → K2 (vsub u w) := by
    intro u w hu hw; unfold K2 at *; rw [act_vsub, hu, hw]; exact Prod.ext (sub_self_ring 0) (sub_self_ring 0)
  have hv0_K2 : K2 v0 := hv0_orth i2 (by decide)
  have hv1_K2 : K2 v1 := hv1_orth i2 (by decide)
  have hv0_K1 : act (P i1) v0 = (0, 0) := hv0_orth i1 (by decide)
  -- Show both (1, 0) and (0, 1) lie in K2 by Gauss-Jordan elimination on v0, v1!
  have hbasis_K2 : K2 (1, 0) ∧ K2 (0, 1) := by
    by_cases ha0 : v0.1 = 0
    · -- v0 = (0, b0) with b0 ≠ 0
      have hb0 : v0.2 ≠ 0 := by
        intro hb0_0
        apply hv0_ne
        exact Prod.ext ha0 hb0_0
      rcases hdiv v0.2 hb0 with ⟨invb0, hbinv, _⟩
      have he2_eq : rsmul v0 invb0 = (0, 1) := by
        unfold rsmul
        rw [ha0, zero_mul_ring, hbinv]
      have he2_K2 : K2 (0, 1) := he2_eq ▸ K2_rsmul v0 invb0 hv0_K2
      have he2_K1 : act (P i1) (0, 1) = (0, 0) := by
        rw [← he2_eq, act_rsmul, hv0_K1]
        exact Prod.ext (zero_mul_ring _) (zero_mul_ring _)
      let w1 : R × R := vsub v1 (rsmul (0, 1) v1.2)
      have hw1_eq : w1 = (v1.1, 0) := by
        unfold w1 vsub rsmul
        rw [zero_mul_ring, AssocRing.one_mul, sub_self_ring,
            AssocRing.sub_eq_add_neg v1.1 0, neg_zero_ring, AssocRing.add_zero]
      have hw1_K2 : K2 w1 := K2_vsub v1 _ hv1_K2 (K2_rsmul (0, 1) v1.2 he2_K2)
      have hw1_P1 : act (P i1) w1 = v1 := by
        unfold w1
        rw [act_vsub, act_rsmul, hv1_fix, he2_K1]
        unfold rsmul vsub
        rw [zero_mul_ring, AssocRing.sub_eq_add_neg v1.1 0, AssocRing.sub_eq_add_neg v1.2 0,
            neg_zero_ring, AssocRing.add_zero, AssocRing.add_zero]
      have ha1 : v1.1 ≠ 0 := by
        intro ha1_0
        have hw0 : w1 = (0, 0) := by rw [hw1_eq, ha1_0]
        rw [hw0, act_zero_vec] at hw1_P1
        exact hv1_ne hw1_P1.symm
      rcases hdiv v1.1 ha1 with ⟨inva1, hainv, _⟩
      have he1_eq : rsmul w1 inva1 = (1, 0) := by
        rw [hw1_eq]
        unfold rsmul
        rw [hainv, zero_mul_ring]
      exact ⟨he1_eq ▸ K2_rsmul w1 inva1 hw1_K2, he2_K2⟩
    · -- v0.1 ≠ 0
      rcases hdiv v0.1 ha0 with ⟨inva0, hainv, _⟩
      let u0 : R × R := rsmul v0 inva0
      have hu0_1 : u0.1 = 1 := hainv
      have hu0_K2 : K2 u0 := K2_rsmul v0 inva0 hv0_K2
      have hu0_K1 : act (P i1) u0 = (0, 0) := by
        unfold u0; rw [act_rsmul, hv0_K1]
        exact Prod.ext (zero_mul_ring _) (zero_mul_ring _)
      let w1 : R × R := vsub v1 (rsmul u0 v1.1)
      have hw1_1 : w1.1 = 0 := by
        show v1.1 - u0.1 * v1.1 = 0
        rw [hu0_1, AssocRing.one_mul, sub_self_ring]
      have hw1_K2 : K2 w1 := K2_vsub v1 _ hv1_K2 (K2_rsmul u0 v1.1 hu0_K2)
      have hw1_P1 : act (P i1) w1 = v1 := by
        unfold w1
        rw [act_vsub, act_rsmul, hv1_fix, hu0_K1]
        unfold rsmul vsub
        rw [zero_mul_ring, AssocRing.sub_eq_add_neg v1.1 0, AssocRing.sub_eq_add_neg v1.2 0,
            neg_zero_ring, AssocRing.add_zero, AssocRing.add_zero]
      have hw1_2_ne : w1.2 ≠ 0 := by
        intro hw2_0
        have hw0 : w1 = (0, 0) := Prod.ext hw1_1 hw2_0
        rw [hw0, act_zero_vec] at hw1_P1
        exact hv1_ne hw1_P1.symm
      rcases hdiv w1.2 hw1_2_ne with ⟨invw, hwinv, _⟩
      have he2_eq : rsmul w1 invw = (0, 1) := by
        unfold rsmul
        rw [hw1_1, zero_mul_ring, hwinv]
      have he2_K2 : K2 (0, 1) := he2_eq ▸ K2_rsmul w1 invw hw1_K2
      have he1_eq : vsub u0 (rsmul (0, 1) u0.2) = (1, 0) := by
        unfold vsub rsmul
        rw [hu0_1, zero_mul_ring, AssocRing.one_mul, sub_self_ring,
            AssocRing.sub_eq_add_neg 1 0, neg_zero_ring, AssocRing.add_zero]
      exact ⟨he1_eq ▸ K2_vsub u0 _ hu0_K2 (K2_rsmul (0, 1) u0.2 he2_K2), he2_K2⟩
  -- Now v2 = (1, 0) • v2.1 + (0, 1) • v2.2 ∈ K2!
  have hv2_decomp : vadd (rsmul (1, 0) v2.1) (rsmul (0, 1) v2.2) = v2 := by
    unfold vadd rsmul
    rw [AssocRing.one_mul, zero_mul_ring, zero_mul_ring, AssocRing.one_mul,
        AssocRing.add_zero, AssocRing.zero_add]
  have hv2_K2 : K2 v2 :=
    hv2_decomp ▸ K2_vadd _ _ (K2_rsmul (1, 0) v2.1 hbasis_K2.1) (K2_rsmul (0, 1) v2.2 hbasis_K2.2)
  unfold K2 at hv2_K2
  rw [hv2_fix] at hv2_K2
  exact hv2_ne hv2_K2

end RingInst

end Mat2

section EvenLorentzianSeparationPartD

variable {F : Type u} [FormallyRealField F]

/-! #### Part D: Explicit Injective Ring Homomorphism `Cl_{1,3}(F) → M₂(ℍ_F)` -/

private def quatI : QuatAlg F := CliffordAlg.gamma ⟨0, by decide⟩
private def quatJ : QuatAlg F := CliffordAlg.gamma ⟨1, by decide⟩
private def quatK : QuatAlg F := quatI * quatJ

private theorem quatI_sq : (quatI : QuatAlg F) * quatI = -1 := by
  unfold quatI
  rw [CliffordAlg.gamma_sq]
  apply CliffordAlg.ext
  show clScale (-1 : F) (clOne 2) = clNeg (clOne 2)
  rw [clNeg_scale, clOne_scale]

private theorem quatJ_sq : (quatJ : QuatAlg F) * quatJ = -1 := by
  unfold quatJ
  rw [CliffordAlg.gamma_sq]
  apply CliffordAlg.ext
  show clScale (-1 : F) (clOne 2) = clNeg (clOne 2)
  rw [clNeg_scale, clOne_scale]

private theorem quatIJ_anticomm : (quatI : QuatAlg F) * quatJ + quatJ * quatI = 0 :=
  CliffordAlg.gamma_anticomm _ (by decide)

private theorem quatK_sq : (quatK : QuatAlg F) * quatK = -1 := by
  let I : QuatAlg F := quatI
  let J : QuatAlg F := quatJ
  have aJI : J * I = -(I * J) :=
    anticomm_swap (CliffordAlg.gamma_anticomm _ (by decide))
  show (I * J) * (I * J) = -1
  calc
    (I * J) * (I * J)
        = I * ((J * I) * J) := by
          rw [AssocRing.mul_assoc I J (I * J), ← AssocRing.mul_assoc J I J]
    _ = -((I * I) * (J * J)) := by
          rw [aJI, neg_mul_ring, mul_neg_ring,
              ← AssocRing.mul_assoc I (I * J) J,
              ← AssocRing.mul_assoc I I J,
              AssocRing.mul_assoc (I * I) J J]
    _ = -((-1 : QuatAlg F) * (-1)) := by rw [quatI_sq, quatJ_sq]
    _ = -1 := by rw [neg_mul_neg_ring, AssocRing.one_mul]

private theorem quatIK_anticomm : (quatI : QuatAlg F) * quatK + quatK * quatI = 0 := by
  unfold quatK
  have aJI : (quatJ : QuatAlg F) * quatI = -(quatI * quatJ) :=
    anticomm_swap (CliffordAlg.gamma_anticomm _ (by decide))
  have t1 : (quatI : QuatAlg F) * (quatI * quatJ) = -quatJ := by
    rw [← AssocRing.mul_assoc, quatI_sq, neg_mul_ring, AssocRing.one_mul]
  have t2 : (quatI * quatJ : QuatAlg F) * quatI = quatJ := by
    rw [AssocRing.mul_assoc, aJI, mul_neg_ring, t1, neg_neg_ring]
  rw [t1, t2, AssocRing.neg_add_cancel]

private theorem quatJK_anticomm : (quatJ : QuatAlg F) * quatK + quatK * quatJ = 0 := by
  unfold quatK
  have aJI : (quatJ : QuatAlg F) * quatI = -(quatI * quatJ) :=
    anticomm_swap (CliffordAlg.gamma_anticomm _ (by decide))
  have t1 : (quatJ : QuatAlg F) * (quatI * quatJ) = quatI := by
    rw [← AssocRing.mul_assoc, aJI, neg_mul_ring, AssocRing.mul_assoc,
        quatJ_sq, mul_neg_ring, AssocRing.mul_one, neg_neg_ring]
  have t2 : (quatI * quatJ : QuatAlg F) * quatJ = -quatI := by
    rw [AssocRing.mul_assoc, quatJ_sq, mul_neg_ring, AssocRing.mul_one]
  rw [t1, t2, add_neg_cancel_right_ring]

def scalarToMat2Quat : RingHom F (Mat2 (QuatAlg F)) where
  toFun := fun c => ⟨CliffordAlg.ofScalar c, 0, 0, CliffordAlg.ofScalar c⟩
  map_one := by
    apply Mat2.ext
    · exact CliffordAlg.ofScalar_one
    · rfl
    · rfl
    · exact CliffordAlg.ofScalar_one
  map_add := fun a b => by
    apply Mat2.ext
    · exact CliffordAlg.ofScalar_add a b
    · exact (AssocRing.add_zero 0).symm
    · exact (AssocRing.add_zero 0).symm
    · exact CliffordAlg.ofScalar_add a b
  map_mul := fun a b => by
    apply Mat2.ext
    · show CliffordAlg.ofScalar (a * b) = CliffordAlg.ofScalar a * CliffordAlg.ofScalar b + 0 * 0
      rw [mul_zero_ring, AssocRing.add_zero, CliffordAlg.ofScalar_mul]
    · show (0 : QuatAlg F) = CliffordAlg.ofScalar a * 0 + 0 * CliffordAlg.ofScalar b
      rw [mul_zero_ring, zero_mul_ring, AssocRing.add_zero]
    · show (0 : QuatAlg F) = 0 * CliffordAlg.ofScalar b + CliffordAlg.ofScalar a * 0
      rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero]
    · show CliffordAlg.ofScalar (a * b) = 0 * 0 + CliffordAlg.ofScalar a * CliffordAlg.ofScalar b
      rw [mul_zero_ring, AssocRing.zero_add, CliffordAlg.ofScalar_mul]

private theorem scalarToMat2Quat_central (c : F) :
    IsCentral (scalarToMat2Quat (F := F).toFun c) := by
  intro M
  unfold scalarToMat2Quat
  dsimp only
  apply Mat2.ext
  · show CliffordAlg.ofScalar c * M.m00 + 0 * M.m10 = M.m00 * CliffordAlg.ofScalar c + M.m01 * 0
    rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero, AssocRing.add_zero,
        CliffordAlg.ofScalar_central]
  · show CliffordAlg.ofScalar c * M.m01 + 0 * M.m11 = M.m00 * 0 + M.m01 * CliffordAlg.ofScalar c
    rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero, AssocRing.zero_add,
        CliffordAlg.ofScalar_central]
  · show 0 * M.m00 + CliffordAlg.ofScalar c * M.m10 = M.m10 * CliffordAlg.ofScalar c + M.m11 * 0
    rw [zero_mul_ring, mul_zero_ring, AssocRing.zero_add, AssocRing.add_zero,
        CliffordAlg.ofScalar_central]
  · show 0 * M.m01 + CliffordAlg.ofScalar c * M.m11 = M.m10 * 0 + M.m11 * CliffordAlg.ofScalar c
    rw [zero_mul_ring, mul_zero_ring, AssocRing.zero_add, AssocRing.zero_add,
        CliffordAlg.ofScalar_central]

def cl13Gens : Fin 4 → Mat2 (QuatAlg F)
  | ⟨0, _⟩ => ⟨0, quatI, quatI, 0⟩
  | ⟨1, _⟩ => ⟨0, quatJ, quatJ, 0⟩
  | ⟨2, _⟩ => ⟨0, quatK, quatK, 0⟩
  | _ => ⟨1, 0, 0, -1⟩

private theorem offDiag_sq (u : QuatAlg F) (hu : u * u = -1) :
    (⟨0, u, u, 0⟩ : Mat2 (QuatAlg F)) * ⟨0, u, u, 0⟩ =
    scalarToMat2Quat.toFun (-1) := by
  have hofn1 : (CliffordAlg.ofScalar (-1) : QuatAlg F) = -1 := by
    apply CliffordAlg.ext
    show clScale (-1 : F) (clOne 2) = clNeg (clOne 2)
    rw [clNeg_scale, clOne_scale]
  apply Mat2.ext
  · show 0 * 0 + u * u = CliffordAlg.ofScalar (-1)
    rw [zero_mul_ring, AssocRing.zero_add, hu, hofn1]
  · show 0 * u + u * 0 = 0
    rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero]
  · show u * 0 + 0 * u = 0
    rw [mul_zero_ring, zero_mul_ring, AssocRing.add_zero]
  · show u * u + 0 * 0 = CliffordAlg.ofScalar (-1)
    rw [zero_mul_ring, AssocRing.add_zero, hu, hofn1]

private theorem offDiag_anticomm (u v : QuatAlg F) (huv : u * v + v * u = 0) :
    (⟨0, u, u, 0⟩ : Mat2 (QuatAlg F)) * ⟨0, v, v, 0⟩ +
    ⟨0, v, v, 0⟩ * ⟨0, u, u, 0⟩ = 0 := by
  apply Mat2.ext
  · show (0 * 0 + u * v) + (0 * 0 + v * u) = 0
    rw [zero_mul_ring, AssocRing.zero_add, AssocRing.zero_add, huv]
  · show (0 * v + u * 0) + (0 * u + v * 0) = 0
    rw [zero_mul_ring, mul_zero_ring, zero_mul_ring, mul_zero_ring,
        AssocRing.add_zero, AssocRing.add_zero]
  · show (u * 0 + 0 * v) + (v * 0 + 0 * u) = 0
    rw [mul_zero_ring, zero_mul_ring, mul_zero_ring, zero_mul_ring,
        AssocRing.add_zero, AssocRing.add_zero]
  · show (u * v + 0 * 0) + (v * u + 0 * 0) = 0
    rw [zero_mul_ring, AssocRing.add_zero, AssocRing.add_zero, huv]

private theorem offDiag_diagZ_anticomm (u : QuatAlg F) :
    (⟨0, u, u, 0⟩ : Mat2 (QuatAlg F)) * ⟨1, 0, 0, -1⟩ +
    ⟨1, 0, 0, -1⟩ * ⟨0, u, u, 0⟩ = 0 := by
  apply Mat2.ext
  · show (0 * 1 + u * 0) + (1 * 0 + 0 * u) = 0
    simp only [zero_mul_ring, mul_zero_ring, AssocRing.add_zero]
  · show (0 * 0 + u * -1) + (1 * u + 0 * 0) = 0
    rw [zero_mul_ring, mul_neg_ring, AssocRing.mul_one, AssocRing.one_mul,
        AssocRing.zero_add, AssocRing.add_zero, AssocRing.neg_add_cancel]
  · show (u * 1 + 0 * 0) + (0 * 0 + -1 * u) = 0
    rw [AssocRing.mul_one, zero_mul_ring, neg_mul_ring, AssocRing.one_mul,
        AssocRing.add_zero, AssocRing.zero_add, add_neg_cancel_right_ring]
  · show (u * 0 + 0 * -1) + (0 * u + -1 * 0) = 0
    simp only [zero_mul_ring, mul_zero_ring, AssocRing.add_zero]

def cl13ToMat2Quat :
    RingHom (CliffordAlg F 4 (Sig.toVec (confModel02 (F := F)).ambSig)) (Mat2 (QuatAlg F)) :=
  CliffordAlg.lift
    scalarToMat2Quat
    scalarToMat2Quat_central
    cl13Gens
    (fun i => by
      match i with
      | ⟨0, _⟩ => exact offDiag_sq quatI quatI_sq
      | ⟨1, _⟩ => exact offDiag_sq quatJ quatJ_sq
      | ⟨2, _⟩ => exact offDiag_sq quatK quatK_sq
      | ⟨3, _⟩ =>
        show (⟨1, 0, 0, -1⟩ : Mat2 (QuatAlg F)) * ⟨1, 0, 0, -1⟩ = scalarToMat2Quat.toFun 1
        rw [scalarToMat2Quat.map_one]
        apply Mat2.ext
        · show (1 : QuatAlg F) * 1 + 0 * 0 = 1
          rw [AssocRing.one_mul, mul_zero_ring, AssocRing.add_zero]
        · show (1 : QuatAlg F) * 0 + 0 * -1 = 0
          rw [mul_zero_ring, zero_mul_ring, AssocRing.add_zero]
        · show (0 : QuatAlg F) * 1 + -1 * 0 = 0
          rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero]
        · show (0 : QuatAlg F) * 0 + -1 * -1 = 1
          rw [mul_zero_ring, neg_mul_neg_ring, AssocRing.one_mul, AssocRing.zero_add])
    (fun i j hij => by
      have symm_anti : ∀ A B : Mat2 (QuatAlg F), A * B + B * A = 0 → B * A + A * B = 0 := by
        intro A B h; rw [AssocRing.add_comm]; exact h
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact False.elim (hij rfl)
      | ⟨0, _⟩, ⟨1, _⟩ => exact offDiag_anticomm quatI quatJ quatIJ_anticomm
      | ⟨0, _⟩, ⟨2, _⟩ => exact offDiag_anticomm quatI quatK quatIK_anticomm
      | ⟨0, _⟩, ⟨3, _⟩ => exact offDiag_diagZ_anticomm quatI
      | ⟨1, _⟩, ⟨0, _⟩ => exact symm_anti _ _ (offDiag_anticomm quatI quatJ quatIJ_anticomm)
      | ⟨1, _⟩, ⟨1, _⟩ => exact False.elim (hij rfl)
      | ⟨1, _⟩, ⟨2, _⟩ => exact offDiag_anticomm quatJ quatK quatJK_anticomm
      | ⟨1, _⟩, ⟨3, _⟩ => exact offDiag_diagZ_anticomm quatJ
      | ⟨2, _⟩, ⟨0, _⟩ => exact symm_anti _ _ (offDiag_anticomm quatI quatK quatIK_anticomm)
      | ⟨2, _⟩, ⟨1, _⟩ => exact symm_anti _ _ (offDiag_anticomm quatJ quatK quatJK_anticomm)
      | ⟨2, _⟩, ⟨2, _⟩ => exact False.elim (hij rfl)
      | ⟨2, _⟩, ⟨3, _⟩ => exact offDiag_diagZ_anticomm quatK
      | ⟨3, _⟩, ⟨0, _⟩ => exact symm_anti _ _ (offDiag_diagZ_anticomm quatI)
      | ⟨3, _⟩, ⟨1, _⟩ => exact symm_anti _ _ (offDiag_diagZ_anticomm quatJ)
      | ⟨3, _⟩, ⟨2, _⟩ => exact symm_anti _ _ (offDiag_diagZ_anticomm quatK)
      | ⟨3, _⟩, ⟨3, _⟩ => exact False.elim (hij rfl))

private theorem lift3_cl13_formula (w : CliffordCarrier F 3) :
    let g3 : Fin 3 → Mat2 (QuatAlg F) := fun j => cl13Gens (finCastSucc j)
    let P : QuatAlg F := ⟨((w.1.1.1, -w.2.2.1), (w.2.1.2, w.1.2.2))⟩
    let Q : QuatAlg F := ⟨((w.2.2.2, w.1.1.2), (w.1.2.1, -w.2.1.1))⟩
    CliffordAlg.clLiftAux (scalarToMat2Quat (F := F)) g3 w = ⟨P, Q, Q, P⟩ := by
  rcases w with ⟨⟨⟨w000, w001⟩, ⟨w010, w011⟩⟩, ⟨⟨w100, w101⟩, ⟨w110, w111⟩⟩⟩
  dsimp only
  -- Unfold clLiftAux down to scalars and check equality of all 4 quaternion entries!
  have hI_raw : (quatI : QuatAlg F).raw = ((0, 1), (0, 0)) := rfl
  have hJ_raw : (quatJ : QuatAlg F).raw = ((0, 0), (1, 0)) := rfl
  have hK_raw : (quatK : QuatAlg F).raw = ((0, 0), (0, -1)) := by
    unfold quatK
    rw [CliffordAlg.raw_mul, hI_raw, hJ_raw]
    repeat rw [clMul_succ]
    repeat rw [clInvol_succ]
    repeat rw [clNeg_succ]
    repeat rw [clScale_succ]
    repeat rw [clAdd_succ]
    dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                 AssocRing.one_mul, AssocRing.mul_one, neg_zero_ring, neg_mul_ring,
                 mul_neg_ring, neg_neg_ring]
  repeat rw [CliffordAlg.clLiftAux_succ]
  repeat rw [clLiftAux_zero_dim]
  dsimp only [scalarToMat2Quat, finCastSucc, finLast, cl13Gens]
  -- Step-by-step evaluation of the 3 levels on Mat2 (QuatAlg F)
  have lvl2_eval : ∀ a00 a01 a10 a11 : F,
      (⟨CliffordAlg.ofScalar a00, 0, 0, CliffordAlg.ofScalar a00⟩ +
       (⟨0, quatI, quatI, 0⟩ : Mat2 (QuatAlg F)) *
         ⟨CliffordAlg.ofScalar a01, 0, 0, CliffordAlg.ofScalar a01⟩) +
      (⟨0, quatJ, quatJ, 0⟩ : Mat2 (QuatAlg F)) *
        (⟨CliffordAlg.ofScalar a10, 0, 0, CliffordAlg.ofScalar a10⟩ +
         (⟨0, quatI, quatI, 0⟩ : Mat2 (QuatAlg F)) *
           ⟨CliffordAlg.ofScalar a11, 0, 0, CliffordAlg.ofScalar a11⟩) =
      (⟨⟨((a00, 0), (0, a11))⟩, ⟨((0, a01), (a10, 0))⟩,
        ⟨((0, a01), (a10, 0))⟩, ⟨((a00, 0), (0, a11))⟩⟩ : Mat2 (QuatAlg F)) := by
    intro a00 a01 a10 a11
    have q_step1 : ∀ u v : F,
        (⟨CliffordAlg.ofScalar u, 0, 0, CliffordAlg.ofScalar u⟩ +
         (⟨0, quatI, quatI, 0⟩ : Mat2 (QuatAlg F)) *
           ⟨CliffordAlg.ofScalar v, 0, 0, CliffordAlg.ofScalar v⟩) =
        ⟨⟨((u, 0), (0, 0))⟩, ⟨((0, v), (0, 0))⟩,
         ⟨((0, v), (0, 0))⟩, ⟨((u, 0), (0, 0))⟩⟩ := by
      intro u v
      have hi_v : quatI * CliffordAlg.ofScalar v = ⟨((0, v), (0, 0))⟩ := by
        rw [CliffordAlg.mul_ofScalar_eq_smul]
        apply CliffordAlg.ext
        rw [CliffordAlg.raw_smul, hI_raw]
        repeat rw [clScale_succ]
        dsimp only [clScale]
        apply Prod.ext <;> apply Prod.ext <;>
          simp only [mul_zero_ring, AssocRing.mul_one]
      have hsc_u : (CliffordAlg.ofScalar u : QuatAlg F) = ⟨((u, 0), (0, 0))⟩ := by
        apply CliffordAlg.ext
        rw [CliffordAlg.raw_ofScalar]
        repeat rw [clOne_succ]
        repeat rw [clZero_succ]
        repeat rw [clScale_succ]
        dsimp only [clOne, clZero, clScale]
        apply Prod.ext <;> apply Prod.ext <;>
          simp only [mul_zero_ring, AssocRing.mul_one]
      apply Mat2.ext
      · show CliffordAlg.ofScalar u + (0 * CliffordAlg.ofScalar v + quatI * 0) = _
        rw [zero_mul_ring, mul_zero_ring, AssocRing.add_zero, AssocRing.add_zero, hsc_u]
      · show 0 + (0 * 0 + quatI * CliffordAlg.ofScalar v) = _
        rw [mul_zero_ring, AssocRing.zero_add, AssocRing.zero_add, hi_v]
      · show 0 + (quatI * CliffordAlg.ofScalar v + 0 * 0) = _
        rw [mul_zero_ring, AssocRing.add_zero, AssocRing.zero_add, hi_v]
      · show CliffordAlg.ofScalar u + (quatI * 0 + 0 * CliffordAlg.ofScalar v) = _
        rw [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.add_zero, hsc_u]
    rw [q_step1 a00 a01, q_step1 a10 a11]
    have hj_diag : quatJ * (⟨((0, a11), (0, 0))⟩ : QuatAlg F) = ⟨((0, 0), (0, a11))⟩ := by
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_mul, hJ_raw]
      repeat rw [clMul_succ]
      repeat rw [clInvol_succ]
      repeat rw [clNeg_succ]
      repeat rw [clScale_succ]
      repeat rw [clAdd_succ]
      dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                   AssocRing.one_mul, neg_zero_ring, mul_neg_ring, neg_mul_ring]
    have hj_off : quatJ * (⟨((a10, 0), (0, 0))⟩ : QuatAlg F) = ⟨((0, 0), (a10, 0))⟩ := by
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_mul, hJ_raw]
      repeat rw [clMul_succ]
      repeat rw [clInvol_succ]
      repeat rw [clNeg_succ]
      repeat rw [clScale_succ]
      repeat rw [clAdd_succ]
      dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                   AssocRing.one_mul, neg_zero_ring, mul_neg_ring, neg_mul_ring]
    apply Mat2.ext
    · show (⟨((a00, 0), (0, 0))⟩ : QuatAlg F) + (0 * _ + quatJ * ⟨((0, a11), (0, 0))⟩) = _
      rw [zero_mul_ring, AssocRing.zero_add, hj_diag]
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_add]
      repeat rw [clAdd_succ]
      dsimp only [clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [AssocRing.add_zero, AssocRing.zero_add]
    · show (⟨((0, a01), (0, 0))⟩ : QuatAlg F) + (0 * _ + quatJ * ⟨((a10, 0), (0, 0))⟩) = _
      rw [zero_mul_ring, AssocRing.zero_add, hj_off]
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_add]
      repeat rw [clAdd_succ]
      dsimp only [clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [AssocRing.add_zero, AssocRing.zero_add]
    · show (⟨((0, a01), (0, 0))⟩ : QuatAlg F) + (quatJ * ⟨((a10, 0), (0, 0))⟩ + 0 * _) = _
      rw [zero_mul_ring, AssocRing.add_zero, hj_off]
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_add]
      repeat rw [clAdd_succ]
      dsimp only [clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [AssocRing.add_zero, AssocRing.zero_add]
    · show (⟨((a00, 0), (0, 0))⟩ : QuatAlg F) + (quatJ * ⟨((0, a11), (0, 0))⟩ + 0 * _) = _
      rw [zero_mul_ring, AssocRing.add_zero, hj_diag]
      apply CliffordAlg.ext
      rw [CliffordAlg.raw_add]
      repeat rw [clAdd_succ]
      dsimp only [clAdd]
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [AssocRing.add_zero, AssocRing.zero_add]
  rw [lvl2_eval w000 w001 w010 w011, lvl2_eval w100 w101 w110 w111]
  have hk_Q : quatK * (⟨((0, w101), (w110, 0))⟩ : QuatAlg F) = ⟨((0, -w110), (w101, 0))⟩ := by
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_mul, hK_raw]
    repeat rw [clMul_succ]
    repeat rw [clInvol_succ]
    repeat rw [clNeg_succ]
    repeat rw [clScale_succ]
    repeat rw [clAdd_succ]
    dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                 AssocRing.one_mul, neg_zero_ring, neg_mul_ring, mul_neg_ring, neg_neg_ring]
  have hk_P : quatK * (⟨((w100, 0), (0, w111))⟩ : QuatAlg F) = ⟨((w111, 0), (0, -w100))⟩ := by
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_mul, hK_raw]
    repeat rw [clMul_succ]
    repeat rw [clInvol_succ]
    repeat rw [clNeg_succ]
    repeat rw [clScale_succ]
    repeat rw [clAdd_succ]
    dsimp only [clMul, clInvol, clNeg, clScale, clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [mul_zero_ring, zero_mul_ring, AssocRing.add_zero, AssocRing.zero_add,
                 AssocRing.one_mul, neg_zero_ring, neg_mul_ring, mul_neg_ring, neg_neg_ring]
  apply Mat2.ext
  · show (⟨((w000, 0), (0, w011))⟩ : QuatAlg F) + (0 * _ + quatK * ⟨((0, w101), (w110, 0))⟩) = _
    rw [zero_mul_ring, AssocRing.zero_add, hk_Q]
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_add]
    repeat rw [clAdd_succ]
    dsimp only [clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [AssocRing.add_zero, AssocRing.zero_add]
  · show (⟨((0, w001), (w010, 0))⟩ : QuatAlg F) + (0 * _ + quatK * ⟨((w100, 0), (0, w111))⟩) = _
    rw [zero_mul_ring, AssocRing.zero_add, hk_P]
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_add]
    repeat rw [clAdd_succ]
    dsimp only [clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [AssocRing.add_zero, AssocRing.zero_add]
  · show (⟨((0, w001), (w010, 0))⟩ : QuatAlg F) + (quatK * ⟨((w100, 0), (0, w111))⟩ + 0 * _) = _
    rw [zero_mul_ring, AssocRing.add_zero, hk_P]
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_add]
    repeat rw [clAdd_succ]
    dsimp only [clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [AssocRing.add_zero, AssocRing.zero_add]
  · show (⟨((w000, 0), (0, w011))⟩ : QuatAlg F) + (quatK * ⟨((0, w101), (w110, 0))⟩ + 0 * _) = _
    rw [zero_mul_ring, AssocRing.add_zero, hk_Q]
    apply CliffordAlg.ext
    rw [CliffordAlg.raw_add]
    repeat rw [clAdd_succ]
    dsimp only [clAdd]
    apply Prod.ext <;> apply Prod.ext <;>
      simp only [AssocRing.add_zero, AssocRing.zero_add]

theorem cl13ToMat2Quat_injective {x : CliffordAlg F 4 (Sig.toVec (confModel02 (F := F)).ambSig)}
    (hx : cl13ToMat2Quat.toFun x = 0) : x = 0 := by
  rcases x with ⟨⟨u, v⟩⟩
  -- Unfold level 4: lift (u, v) = lift3 u + G3 * lift3 v
  change CliffordAlg.clLiftAux scalarToMat2Quat cl13Gens (u, v) = 0 at hx
  unfold CliffordAlg.clLiftAux at hx
  rw [lift3_cl13_formula u, lift3_cl13_formula v] at hx
  let Pu : QuatAlg F := ⟨((u.1.1.1, -u.2.2.1), (u.2.1.2, u.1.2.2))⟩
  let Qu : QuatAlg F := ⟨((u.2.2.2, u.1.1.2), (u.1.2.1, -u.2.1.1))⟩
  let Pv : QuatAlg F := ⟨((v.1.1.1, -v.2.2.1), (v.2.1.2, v.1.2.2))⟩
  let Qv : QuatAlg F := ⟨((v.2.2.2, v.1.1.2), (v.1.2.1, -v.2.1.1))⟩
  have hG3 : cl13Gens (F := F) (finLast 3) = ⟨1, 0, 0, -1⟩ := rfl
  rw [hG3] at hx
  have hmul_G3 : (⟨1, 0, 0, -1⟩ : Mat2 (QuatAlg F)) * ⟨Pv, Qv, Qv, Pv⟩ = ⟨Pv, Qv, -Qv, -Pv⟩ := by
    apply Mat2.ext
    · show 1 * Pv + 0 * Qv = Pv; rw [AssocRing.one_mul, zero_mul_ring, AssocRing.add_zero]
    · show 1 * Qv + 0 * Pv = Qv; rw [AssocRing.one_mul, zero_mul_ring, AssocRing.add_zero]
    · show 0 * Pv + -1 * Qv = -Qv; rw [zero_mul_ring, neg_mul_ring, AssocRing.one_mul, AssocRing.zero_add]
    · show 0 * Qv + -1 * Pv = -Pv; rw [zero_mul_ring, neg_mul_ring, AssocRing.one_mul, AssocRing.zero_add]
  rw [hmul_G3] at hx
  have hP_sum : Pu + Pv = 0 := congrArg Mat2.m00 hx
  have hQ_sum : Qu + Qv = 0 := congrArg Mat2.m01 hx
  have hQ_diff : Qu - Qv = 0 := by
    rw [AssocRing.sub_eq_add_neg]; exact congrArg Mat2.m10 hx
  have hP_diff : Pu - Pv = 0 := by
    rw [AssocRing.sub_eq_add_neg]; exact congrArg Mat2.m11 hx
  -- In QuatAlg F, x + y = 0 ∧ x - y = 0 => x = 0 ∧ y = 0 componentwise!
  have quat_pair_zero : ∀ A B : QuatAlg F, A + B = 0 → A - B = 0 → A = 0 ∧ B = 0 := by
    intro A B hs hd
    rcases A with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩⟩
    rcases B with ⟨⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩⟩
    have pair0 : ∀ x y : F, x + y = 0 → x + -y = 0 → x = 0 ∧ y = 0 := by
      intro x y hxy hxny
      apply linear_pair_eq_zero hxy
      rw [AssocRing.sub_eq_add_neg]
      exact hxny
    have c1 := pair0 a1 b1
      (congrArg (fun q : QuatAlg F => q.raw.1.1) hs)
      (congrArg (fun q : QuatAlg F => q.raw.1.1) hd)
    have c2 := pair0 a2 b2
      (congrArg (fun q : QuatAlg F => q.raw.1.2) hs)
      (congrArg (fun q : QuatAlg F => q.raw.1.2) hd)
    have c3 := pair0 a3 b3
      (congrArg (fun q : QuatAlg F => q.raw.2.1) hs)
      (congrArg (fun q : QuatAlg F => q.raw.2.1) hd)
    have c4 := pair0 a4 b4
      (congrArg (fun q : QuatAlg F => q.raw.2.2) hs)
      (congrArg (fun q : QuatAlg F => q.raw.2.2) hd)
    refine ⟨?_, ?_⟩
    · apply CliffordAlg.ext; rw [c1.1, c2.1, c3.1, c4.1]; rfl
    · apply CliffordAlg.ext; rw [c1.2, c2.2, c3.2, c4.2]; rfl
  rcases quat_pair_zero Pu Pv hP_sum hP_diff with ⟨hPu0, hPv0⟩
  rcases quat_pair_zero Qu Qv hQ_sum hQ_diff with ⟨hQu0, hQv0⟩
  have carrier3_zero : ∀ w : CliffordCarrier F 3,
      (⟨((w.1.1.1, -w.2.2.1), (w.2.1.2, w.1.2.2))⟩ : QuatAlg F) = 0 →
      (⟨((w.2.2.2, w.1.1.2), (w.1.2.1, -w.2.1.1))⟩ : QuatAlg F) = 0 →
      w = clZero 3 := by
    intro w hp hq
    rcases w with ⟨⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩, ⟨⟨b0, b1⟩, ⟨b2, b3⟩⟩⟩
    have z_a0 : a0 = 0 := congrArg (fun q : QuatAlg F => q.raw.1.1) hp
    have z_b2 : b2 = 0 := by
      have p : -b2 = 0 := congrArg (fun q : QuatAlg F => q.raw.1.2) hp
      rw [← neg_neg_ring b2, p, neg_zero_ring]
    have z_b1 : b1 = 0 := congrArg (fun q : QuatAlg F => q.raw.2.1) hp
    have z_a3 : a3 = 0 := congrArg (fun q : QuatAlg F => q.raw.2.2) hp
    have z_b3 : b3 = 0 := congrArg (fun q : QuatAlg F => q.raw.1.1) hq
    have z_a1 : a1 = 0 := congrArg (fun q : QuatAlg F => q.raw.1.2) hq
    have z_a2 : a2 = 0 := congrArg (fun q : QuatAlg F => q.raw.2.1) hq
    have z_b0 : b0 = 0 := by
      have p : -b0 = 0 := congrArg (fun q : QuatAlg F => q.raw.2.2) hq
      rw [← neg_neg_ring b0, p, neg_zero_ring]
    subst z_a0; subst z_a1; subst z_a2; subst z_a3
    subst z_b0; subst z_b1; subst z_b2; subst z_b3
    rfl
  apply CliffordAlg.ext
  exact Prod.ext (carrier3_zero u hPu0 hQu0) (carrier3_zero v hPv0 hQv0)

/-- `Cl_{1,3}(F)` has Pierce capacity at most 2 (cannot have 3 orthogonal nonzero idempotents)! -/
theorem cl13_no_three_orthogonal_idempotents :
    ¬ HasOrthogonalIdempotents
        (CliffordAlg F 4 (Sig.toVec (confModel02 (F := F)).ambSig)) 3 := by
  rintro ⟨p, hp, horth⟩
  apply Mat2.no_three_orthogonal_idempotents_of_divRing (R := QuatAlg F) quat_is_division_ring
  refine ⟨fun i => cl13ToMat2Quat.toFun (p i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · intro h0
      exact (hp i).1 (cl13ToMat2Quat_injective h0)
    · rw [← cl13ToMat2Quat.map_mul, (hp i).2]
  · intro i j hij
    rw [← cl13ToMat2Quat.map_mul, horth i j hij, cl13ToMat2Quat.map_zero]

/-- Corollary: `Cl_{3,1}(F)` ALSO has 3 mutually orthogonal nonzero idempotents, hence `Cl_{3,1}(F) ≇ Cl_{1,3}(F)`! -/
theorem cl31_has_three_orthogonal_idempotents :
    HasOrthogonalIdempotents
      (CliffordAlg F 4 (Sig.toVec (confModel20 (F := F)).ambSig)) 3 := by
  rcases cl31_has_four_orthogonal_idempotents (F := F) with ⟨p, hp, horth⟩
  refine ⟨fun i : Fin 3 => p (finCastSucc i), fun i => hp (finCastSucc i), ?_⟩
  intro i j hij
  exact horth (finCastSucc i) (finCastSucc j) (fun hc => hij (finCastSucc_inj hc))

/-- Genuine Unital Ring Non-Isomorphism in Even Dimension: `Cl_{3,1}(F) ≇ Cl_{1,3}(F)`! -/
theorem clifford_31_not_iso_13 :
    ¬ Nonempty (RingIso
        (CliffordAlg F 4 (Sig.toVec (confModel20 (F := F)).ambSig))
        (CliffordAlg F 4 (Sig.toVec (confModel02 (F := F)).ambSig))) := by
  rintro ⟨e⟩
  exact cl13_no_three_orthogonal_idempotents (F := F)
    (e.preserve_orthogonalIdempotents (cl31_has_three_orthogonal_idempotents (F := F)))

end EvenLorentzianSeparationPartD

/-! ### Master Theorems for Conjecture 00000007620 -/

/-- Universal resolution of Conjecture 00000007620 over ANY formally real field `F`
    (simultaneously encompassing `ℝ` and `ℚ`):
    There exist two genuine conformal horosphere models `M₁, M₂` realized by an explicit
    opposite-signature pair `(1, 0)` vs `(0, 1)` (ambient `(2, 1)` vs `(1, 2)`) with:
    1. Distinct conformal null-cone embeddings (`M₁.embed ≠ M₂.embed`, projectively disjoint on `F¹ \ {0}`),
    2. Literally identical ambient orthogonal isometry groups (`O(Q₁) = O(Q₂)`), Lie algebras,
       and Layer-1 isometry-group eigenvalue & trace spectra,
    3. Strictly separated Layer-2 Clifford spectra (central idempotent & pseudoscalar spectra)
       and genuinely non-isomorphic Clifford algebras (`Cl(Q₁) ≇ Cl(Q₂)`). -/
theorem conjecture_00000007620_universal {F : Type u} [FormallyRealField F] :
    ∃ (d : Nat) (M₁ M₂ : ConformalModel F d),
      signatureCount M₁.baseSig ≠ signatureCount M₂.baseSig ∧
      signatureCount M₁.ambSig ≠ signatureCount M₂.ambSig ∧
      M₁.embed ≠ M₂.embed ∧
      (∀ x : Vec F d, x ≠ zeroVec d → ∀ c : F, M₁.embed x ≠ smulVec c (M₂.embed x)) ∧
      M₁.infty = M₂.infty ∧
      InFullOrthGroup (F := F) M₁.ambSig = InFullOrthGroup (F := F) M₂.ambSig ∧
      InOrthLieAlg (F := F) M₁.ambSig = InOrthLieAlg (F := F) M₂.ambSig ∧
      InGroupEigenSpectrum (F := F) M₁.ambSig = InGroupEigenSpectrum (F := F) M₂.ambSig ∧
      InGroupScalarSpectrum (F := F) M₁.ambSig = InGroupScalarSpectrum (F := F) M₂.ambSig ∧
      InGroupTraceSpectrum (F := F) M₁.ambSig = InGroupTraceSpectrum (F := F) M₂.ambSig ∧
      (HasNontrivialCentralIdem (CliffordAlg F (d + 2) (Sig.toVec M₁.ambSig)) ∧
       ¬ HasNontrivialCentralIdem (CliffordAlg F (d + 2) (Sig.toVec M₂.ambSig))) ∧
      ¬ Nonempty (RingIso
          (CliffordAlg F (d + 2) (Sig.toVec M₁.ambSig))
          (CliffordAlg F (d + 2) (Sig.toVec M₂.ambSig))) := by
  refine ⟨1, confModel10 (F := F), confModel01 (F := F),
    ?_, ?_, conformal_embeddings_ne sig10,
    fun x hx c => conformal_embeddings_proj_disjoint sig10 hx c,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, clifford_21_not_iso_12 (F := F)⟩
  · rw [confModel10_signatures.1, confModel01_signatures.1]; decide
  · rw [confModel10_signatures.2, confModel01_signatures.2]; decide
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, fullOrthGroup_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, orthLieAlg_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, groupEigenSpectrum_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, groupScalarSpectrum_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, groupTraceSpectrum_flip_eq]
  · exact ⟨(cl21_has_nontrivial_central_spectra (F := F)).2,
           (cl12_no_nontrivial_central_spectra (F := F)).2⟩

/-- Unconditional concrete resolution of Conjecture 00000007620 (zero hypotheses),
    instantiated over the exact rational field `RatField`. -/
theorem conjecture_00000007620 :
    ∃ (d : Nat) (M₁ M₂ : ConformalModel RatField d),
      signatureCount M₁.baseSig = (1, 0) ∧
      signatureCount M₂.baseSig = (0, 1) ∧
      signatureCount M₁.ambSig = (2, 1) ∧
      signatureCount M₂.ambSig = (1, 2) ∧
      M₁.embed ≠ M₂.embed ∧
      (∀ x : Vec RatField d, x ≠ zeroVec d → ∀ c : RatField,
        M₁.embed x ≠ smulVec c (M₂.embed x)) ∧
      InFullOrthGroup (F := RatField) M₁.ambSig = InFullOrthGroup (F := RatField) M₂.ambSig ∧
      InGroupEigenSpectrum (F := RatField) M₁.ambSig =
        InGroupEigenSpectrum (F := RatField) M₂.ambSig ∧
      InGroupTraceSpectrum (F := RatField) M₁.ambSig =
        InGroupTraceSpectrum (F := RatField) M₂.ambSig ∧
      (HasNontrivialCentralIdem (CliffordAlg RatField (d + 2) (Sig.toVec M₁.ambSig)) ∧
       ¬ HasNontrivialCentralIdem (CliffordAlg RatField (d + 2) (Sig.toVec M₂.ambSig))) ∧
      ¬ Nonempty (RingIso
          (CliffordAlg RatField (d + 2) (Sig.toVec M₁.ambSig))
          (CliffordAlg RatField (d + 2) (Sig.toVec M₂.ambSig))) := by
  refine ⟨1, confModel10 (F := RatField), confModel01 (F := RatField),
    rfl, rfl, rfl, rfl,
    conformal_embeddings_ne sig10,
    fun x hx c => conformal_embeddings_proj_disjoint sig10 hx c,
    ?_, ?_, ?_,
    ⟨(cl21_has_nontrivial_central_spectra (F := RatField)).2,
     (cl12_no_nontrivial_central_spectra (F := RatField)).2⟩,
    clifford_21_not_iso_12 (F := RatField)⟩
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, fullOrthGroup_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, groupEigenSpectrum_flip_eq]
  · rw [confModel10, confModel01, dualConformalModel_ambSig_eq_flip, groupTraceSpectrum_flip_eq]

/-- Even-dimensional Lorentzian Conformal Separation Theorem (unconditional):
    Conformal models of `(2, 0)` and `(0, 2)` in signatures `(3, 1)` and `(1, 3)` share
    the exact same Lorentzian conformal isometry group `O(3,1) = O(1,3)` and group spectra,
    yet have distinct Pierce/spinor Clifford spectra (capacity 4 vs ≤ 2) and non-isomorphic
    Clifford algebras `Cl_{3,1}(ℚ) ≇ Cl_{1,3}(ℚ)` even though both centers are trivial! -/
theorem conjecture_00000007620_lorentzian :
    ∃ (M₁ M₂ : ConformalModel RatField 2),
      signatureCount M₁.baseSig = (2, 0) ∧
      signatureCount M₂.baseSig = (0, 2) ∧
      signatureCount M₁.ambSig = (3, 1) ∧
      signatureCount M₂.ambSig = (1, 3) ∧
      M₁.embed ≠ M₂.embed ∧
      InFullOrthGroup (F := RatField) M₁.ambSig = InFullOrthGroup (F := RatField) M₂.ambSig ∧
      InGroupEigenSpectrum (F := RatField) M₁.ambSig =
        InGroupEigenSpectrum (F := RatField) M₂.ambSig ∧
      (HasOrthogonalIdempotents (CliffordAlg RatField 4 (Sig.toVec M₁.ambSig)) 4 ∧
       ¬ HasOrthogonalIdempotents (CliffordAlg RatField 4 (Sig.toVec M₂.ambSig)) 3) ∧
      ¬ Nonempty (RingIso
          (CliffordAlg RatField 4 (Sig.toVec M₁.ambSig))
          (CliffordAlg RatField 4 (Sig.toVec M₂.ambSig))) := by
  refine ⟨confModel20 (F := RatField), confModel02 (F := RatField),
    rfl, rfl, rfl, rfl,
    conformal_embeddings_ne sig20,
    ?_, ?_,
    ⟨cl31_has_four_orthogonal_idempotents (F := RatField),
     cl13_no_three_orthogonal_idempotents (F := RatField)⟩,
    clifford_31_not_iso_13 (F := RatField)⟩
  · rw [confModel20, confModel02, dualConformalModel_ambSig_eq_flip, fullOrthGroup_flip_eq]
  · rw [confModel20, confModel02, dualConformalModel_ambSig_eq_flip, groupEigenSpectrum_flip_eq]

end Conjecture00000007620

