/-
  Conjecture 00000007610 — Main Separation Theorems Across All Three Field-Extension Regimes
  and the Quadratically-Closed Obstruction Theorem.
-/

import Conjecture00000007610.Algebra
import Conjecture00000007610.Fields
import Conjecture00000007610.Clifford
import Conjecture00000007610.Modules

namespace Conjecture00000007610

universe u

/-- 1-tuple (d0) : Fin 1 → α. -/
def vec1 {α : Type u} (a : α) : Fin 1 → α := fun _ => a

/-- 2-tuple (a, b) : Fin 2 → α. -/
def vec2 {α : Type u} (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

/-- High-priority coordinate `AddCommGrp` shortcut so `(Fin m → K)` resolves without
    traversing unconstrained module coercions. -/
local instance (priority := 2000) finAddCommGrpPrio (K : Type u) [FieldStructure K] (m : Nat) :
    AddCommGrp (Fin m → K) :=
  (finVecSpace K m).toAddCommGrp

/-! ### Section 1: General Structure of `Cl(K^1, (d0))` and `Cl(K^2, (1, -1))` -/

/-- Canonical K-algebra isomorphism `Cl(K^1, (d0)) ≃ₐ[K] QuadExt K d0`. -/
def cl1IsoQuadExt (K : Type u) [FieldStructure K] (d0 : K) :
    AlgIso K (Clifford K 1 (vec1 d0)) (QuadExt K d0) where
  toFun x := ⟨x.raw.1, x.raw.2⟩
  invFun z := ⟨(z.re, z.im)⟩
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_smul _ _ := rfl
  left_inv _ := Clifford.ext (Prod.ext rfl rfl)
  right_inv _ := QuadExt.ext rfl rfl

/-- QuadExt K d0 has exact K-dimension 2. -/
def quadExtCoordIso (K : Type u) [FieldStructure K] (d0 : K) :
    KLinearIso K (Fin 2 → K) (QuadExt K d0) :=
  KLinearIso.trans (cliffordCoordIso K 1 (vec1 d0)) (cl1IsoQuadExt K d0).toKLinearIso

theorem quadExt_hasKDim (K : Type u) [FieldStructure K] (d0 : K) :
    HasKDim K (QuadExt K d0) 2 :=
  ⟨quadExtCoordIso K d0⟩

/-- Field K over itself has exact K-dimension 1. -/
def fieldSelfCoordIso (K : Type u) [FieldStructure K] :
    KLinearIso K (Fin 1 → K) K where
  toFun f := f ⟨0, by omega⟩
  invFun c := fun _ => c
  map_add _ _ := rfl
  map_smul _ _ := rfl
  left_inv f := by
    funext i
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hi]
  right_inv _ := rfl

theorem field_self_hasKDim (K : Type u) [FieldStructure K] : HasKDim K K 1 :=
  ⟨fieldSelfCoordIso K⟩

/-- Center of `Cl(K^1, (d0))` is K-algebra isomorphic to `QuadExt K d0`. -/
def cl1CenterIsoQuadExt (K : Type u) [FieldStructure K] (d0 : K) :
    AlgIso K (Center (Clifford K 1 (vec1 d0))) (QuadExt K d0) :=
  AlgIso.trans
    (AlgIso.centerIso (cl1IsoQuadExt K d0))
    (commCenterAlgIso (QuadExt K d0) QuadExt.mul_comm)

/-- Whenever `d0` is a non-square in `K`, `Cl(K^1, (d0))` has irreducible-representation
    spectrum `(1; [2])` over `K` (unique simple module class, of exact K-dimension 2). -/
theorem cl1_nonSquare_hasUniqueSimpleModuleOfDim
    (K : Type u) [FieldStructure K] (d0 : K) (hd0 : NonSquare d0) :
    HasUniqueSimpleModuleOfDim K (Clifford K 1 (vec1 d0)) 2 := by
  let instFL : FieldStructure (QuadExt K d0) := quadExtFieldStructure K d0 hd0
  rcases @field_simple_module_unique (QuadExt K d0) instFL with ⟨hSimple, hUniq⟩
  have hQuad : HasUniqueSimpleModuleOfDim K (QuadExt K d0) 2 :=
    ⟨⟨QuadExt K d0, regularKModule K (QuadExt K d0), hSimple, quadExt_hasKDim K d0, hUniq⟩⟩
  exact HasUniqueSimpleModuleOfDim.ofAlgIso (cl1IsoQuadExt K d0) hQuad

section SplitCl11

variable {K : Type u} [FieldStructure K]

/-- Explicit spinor Clifford map K^2 → M_2(K):
    v = (v0, v1) ↦ [[v0, v1], [-v1, -v0]], satisfying f(v)^2 = (v0^2 - v1^2) I_2. -/
def spinorMap (v : Fin 2 → K) : Mat2 K :=
  let v0 := v ⟨0, by omega⟩
  let v1 := v ⟨1, by omega⟩
  ⟨v0, v1, -v1, -v0⟩

theorem spinorMap_isClifford : IsCliffordMap (vec2 (1 : K) (-1)) (spinorMap (K := K)) where
  map_add u w := Mat2.ext rfl rfl
    (neg_add_grp (u ⟨1, by omega⟩) (w ⟨1, by omega⟩))
    (neg_add_grp (u ⟨0, by omega⟩) (w ⟨0, by omega⟩))
  map_smul c u := Mat2.ext rfl rfl
    (mul_neg_ring c (u ⟨1, by omega⟩)).symm
    (mul_neg_ring c (u ⟨0, by omega⟩)).symm
  map_sq v := by
    let v0 := v ⟨0, by omega⟩
    let v1 := v ⟨1, by omega⟩
    have hq : quadForm (vec2 (1 : K) (-1)) v = v0 * v0 + -(v1 * v1) := by
      change ((0 : K) + 1 * (v0 * v0)) + (-1 : K) * (v1 * v1) = v0 * v0 + -(v1 * v1)
      rw [UnitalRing.one_mul, AddCommGrp.zero_add, neg_mul_ring, UnitalRing.one_mul]
    rw [hq]
    apply Mat2.ext
    · change v0 * v0 + v1 * (-v1) = (v0 * v0 + -(v1 * v1)) * 1
      rw [mul_neg_ring, UnitalRing.mul_one]
    · change v0 * v1 + v1 * (-v0) = (v0 * v0 + -(v1 * v1)) * 0
      rw [mul_neg_ring, FieldStructure.mul_comm v1 v0, add_neg_cancel_grp, mul_zero_ring]
    · change (-v1) * v0 + (-v0) * (-v1) = (v0 * v0 + -(v1 * v1)) * 0
      rw [neg_mul_ring, neg_mul_neg_ring, FieldStructure.mul_comm v1 v0,
          AddCommGrp.neg_add_cancel, mul_zero_ring]
    · change (-v1) * v1 + (-v0) * (-v0) = (v0 * v0 + -(v1 * v1)) * 1
      rw [neg_mul_ring, neg_mul_neg_ring, AddCommGrp.add_comm, UnitalRing.mul_one]

/-- Forward K-algebra homomorphism `Cl(K^2, (1, -1)) → M_2(K)` obtained from the
    Universal Property of Clifford Algebras! -/
def cl11ToMat2Hom (K : Type u) [FieldStructure K] :
    AlgHom K (Clifford K 2 (vec2 1 (-1))) (Mat2 K) :=
  Clifford.lift (vec2 (1 : K) (-1)) spinorMap spinorMap_isClifford

/-- Explicit evaluation formula of `cl11ToMat2Hom` on `((a, b), (c, d))`. -/
theorem cl11ToMat2Hom_eval (a b c d : K) :
    (cl11ToMat2Hom K).toFun ⟨((a, b), (c, d))⟩ =
      ⟨a + b, c + d, -c + d, a + -b⟩ := by
  change clLiftRaw 2 spinorMap ((a, b), (c, d)) = ⟨a + b, c + d, -c + d, a + -b⟩
  dsimp [clLiftRaw]
  have he0 : spinorMap (finSnoc (finSnoc (0 : Fin 0 → K) (1 : K)) (0 : K)) =
      (⟨1, 0, 0, -1⟩ : Mat2 K) :=
    Mat2.ext rfl rfl neg_zero_grp rfl
  have he1 : spinorMap (finSnoc (0 : Fin 1 → K) (1 : K)) =
      (⟨0, 1, -1, 0⟩ : Mat2 K) :=
    Mat2.ext rfl rfl rfl neg_zero_grp
  rw [he0, he1]
  have he01 : (⟨1, 0, 0, -1⟩ : Mat2 K) * ⟨0, 1, -1, 0⟩ = ⟨0, 1, 1, 0⟩ := by
    apply Mat2.ext
    · change (1 : K) * 0 + (0 : K) * (-1) = 0
      rw [mul_zero_ring, zero_mul_ring, add_zero_grp]
    · change (1 : K) * 1 + (0 : K) * 0 = 1
      rw [UnitalRing.one_mul, mul_zero_ring, add_zero_grp]
    · change (0 : K) * 0 + (-1 : K) * (-1) = 1
      rw [mul_zero_ring, neg_mul_neg_ring, UnitalRing.one_mul, AddCommGrp.zero_add]
    · change (0 : K) * 1 + (-1 : K) * 0 = 0
      rw [zero_mul_ring, mul_zero_ring, add_zero_grp]
  unfold algebraMap
  rw [KAlgebra.smul_mul_assoc b 1, UnitalRing.one_mul,
      KAlgebra.smul_mul_assoc d 1, UnitalRing.one_mul]
  rw [UnitalRing.right_distrib, KAlgebra.smul_mul_assoc c 1, UnitalRing.one_mul,
      KAlgebra.smul_mul_assoc d, he01]
  apply Mat2.ext
  · change (a * 1 + b * 1) + (c * 0 + d * 0) = a + b
    rw [UnitalRing.mul_one, UnitalRing.mul_one, mul_zero_ring, mul_zero_ring,
        add_zero_grp, add_zero_grp]
  · change (a * 0 + b * 0) + (c * 1 + d * 1) = c + d
    rw [mul_zero_ring, mul_zero_ring, UnitalRing.mul_one, UnitalRing.mul_one,
        add_zero_grp, AddCommGrp.zero_add]
  · change (a * 0 + b * 0) + (c * (-1) + d * 1) = -c + d
    rw [mul_zero_ring, mul_zero_ring, mul_neg_ring, UnitalRing.mul_one, UnitalRing.mul_one,
        add_zero_grp, AddCommGrp.zero_add]
  · change (a * 1 + b * (-1)) + (c * 0 + d * 0) = a + -b
    rw [UnitalRing.mul_one, mul_neg_ring, UnitalRing.mul_one, mul_zero_ring, mul_zero_ring,
        add_zero_grp, add_zero_grp]

private theorem half_sum_add (h2 : (1 : K) + 1 ≠ 0) (x y : K) :
    let half := FieldStructure.inv ((1 : K) + 1)
    half * ((x + y) + (x + -y)) = x := by
  intro half
  have hsum : (x + y) + (x + -y) = ((1 : K) + 1) * x := by
    calc
      (x + y) + (x + -y) = x + (y + (x + -y)) := AddCommGrp.add_assoc x y _
      _ = x + ((x + -y) + y) := by rw [AddCommGrp.add_comm y (x + -y)]
      _ = x + (x + (-y + y)) := by rw [AddCommGrp.add_assoc x (-y) y]
      _ = x + (x + 0) := by rw [AddCommGrp.neg_add_cancel]
      _ = x + x := by rw [add_zero_grp]
      _ = 1 * x + 1 * x := by rw [UnitalRing.one_mul]
      _ = ((1 : K) + 1) * x := (UnitalRing.right_distrib 1 1 x).symm
  rw [hsum, ← UnitalRing.mul_assoc, inv_mul_cancel_field h2, UnitalRing.one_mul]

private theorem half_sum_sub (h2 : (1 : K) + 1 ≠ 0) (x y : K) :
    let half := FieldStructure.inv ((1 : K) + 1)
    half * ((x + y) + -(x + -y)) = y := by
  intro half
  have hdiff : (x + y) + -(x + -y) = ((1 : K) + 1) * y := by
    rw [neg_add_grp, neg_neg_grp]
    calc
      (x + y) + (-x + y) = y + x + (-x + y) := by rw [AddCommGrp.add_comm x y]
      _ = y + (x + (-x + y)) := AddCommGrp.add_assoc y x _
      _ = y + ((x + -x) + y) := by rw [← AddCommGrp.add_assoc x (-x) y]
      _ = y + (0 + y) := by rw [add_neg_cancel_grp]
      _ = y + y := by rw [AddCommGrp.zero_add]
      _ = 1 * y + 1 * y := by rw [UnitalRing.one_mul]
      _ = ((1 : K) + 1) * y := (UnitalRing.right_distrib 1 1 y).symm
  rw [hdiff, ← UnitalRing.mul_assoc, inv_mul_cancel_field h2, UnitalRing.one_mul]

private theorem add_half_pair (h2 : (1 : K) + 1 ≠ 0) (p q : K) :
    let half := FieldStructure.inv ((1 : K) + 1)
    half * (p + q) + half * (p + -q) = p := by
  intro half
  rw [← UnitalRing.left_distrib]
  exact half_sum_add h2 p q

private theorem sub_half_pair (h2 : (1 : K) + 1 ≠ 0) (p q : K) :
    let half := FieldStructure.inv ((1 : K) + 1)
    half * (p + q) + -(half * (p + -q)) = q := by
  intro half
  rw [← mul_neg_ring, ← UnitalRing.left_distrib]
  exact half_sum_sub h2 p q

/-- Canonical K-algebra isomorphism `Cl(K^2, (1, -1)) ≃ₐ[K] M_2(K)` for any field K
    with `char(K) ≠ 2`. -/
def cl11IsoMat2 (K : Type u) [FieldStructure K] (h2 : (1 : K) + 1 ≠ 0) :
    AlgIso K (Clifford K 2 (vec2 1 (-1))) (Mat2 K) where
  toAlgHom := cl11ToMat2Hom K
  invFun M :=
    let half := FieldStructure.inv ((1 : K) + 1)
    ⟨((half * (M.m11 + M.m22), half * (M.m11 + -M.m22)),
      (half * (M.m12 + -M.m21), half * (M.m12 + M.m21)))⟩
  left_inv x := by
    rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
    change _ = (⟨((a, b), (c, d))⟩ : Clifford K 2 (vec2 1 (-1)))
    have hev := cl11ToMat2Hom_eval a b c d
    change (cl11ToMat2Hom K).toFun ⟨((a, b), (c, d))⟩ = _ at hev
    rw [hev]
    apply Clifford.ext
    apply Prod.ext
    · apply Prod.ext
      · exact half_sum_add h2 a b
      · exact half_sum_sub h2 a b
    · apply Prod.ext
      · -- half * ((c + d) + -(-c + d)) = c
        have h : (c + d) + -(-c + d) = (d + c) + -(d + -c) := by
          rw [AddCommGrp.add_comm c d, AddCommGrp.add_comm (-c) d]
        dsimp
        rw [h]
        exact half_sum_sub h2 d c
      · -- half * ((c + d) + (-c + d)) = d
        have h : (c + d) + (-c + d) = (d + c) + (d + -c) := by
          rw [AddCommGrp.add_comm c d, AddCommGrp.add_comm (-c) d]
        dsimp
        rw [h]
        exact half_sum_add h2 d c
  right_inv M := by
    let half := FieldStructure.inv ((1 : K) + 1)
    change (cl11ToMat2Hom K).toFun
      ⟨((half * (M.m11 + M.m22), half * (M.m11 + -M.m22)),
        (half * (M.m12 + -M.m21), half * (M.m12 + M.m21)))⟩ = M
    rw [cl11ToMat2Hom_eval]
    apply Mat2.ext
    · exact add_half_pair h2 M.m11 M.m22
    · -- half * (m12 - m21) + half * (m12 + m21) = m12
      dsimp
      rw [AddCommGrp.add_comm (half * (M.m12 + -M.m21))]
      exact add_half_pair h2 M.m12 M.m21
    · -- -(half * (m12 - m21)) + half * (m12 + m21) = m21
      dsimp
      rw [AddCommGrp.add_comm (-(half * (M.m12 + -M.m21)))]
      exact sub_half_pair h2 M.m12 M.m21
    · exact sub_half_pair h2 M.m11 M.m22

/-- Center of `Cl(K^2, (1, -1))` is canonically K-algebra isomorphic to `K`. -/
def cl11CenterIsoField (K : Type u) [FieldStructure K] (h2 : (1 : K) + 1 ≠ 0) :
    AlgIso K (Center (Clifford K 2 (vec2 1 (-1)))) K :=
  AlgIso.trans (AlgIso.centerIso (cl11IsoMat2 K h2)) (mat2CenterAlgIso K)

/-- `Cl(K^2, (1, -1))` has irreducible-representation spectrum `(1; [2])` over `K`. -/
theorem cl11_hasUniqueSimpleModuleOfDim (K : Type u) [FieldStructure K]
    (h2 : (1 : K) + 1 ≠ 0) :
    HasUniqueSimpleModuleOfDim K (Clifford K 2 (vec2 1 (-1))) 2 :=
  HasUniqueSimpleModuleOfDim.ofAlgIso (cl11IsoMat2 K h2) (mat2_hasUniqueSimpleModuleOfDim K)

end SplitCl11

/-! ### Section 2: Characteristic != 2 for Exact `RatQ` and `Qi` -/

theorem ratQ_two_ne_zero : (1 : RatQ) + 1 ≠ 0 := by
  intro h
  have heq := RatQ.exact h
  unfold PreRat.Rel PreRat.add at heq
  dsimp at heq
  omega

theorem qi_two_ne_zero : (1 : Qi) + 1 ≠ 0 := by
  intro h
  exact ratQ_two_ne_zero (congrArg QuadExt.re h)

/-! ### Section 3: Main Theorem I — Fixed-Base-Field Separation (`Cl_{1,1}(Q)` vs `Cl_{0,1}(Q)`) -/

/-- `A1_Q = Cl_{1,1}(Q) = Cl(Q^2, (1, -1))` (4-dimensional split Clifford algebra over Q). -/
abbrev A1_Q : Type := Clifford RatQ 2 (vec2 1 (-1))

/-- `A2_Q = Cl_{0,1}(Q) = Cl(Q^1, (-1))` (2-dimensional Clifford algebra over Q). -/
abbrev A2_Q : Type := Clifford RatQ 1 (vec1 (-1))

/-- **Main Theorem I (Fixed Base Field Q, Center Field-Extension Pair `(Q, Q(i))`)**:
    `A1_Q = Cl_{1,1}(Q)` and `A2_Q = Cl_{0,1}(Q)` have the **exact same** irreducible
    Q-representation spectrum `(1; [2])` (each possesses a unique isomorphism class of
    simple left modules, of exact Q-dimension 2), while their genuine ring-theoretic centers
    form the explicit quadratic field-extension pair `Z(A1_Q) ≃ₐ[Q] Q` and `Z(A2_Q) ≃ₐ[Q] Q(i)`,
    which are non-isomorphic BOTH as Q-algebras (dim_Q 1 ≠ dim_Q 2) AND as abstract unital rings! -/
theorem regime_I_separation :
    HasUniqueSimpleModuleOfDim RatQ A1_Q 2 ∧
    HasUniqueSimpleModuleOfDim RatQ A2_Q 2 ∧
    Nonempty (AlgIso RatQ (Center A1_Q) RatQ) ∧
    Nonempty (AlgIso RatQ (Center A2_Q) Qi) ∧
    HasKDim RatQ (Center A1_Q) 1 ∧
    HasKDim RatQ (Center A2_Q) 2 ∧
    ¬ Nonempty (AlgIso RatQ (Center A1_Q) (Center A2_Q)) ∧
    ¬ Nonempty (RingIso (Center A1_Q) (Center A2_Q)) := by
  have hRep1 : HasUniqueSimpleModuleOfDim RatQ A1_Q 2 :=
    cl11_hasUniqueSimpleModuleOfDim RatQ ratQ_two_ne_zero
  have hRep2 : HasUniqueSimpleModuleOfDim RatQ A2_Q 2 :=
    cl1_nonSquare_hasUniqueSimpleModuleOfDim RatQ (-1) ratQ_nonSquare_neg_one
  let eZ1 : AlgIso RatQ (Center A1_Q) RatQ := cl11CenterIsoField RatQ ratQ_two_ne_zero
  let eZ2 : AlgIso RatQ (Center A2_Q) Qi := cl1CenterIsoQuadExt RatQ (-1)
  have hDim1 : HasKDim RatQ (Center A1_Q) 1 :=
    ⟨KLinearIso.trans (fieldSelfCoordIso RatQ) eZ1.symm.toKLinearIso⟩
  have hDim2 : HasKDim RatQ (Center A2_Q) 2 :=
    ⟨KLinearIso.trans (quadExtCoordIso RatQ (-1)) eZ2.symm.toKLinearIso⟩
  have hNoRing : ¬ Nonempty (RingIso (Center A1_Q) (Center A2_Q)) := by
    intro ⟨eRing⟩
    -- Compose Qi ≃ Center A2_Q ≃ Center A1_Q ≃ RatQ to get RingHom Qi RatQ, impossible!
    let isoQiRat : RingIso Qi RatQ :=
      RingIso.trans eZ2.symm.toRingIso (RingIso.trans eRing.symm eZ1.toRingIso)
    exact no_ringHom_qi_to_ratQ ⟨isoQiRat.toRingHom⟩
  have hNoAlg : ¬ Nonempty (AlgIso RatQ (Center A1_Q) (Center A2_Q)) := by
    intro ⟨eAlg⟩
    exact hNoRing ⟨eAlg.toRingIso⟩
  exact ⟨hRep1, hRep2, ⟨eZ1⟩, ⟨eZ2⟩, hDim1, hDim2, hNoAlg, hNoRing⟩

/-! ### Section 4: Main Theorem II — Same-Dimension Separation (`Cl(Q^1, (2))` vs `Cl(Q^1, (-1))`) -/

/-- `C1_Q = Cl(Q^1, (2))` (1-generator, 2-dimensional Clifford algebra over Q). -/
abbrev C1_Q : Type := Clifford RatQ 1 (vec1 ((1 : RatQ) + 1))

/-- `C2_Q = Cl(Q^1, (-1))` (1-generator, 2-dimensional Clifford algebra over Q). -/
abbrev C2_Q : Type := Clifford RatQ 1 (vec1 (-1))

/-- **Main Theorem II (Same Generator Dimension n = 1 & Same Algebra Dimension 2)**:
    Even restricting to Clifford algebras on the **exact same** 1-dimensional vector space `Q^1`
    (both of algebra dimension 2 over Q), `C1_Q = Cl(Q^1, (2))` and `C2_Q = Cl(Q^1, (-1))`
    both have irreducible Q-representation spectrum `(1; [2])`, while their centers are the
    explicit quadratic field extensions `Q(√2)` and `Q(i)`, which are non-isomorphic both as
    Q-algebras and as abstract unital rings! -/
theorem regime_II_same_dim_separation :
    HasKDim RatQ C1_Q 2 ∧
    HasKDim RatQ C2_Q 2 ∧
    HasUniqueSimpleModuleOfDim RatQ C1_Q 2 ∧
    HasUniqueSimpleModuleOfDim RatQ C2_Q 2 ∧
    Nonempty (AlgIso RatQ (Center C1_Q) Qsqrt2) ∧
    Nonempty (AlgIso RatQ (Center C2_Q) Qi) ∧
    ¬ Nonempty (AlgIso RatQ (Center C1_Q) (Center C2_Q)) ∧
    ¬ Nonempty (RingIso (Center C1_Q) (Center C2_Q)) := by
  have hAlgDim1 : HasKDim RatQ C1_Q 2 := clifford_hasKDim RatQ 1 (vec1 ((1 : RatQ) + 1))
  have hAlgDim2 : HasKDim RatQ C2_Q 2 := clifford_hasKDim RatQ 1 (vec1 (-1))
  have hRep1 : HasUniqueSimpleModuleOfDim RatQ C1_Q 2 :=
    cl1_nonSquare_hasUniqueSimpleModuleOfDim RatQ ((1 : RatQ) + 1) ratQ_nonSquare_two
  have hRep2 : HasUniqueSimpleModuleOfDim RatQ C2_Q 2 :=
    cl1_nonSquare_hasUniqueSimpleModuleOfDim RatQ (-1) ratQ_nonSquare_neg_one
  let eZ1 : AlgIso RatQ (Center C1_Q) Qsqrt2 := cl1CenterIsoQuadExt RatQ ((1 : RatQ) + 1)
  let eZ2 : AlgIso RatQ (Center C2_Q) Qi := cl1CenterIsoQuadExt RatQ (-1)
  have hNoRing : ¬ Nonempty (RingIso (Center C1_Q) (Center C2_Q)) := by
    intro ⟨eRing⟩
    let isoQiSqrt2 : RingIso Qi Qsqrt2 :=
      RingIso.trans eZ2.symm.toRingIso (RingIso.trans eRing.symm eZ1.toRingIso)
    exact no_ringHom_qi_to_qsqrt2 ⟨isoQiSqrt2.toRingHom⟩
  have hNoAlg : ¬ Nonempty (AlgIso RatQ (Center C1_Q) (Center C2_Q)) := by
    intro ⟨eAlg⟩
    exact hNoRing ⟨eAlg.toRingIso⟩
  exact ⟨hAlgDim1, hAlgDim2, hRep1, hRep2, ⟨eZ1⟩, ⟨eZ2⟩, hNoAlg, hNoRing⟩

/-! ### Section 5: Main Theorem III — Base-Field Extension Pair `(Q, Q(i))` on `Cl_{1,1}` -/

/-- `B_Qi = Cl_{1,1}(Q(i)) = Cl(Q(i)^2, (1, -1))` over the quadratic extension `Q(i)`. -/
abbrev B_Qi : Type := Clifford Qi 2 (vec2 1 (-1))

/-- Canonical injective ring homomorphism `Cl_{1,1}(Q) ↪ Cl_{1,1}(Q(i))` induced by `Q ↪ Q(i)`. -/
def cl11ScalarExtHom : RingHom A1_Q B_Qi where
  toFun x :=
    let emb := (QuadExt.embed RatQ (-1)).toFun
    ⟨((emb x.raw.1.1, emb x.raw.1.2), (emb x.raw.2.1, emb x.raw.2.2))⟩
  map_zero := rfl
  map_one := rfl
  map_add x y := by
    let emb := QuadExt.embed RatQ (-1)
    apply Clifford.ext
    exact Prod.ext
      (Prod.ext (emb.map_add x.raw.1.1 y.raw.1.1) (emb.map_add x.raw.1.2 y.raw.1.2))
      (Prod.ext (emb.map_add x.raw.2.1 y.raw.2.1) (emb.map_add x.raw.2.2 y.raw.2.2))
  map_mul x y := by
    let emb := QuadExt.embed RatQ (-1)
    have hneg1 : emb.toFun (-1 : RatQ) = (-1 : Qi) := by
      rw [emb.map_neg, emb.map_one]
    apply Clifford.ext
    apply Prod.ext
    · apply Prod.ext
      · -- First entry (0,0)
        change emb.toFun ((x.raw.1.1 * y.raw.1.1 + 1 * (x.raw.1.2 * y.raw.1.2)) +
          (-1 : RatQ) * (x.raw.2.1 * y.raw.2.1 + 1 * (x.raw.2.2 * (-y.raw.2.2)))) = _
        rw [emb.map_add, emb.map_add, emb.map_mul, emb.map_mul, emb.map_mul,
            emb.map_mul, emb.map_add, emb.map_mul, emb.map_mul, emb.map_mul,
            emb.map_one, hneg1, emb.map_neg]
        rfl
      · -- Entry (0,1)
        change emb.toFun ((x.raw.1.1 * y.raw.1.2 + x.raw.1.2 * y.raw.1.1) +
          (-1 : RatQ) * (x.raw.2.1 * (-y.raw.2.2) + x.raw.2.2 * y.raw.2.1)) = _
        rw [emb.map_add, emb.map_add, emb.map_mul, emb.map_mul, emb.map_mul,
            emb.map_add, emb.map_mul, emb.map_mul, hneg1, emb.map_neg]
        rfl
    · apply Prod.ext
      · -- Entry (1,0)
        change emb.toFun ((x.raw.1.1 * y.raw.2.1 + 1 * (x.raw.1.2 * y.raw.2.2)) +
          (x.raw.2.1 * y.raw.1.1 + 1 * (x.raw.2.2 * (-y.raw.1.2)))) = _
        rw [emb.map_add, emb.map_add, emb.map_add, emb.map_mul, emb.map_mul,
            emb.map_mul, emb.map_mul, emb.map_mul, emb.map_mul, emb.map_one, emb.map_neg]
        rfl
      · -- Entry (1,1)
        change emb.toFun ((x.raw.1.1 * y.raw.2.2 + x.raw.1.2 * y.raw.2.1) +
          (x.raw.2.1 * (-y.raw.1.2) + x.raw.2.2 * y.raw.1.1)) = _
        rw [emb.map_add, emb.map_add, emb.map_add, emb.map_mul, emb.map_mul,
            emb.map_mul, emb.map_mul, emb.map_neg]
        rfl

theorem cl11ScalarExtHom_injective :
    ∀ x y : A1_Q, cl11ScalarExtHom.toFun x = cl11ScalarExtHom.toFun y → x = y := by
  intro x y h
  have hraw := congrArg Clifford.raw h
  have h1 := congrArg Prod.fst hraw
  have h2 := congrArg Prod.snd hraw
  apply Clifford.ext
  exact Prod.ext
    (Prod.ext (QuadExt.embed_injective _ _ (congrArg Prod.fst h1))
              (QuadExt.embed_injective _ _ (congrArg Prod.snd h1)))
    (Prod.ext (QuadExt.embed_injective _ _ (congrArg Prod.fst h2))
              (QuadExt.embed_injective _ _ (congrArg Prod.snd h2)))

/-- **Main Theorem III (Base-Field Extension Pair `Q ↪ Q(i)` on Identical Split Form `(1, -1)`)**:
    Over the explicit field extension `Q ↪ Q(i)`:
    1. `A1_Q = Cl_{1,1}(Q)` embeds injectively into `B_Qi = Cl_{1,1}(Q(i))`;
    2. Both algebras are represented by the exact same spinor formula `[[v0, v1], [-v1, -v0]]`
       and share the identical irreducible-representation spectrum `(1; [2])` over their
       respective base fields (`RatQ` and `Qi`);
    3. Their centers satisfy `Z(Cl_{1,1}(Q)) ≃ Q` and `Z(Cl_{1,1}(Q(i))) ≃ Q(i)`, which are
       **non-isomorphic as unital rings**! -/
theorem regime_III_base_extension_separation :
    (∀ x y : A1_Q, cl11ScalarExtHom.toFun x = cl11ScalarExtHom.toFun y → x = y) ∧
    HasUniqueSimpleModuleOfDim RatQ A1_Q 2 ∧
    HasUniqueSimpleModuleOfDim Qi B_Qi 2 ∧
    Nonempty (RingIso (Center A1_Q) RatQ) ∧
    Nonempty (RingIso (Center B_Qi) Qi) ∧
    ¬ Nonempty (RingIso (Center A1_Q) (Center B_Qi)) := by
  have hRepQ : HasUniqueSimpleModuleOfDim RatQ A1_Q 2 :=
    cl11_hasUniqueSimpleModuleOfDim RatQ ratQ_two_ne_zero
  have hRepQi : HasUniqueSimpleModuleOfDim Qi B_Qi 2 :=
    cl11_hasUniqueSimpleModuleOfDim Qi qi_two_ne_zero
  let eZQ : RingIso (Center A1_Q) RatQ := (cl11CenterIsoField RatQ ratQ_two_ne_zero).toRingIso
  let eZQi : RingIso (Center B_Qi) Qi := (cl11CenterIsoField Qi qi_two_ne_zero).toRingIso
  have hNoRing : ¬ Nonempty (RingIso (Center A1_Q) (Center B_Qi)) := by
    intro ⟨eRing⟩
    let isoQiQ : RingIso Qi RatQ :=
      RingIso.trans eZQi.symm (RingIso.trans eRing.symm eZQ)
    exact no_ringHom_qi_to_ratQ ⟨isoQiQ.toRingHom⟩
  exact ⟨cl11ScalarExtHom_injective, hRepQ, hRepQi, ⟨eZQ⟩, ⟨eZQi⟩, hNoRing⟩

/-! ### Section 6: Quadratically-Closed Obstruction Theorem (Why Field Extensions Are Necessary) -/

section QuadraticallyClosedObstruction

variable {K : Type u} [FieldStructure K]

/-- Over a quadratically closed field K (char(K) ≠ 2), if d0 = u^2 ≠ 0, the character
    χ_+(a, b) = a + u * b : Cl(K^1, (d0)) → K makes K a 1-dimensional simple Cl(K^1, (d0))-module,
    so `Cl(K^1, (d0))` NEVER has irreducible-representation spectrum `(1; [2])`! -/
theorem cl1_square_not_rep_dim2 {d0 u : K} (_hd0 : d0 ≠ 0) (hu : u * u = d0) :
    ¬ HasUniqueSimpleModuleOfDim K (Clifford K 1 (vec1 d0)) 2 := by
  intro hRep2
  -- Define K-algebra character chi : Cl(K^1, (d0)) → K by chi(a, b) = a + u * b
  let chi : RingHom (Clifford K 1 (vec1 d0)) K := {
    toFun := fun x => x.raw.1 + u * x.raw.2
    map_zero := by
      change (0 : K) + u * 0 = 0
      rw [mul_zero_ring, AddCommGrp.zero_add]
    map_one := by
      change (1 : K) + u * 0 = 1
      rw [mul_zero_ring, add_zero_grp]
    map_add := fun x y => by
      change (x.raw.1 + y.raw.1) + u * (x.raw.2 + y.raw.2) =
        (x.raw.1 + u * x.raw.2) + (y.raw.1 + u * y.raw.2)
      rw [UnitalRing.left_distrib]
      rw [AddCommGrp.add_assoc x.raw.1, ← AddCommGrp.add_assoc y.raw.1,
          AddCommGrp.add_comm y.raw.1 (u * x.raw.2), AddCommGrp.add_assoc, ← AddCommGrp.add_assoc]
    map_mul := fun x y => by
      rcases x with ⟨⟨a1, b1⟩⟩
      rcases y with ⟨⟨a2, b2⟩⟩
      change (a1 * a2 + d0 * (b1 * b2)) +
          u * (a1 * b2 + b1 * a2) =
        (a1 + u * b1) * (a2 + u * b2)
      rw [← hu]
      rw [UnitalRing.left_distrib (a1 + u * b1),
          UnitalRing.right_distrib, UnitalRing.right_distrib,
          UnitalRing.left_distrib u]
      have hterm_u2 : (u * b1) * (u * b2) = (u * u) * (b1 * b2) := by
        rw [UnitalRing.mul_assoc u b1, ← UnitalRing.mul_assoc b1 u b2,
            FieldStructure.mul_comm b1 u, UnitalRing.mul_assoc u b1,
            ← UnitalRing.mul_assoc u u]
      have hterm_ux1 : a1 * (u * b2) = u * (a1 * b2) := by
        rw [← UnitalRing.mul_assoc, FieldStructure.mul_comm a1 u, UnitalRing.mul_assoc]
      have hterm_ux2 : (u * b1) * a2 = u * (b1 * a2) :=
        UnitalRing.mul_assoc u b1 a2
      rw [hterm_u2, hterm_ux1, hterm_ux2]
      let P := a1 * a2
      let Q := (u * u) * (b1 * b2)
      let R := u * (a1 * b2)
      let S := u * (b1 * a2)
      calc
        (P + Q) + (R + S) = P + (Q + (R + S)) := AddCommGrp.add_assoc P Q (R + S)
        _ = P + ((R + S) + Q) := by rw [AddCommGrp.add_comm Q (R + S)]
        _ = P + ((S + R) + Q) := by rw [AddCommGrp.add_comm R S]
        _ = P + (S + (R + Q)) := by rw [AddCommGrp.add_assoc S R Q]
        _ = (P + S) + (R + Q) := (AddCommGrp.add_assoc P S (R + Q)).symm
  }
  -- Equip K with the 1-dimensional simple K-module structure pulled back along chi
  let instMod1 : KModule K (Clifford K 1 (vec1 d0)) K := {
    toKVectorSpace := algebraToVectorSpace K K
    act := fun a z => chi.toFun a * z
    one_act := fun z => by rw [chi.map_one, UnitalRing.one_mul]
    mul_act := fun a b z => by rw [chi.map_mul, UnitalRing.mul_assoc]
    act_zero := fun a => mul_zero_ring (chi.toFun a)
    act_add := fun a z1 z2 => UnitalRing.left_distrib (chi.toFun a) z1 z2
    add_act := fun a b z => by rw [chi.map_add, UnitalRing.right_distrib]
    zero_act := fun z => by rw [chi.map_zero, zero_mul_ring]
    smul_act := fun c a z => by
      have hchi_smul : chi.toFun (KSMul.smul c a) = c * chi.toFun a := by
        change c * a.raw.1 + u * (c * a.raw.2) = c * (a.raw.1 + u * a.raw.2)
        rw [UnitalRing.left_distrib, ← UnitalRing.mul_assoc u c,
            FieldStructure.mul_comm u c, UnitalRing.mul_assoc c u]
      change chi.toFun (KSMul.smul c a) * z = c * (chi.toFun a * z)
      rw [hchi_smul, UnitalRing.mul_assoc]
  }
  have hSimple1 : @IsSimpleModule (Clifford K 1 (vec1 d0)) _ K instMod1.toLeftModule := by
    let _ : KModule K (Clifford K 1 (vec1 d0)) K := instMod1
    apply isSimple_of_cyclic (Clifford K 1 (vec1 d0)) ⟨1, one_ne_zero_field⟩
    intro z0 hz0 w
    refine ⟨⟨(w * FieldStructure.inv z0, 0)⟩, ?_⟩
    change ((w * FieldStructure.inv z0) + u * 0) * z0 = w
    rw [mul_zero_ring, add_zero_grp, UnitalRing.mul_assoc,
        inv_mul_cancel_field hz0, UnitalRing.mul_one]
  -- By every_simple_hasDim, K would have K-dimension 2, contradicting dim_K K = 1!
  let _ : KModule K (Clifford K 1 (vec1 d0)) K := instMod1
  have hDim2 : HasKDim K K 2 := hRep2.every_simple_hasDim K hSimple1
  rcases hDim2 with ⟨e2⟩
  exact not_kLinearIso_fin1_fin2 K ⟨KLinearIso.trans (fieldSelfCoordIso K) e2.symm⟩

/-- Over ANY quadratically closed field K (`∀ c : K, ∃ u : K, u * u = c`) with `char(K) ≠ 2`,
    every nondegenerate 2-generator Clifford algebra `Cl(K^2, (d0, d1))` (`d0 ≠ 0, d1 ≠ 0`)
    is K-algebra isomorphic to `M_2(K)` (hence has `Spec_rep^K = (1; [2])` and `Z ≃ₐ[K] K`),
    whereas NO nondegenerate 1-generator Clifford algebra `Cl(K^1, (d2))` (`d2 ≠ 0`) has
    `Spec_rep^K = (1; [2])`! Thus a nontrivial quadratic field extension is REQUIRED. -/
theorem quadratically_closed_obstruction
    (hchar2 : (1 : K) + 1 ≠ 0)
    (hqc : ∀ c : K, ∃ u : K, u * u = c) :
    (∀ d2 : K, d2 ≠ 0 → ¬ HasUniqueSimpleModuleOfDim K (Clifford K 1 (vec1 d2)) 2) ∧
    (∀ d0 d1 : K, d0 ≠ 0 → d1 ≠ 0 →
      HasUniqueSimpleModuleOfDim K (Clifford K 2 (vec2 d0 d1)) 2 ∧
      Nonempty (AlgIso K (Center (Clifford K 2 (vec2 d0 d1))) K)) := by
  constructor
  · intro d2 hd2
    rcases hqc d2 with ⟨u, hu⟩
    exact cl1_square_not_rep_dim2 hd2 hu
  · intro d0 d1 hd0 hd1
    rcases hqc d0 with ⟨u0, hu0⟩
    rcases hqc (-d1) with ⟨u1, hu1⟩
    have hu0_ne : u0 ≠ 0 := by
      intro hz; rw [hz, zero_mul_ring] at hu0; exact hd0 hu0.symm
    have hu1_ne : u1 ≠ 0 := by
      intro hz
      rw [hz, zero_mul_ring] at hu1
      have hd1_0 : d1 = 0 := by
        calc d1 = -(-d1) := (neg_neg_grp d1).symm
          _ = -(0 : K) := by rw [← hu1]
          _ = 0 := neg_zero_grp
      exact hd1 hd1_0
    -- Rescale generators via universal property between Cl(K^2, (d0, d1)) and Cl(K^2, (1, -1))
    let fFwd : (Fin 2 → K) → Clifford K 2 (vec2 1 (-1)) :=
      fun v => Clifford.iota (vec2 1 (-1)) (vec2 (u0 * v ⟨0, by omega⟩) (u1 * v ⟨1, by omega⟩))
    have hfFwd : IsCliffordMap (vec2 d0 d1) fFwd := {
      map_add := fun x y => by
        unfold fFwd
        have hv : vec2 (u0 * (x + y) ⟨0, by omega⟩)
                       (u1 * (x + y) ⟨1, by omega⟩) =
            vec2 (u0 * x ⟨0, by omega⟩) (u1 * x ⟨1, by omega⟩) +
            vec2 (u0 * y ⟨0, by omega⟩) (u1 * y ⟨1, by omega⟩) := by
          funext i
          match i with
          | ⟨0, _⟩ => exact UnitalRing.left_distrib u0 (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)
          | ⟨1, _⟩ => exact UnitalRing.left_distrib u1 (x ⟨1, by omega⟩) (y ⟨1, by omega⟩)
        rw [hv, Clifford.iota_add]
      map_smul := fun c x => by
        unfold fFwd
        have hv : vec2 (u0 * KSMul.smul c x ⟨0, by omega⟩)
                       (u1 * KSMul.smul c x ⟨1, by omega⟩) =
            KSMul.smul c (vec2 (u0 * x ⟨0, by omega⟩) (u1 * x ⟨1, by omega⟩)) := by
          funext i
          match i with
          | ⟨0, _⟩ =>
            change u0 * (c * x ⟨0, by omega⟩) = c * (u0 * x ⟨0, by omega⟩)
            rw [← UnitalRing.mul_assoc, FieldStructure.mul_comm u0 c, UnitalRing.mul_assoc]
          | ⟨1, _⟩ =>
            change u1 * (c * x ⟨1, by omega⟩) = c * (u1 * x ⟨1, by omega⟩)
            rw [← UnitalRing.mul_assoc, FieldStructure.mul_comm u1 c, UnitalRing.mul_assoc]
        rw [hv, Clifford.iota_smul]
      map_sq := fun v => by
        unfold fFwd
        rw [Clifford.iota_sq]
        congr 1
        let v0 := v ⟨0, by omega⟩
        let v1 := v ⟨1, by omega⟩
        change ((0 : K) + 1 * ((u0 * v0) * (u0 * v0))) + (-1 : K) * ((u1 * v1) * (u1 * v1)) =
          ((0 : K) + d0 * (v0 * v0)) + d1 * (v1 * v1)
        have hsq0 : (u0 * v0) * (u0 * v0) = d0 * (v0 * v0) := by
          rw [UnitalRing.mul_assoc u0 v0, ← UnitalRing.mul_assoc v0 u0 v0,
              FieldStructure.mul_comm v0 u0, UnitalRing.mul_assoc u0 v0,
              ← UnitalRing.mul_assoc u0 u0, hu0]
        have hsq1 : (-1 : K) * ((u1 * v1) * (u1 * v1)) = d1 * (v1 * v1) := by
          rw [UnitalRing.mul_assoc u1 v1, ← UnitalRing.mul_assoc v1 u1 v1,
              FieldStructure.mul_comm v1 u1, UnitalRing.mul_assoc u1 v1,
              ← UnitalRing.mul_assoc u1 u1, hu1, neg_mul_ring, UnitalRing.one_mul,
              neg_mul_ring, neg_neg_grp]
        rw [UnitalRing.one_mul, hsq0, hsq1]
    }
    let fBwd : (Fin 2 → K) → Clifford K 2 (vec2 d0 d1) :=
      fun v => Clifford.iota (vec2 d0 d1)
        (vec2 (FieldStructure.inv u0 * v ⟨0, by omega⟩) (FieldStructure.inv u1 * v ⟨1, by omega⟩))
    have hfBwd : IsCliffordMap (vec2 1 (-1)) fBwd := {
      map_add := fun x y => by
        unfold fBwd
        have hv : vec2 (FieldStructure.inv u0 * (x + y) ⟨0, by omega⟩)
                       (FieldStructure.inv u1 * (x + y) ⟨1, by omega⟩) =
            vec2 (FieldStructure.inv u0 * x ⟨0, by omega⟩) (FieldStructure.inv u1 * x ⟨1, by omega⟩) +
            vec2 (FieldStructure.inv u0 * y ⟨0, by omega⟩) (FieldStructure.inv u1 * y ⟨1, by omega⟩) := by
          funext i
          match i with
          | ⟨0, _⟩ =>
            exact UnitalRing.left_distrib (FieldStructure.inv u0) (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)
          | ⟨1, _⟩ =>
            exact UnitalRing.left_distrib (FieldStructure.inv u1) (x ⟨1, by omega⟩) (y ⟨1, by omega⟩)
        rw [hv, Clifford.iota_add]
      map_smul := fun c x => by
        unfold fBwd
        have hv : vec2 (FieldStructure.inv u0 * KSMul.smul c x ⟨0, by omega⟩)
                       (FieldStructure.inv u1 * KSMul.smul c x ⟨1, by omega⟩) =
            KSMul.smul c (vec2 (FieldStructure.inv u0 * x ⟨0, by omega⟩)
                                      (FieldStructure.inv u1 * x ⟨1, by omega⟩)) := by
          funext i
          match i with
          | ⟨0, _⟩ =>
            change FieldStructure.inv u0 * (c * x ⟨0, by omega⟩) =
              c * (FieldStructure.inv u0 * x ⟨0, by omega⟩)
            rw [← UnitalRing.mul_assoc, FieldStructure.mul_comm (FieldStructure.inv u0) c,
                UnitalRing.mul_assoc]
          | ⟨1, _⟩ =>
            change FieldStructure.inv u1 * (c * x ⟨1, by omega⟩) =
              c * (FieldStructure.inv u1 * x ⟨1, by omega⟩)
            rw [← UnitalRing.mul_assoc, FieldStructure.mul_comm (FieldStructure.inv u1) c,
                UnitalRing.mul_assoc]
        rw [hv, Clifford.iota_smul]
      map_sq := fun v => by
        unfold fBwd
        rw [Clifford.iota_sq]
        congr 1
        let v0 := v ⟨0, by omega⟩
        let v1 := v ⟨1, by omega⟩
        let iu0 := FieldStructure.inv u0
        let iu1 := FieldStructure.inv u1
        change ((0 : K) + d0 * ((iu0 * v0) * (iu0 * v0))) + d1 * ((iu1 * v1) * (iu1 * v1)) =
          ((0 : K) + 1 * (v0 * v0)) + (-1 : K) * (v1 * v1)
        have hd0_inv : d0 * (iu0 * iu0) = 1 := by
          rw [← hu0, UnitalRing.mul_assoc u0 u0, ← UnitalRing.mul_assoc u0 iu0 iu0,
              FieldStructure.mul_inv_cancel u0 hu0_ne, UnitalRing.one_mul,
              FieldStructure.mul_inv_cancel u0 hu0_ne]
        have hd1_inv : d1 * (iu1 * iu1) = -1 := by
          have hneg : (-d1) * (iu1 * iu1) = 1 := by
            rw [← hu1, UnitalRing.mul_assoc u1 u1, ← UnitalRing.mul_assoc u1 iu1 iu1,
                FieldStructure.mul_inv_cancel u1 hu1_ne, UnitalRing.one_mul,
                FieldStructure.mul_inv_cancel u1 hu1_ne]
          rw [neg_mul_ring] at hneg
          calc d1 * (iu1 * iu1) = -(-(d1 * (iu1 * iu1))) := (neg_neg_grp _).symm
            _ = -1 := by rw [hneg]
        have hsq0 : d0 * ((iu0 * v0) * (iu0 * v0)) = 1 * (v0 * v0) := by
          rw [UnitalRing.mul_assoc iu0 v0, ← UnitalRing.mul_assoc v0 iu0 v0,
              FieldStructure.mul_comm v0 iu0, UnitalRing.mul_assoc iu0 v0,
              ← UnitalRing.mul_assoc iu0 iu0, ← UnitalRing.mul_assoc d0, hd0_inv]
        have hsq1 : d1 * ((iu1 * v1) * (iu1 * v1)) = (-1 : K) * (v1 * v1) := by
          rw [UnitalRing.mul_assoc iu1 v1, ← UnitalRing.mul_assoc v1 iu1 v1,
              FieldStructure.mul_comm v1 iu1, UnitalRing.mul_assoc iu1 v1,
              ← UnitalRing.mul_assoc iu1 iu1, ← UnitalRing.mul_assoc d1, hd1_inv]
        rw [hsq0, hsq1]
    }
    let homFwd := Clifford.lift (vec2 d0 d1) fFwd hfFwd
    let homBwd := Clifford.lift (vec2 (1 : K) (-1)) fBwd hfBwd
    -- Use lift_unique to show homBwd ∘ homFwd = id and homFwd ∘ homBwd = id!
    have hLeft : ∀ x, homBwd.toFun (homFwd.toFun x) = x := by
      intro x
      let comp1 : AlgHom K (Clifford K 2 (vec2 d0 d1)) (Clifford K 2 (vec2 d0 d1)) := {
        toFun := fun y => homBwd.toFun (homFwd.toFun y)
        map_zero := by rw [homFwd.map_zero, homBwd.map_zero]
        map_one := by rw [homFwd.map_one, homBwd.map_one]
        map_add := fun y1 y2 => by rw [homFwd.map_add, homBwd.map_add]
        map_mul := fun y1 y2 => by rw [homFwd.map_mul, homBwd.map_mul]
        map_smul := fun c y => by rw [homFwd.map_smul, homBwd.map_smul]
      }
      let idAlg : AlgHom K (Clifford K 2 (vec2 d0 d1)) (Clifford K 2 (vec2 d0 d1)) :=
        (AlgIso.refl K _).toAlgHom
      have hiota_cf : IsCliffordMap (vec2 d0 d1) (Clifford.iota (vec2 d0 d1)) :=
        ⟨Clifford.iota_add _, Clifford.iota_smul _, Clifford.iota_sq _⟩
      have hcomp_iota : ∀ v, comp1.toFun (Clifford.iota (vec2 d0 d1) v) =
          Clifford.iota (vec2 d0 d1) v := by
        intro v
        change homBwd.toFun (homFwd.toFun (Clifford.iota (vec2 d0 d1) v)) = _
        rw [Clifford.lift_iota, Clifford.lift_iota]
        dsimp only [fBwd]
        congr 1
        funext i
        match i with
        | ⟨0, _⟩ =>
          change FieldStructure.inv u0 * (u0 * v ⟨0, by omega⟩) = v ⟨0, by omega⟩
          rw [← UnitalRing.mul_assoc, inv_mul_cancel_field hu0_ne, UnitalRing.one_mul]
        | ⟨1, _⟩ =>
          change FieldStructure.inv u1 * (u1 * v ⟨1, by omega⟩) = v ⟨1, by omega⟩
          rw [← UnitalRing.mul_assoc, inv_mul_cancel_field hu1_ne, UnitalRing.one_mul]
      calc
        comp1.toFun x = (Clifford.lift (vec2 d0 d1) _ hiota_cf).toFun x :=
          Clifford.lift_unique _ _ hiota_cf comp1 hcomp_iota x
        _ = idAlg.toFun x :=
          (Clifford.lift_unique _ _ hiota_cf idAlg (fun _ => rfl) x).symm
        _ = x := rfl
    have hRight : ∀ y, homFwd.toFun (homBwd.toFun y) = y := by
      intro y
      let comp2 : AlgHom K (Clifford K 2 (vec2 1 (-1))) (Clifford K 2 (vec2 1 (-1))) := {
        toFun := fun z => homFwd.toFun (homBwd.toFun z)
        map_zero := by rw [homBwd.map_zero, homFwd.map_zero]
        map_one := by rw [homBwd.map_one, homFwd.map_one]
        map_add := fun z1 z2 => by rw [homBwd.map_add, homFwd.map_add]
        map_mul := fun z1 z2 => by rw [homBwd.map_mul, homFwd.map_mul]
        map_smul := fun c z => by rw [homBwd.map_smul, homFwd.map_smul]
      }
      let idAlg : AlgHom K (Clifford K 2 (vec2 1 (-1))) (Clifford K 2 (vec2 1 (-1))) :=
        (AlgIso.refl K _).toAlgHom
      have hiota_cf : IsCliffordMap (vec2 (1 : K) (-1)) (Clifford.iota (vec2 1 (-1))) :=
        ⟨Clifford.iota_add _, Clifford.iota_smul _, Clifford.iota_sq _⟩
      have hcomp_iota : ∀ v, comp2.toFun (Clifford.iota (vec2 1 (-1)) v) =
          Clifford.iota (vec2 1 (-1)) v := by
        intro v
        change homFwd.toFun (homBwd.toFun (Clifford.iota (vec2 1 (-1)) v)) = _
        rw [Clifford.lift_iota, Clifford.lift_iota]
        dsimp only [fFwd]
        congr 1
        funext i
        match i with
        | ⟨0, _⟩ =>
          change u0 * (FieldStructure.inv u0 * v ⟨0, by omega⟩) = v ⟨0, by omega⟩
          rw [← UnitalRing.mul_assoc, FieldStructure.mul_inv_cancel u0 hu0_ne, UnitalRing.one_mul]
        | ⟨1, _⟩ =>
          change u1 * (FieldStructure.inv u1 * v ⟨1, by omega⟩) = v ⟨1, by omega⟩
          rw [← UnitalRing.mul_assoc, FieldStructure.mul_inv_cancel u1 hu1_ne, UnitalRing.one_mul]
      calc
        comp2.toFun y = (Clifford.lift (vec2 1 (-1)) _ hiota_cf).toFun y :=
          Clifford.lift_unique _ _ hiota_cf comp2 hcomp_iota y
        _ = idAlg.toFun y :=
          (Clifford.lift_unique _ _ hiota_cf idAlg (fun _ => rfl) y).symm
        _ = y := rfl
    let isoSplit : AlgIso K (Clifford K 2 (vec2 d0 d1)) (Clifford K 2 (vec2 1 (-1))) := {
      toAlgHom := homFwd
      invFun := homBwd.toFun
      left_inv := hLeft
      right_inv := hRight
    }
    exact ⟨HasUniqueSimpleModuleOfDim.ofAlgIso isoSplit (cl11_hasUniqueSimpleModuleOfDim K hchar2),
           ⟨AlgIso.trans (AlgIso.centerIso isoSplit) (cl11CenterIsoField K hchar2)⟩⟩

end QuadraticallyClosedObstruction

/-! ### Section 7: Master Existential Resolution of Conjecture 00000007610 -/

/-- **Master Theorem (`conjecture_00000007610_true`)**:
    There exist two explicit Clifford algebras `Cl(Q^{n1}, d1)` and `Cl(Q^{n2}, d2)` with
    the **exact same irreducible-representation spectrum** (`HasUniqueSimpleModuleOfDim RatQ _ 2`)
    but **non-isomorphic center spectra** (`¬ Nonempty (RingIso (Center _) (Center _))` and
    `¬ Nonempty (AlgIso RatQ (Center _) (Center _))`), realized explicitly by the quadratic
    field-extension pair `(Q, Q(i))` (both over fixed base field `Q` AND across base-field
    scalar extension `Q ↪ Q(i)` AND within fixed generator dimension `n1 = n2 = 1`). -/
theorem conjecture_00000007610_true :
    (∃ (n1 n2 : Nat) (d1 : Fin n1 → RatQ) (d2 : Fin n2 → RatQ),
      HasUniqueSimpleModuleOfDim RatQ (Clifford RatQ n1 d1) 2 ∧
      HasUniqueSimpleModuleOfDim RatQ (Clifford RatQ n2 d2) 2 ∧
      Nonempty (AlgIso RatQ (Center (Clifford RatQ n1 d1)) RatQ) ∧
      Nonempty (AlgIso RatQ (Center (Clifford RatQ n2 d2)) Qi) ∧
      ¬ Nonempty (AlgIso RatQ (Center (Clifford RatQ n1 d1)) (Center (Clifford RatQ n2 d2))) ∧
      ¬ Nonempty (RingIso (Center (Clifford RatQ n1 d1)) (Center (Clifford RatQ n2 d2)))) ∧
    (∃ (d1 d2 : Fin 1 → RatQ),
      HasUniqueSimpleModuleOfDim RatQ (Clifford RatQ 1 d1) 2 ∧
      HasUniqueSimpleModuleOfDim RatQ (Clifford RatQ 1 d2) 2 ∧
      Nonempty (AlgIso RatQ (Center (Clifford RatQ 1 d1)) Qsqrt2) ∧
      Nonempty (AlgIso RatQ (Center (Clifford RatQ 1 d2)) Qi) ∧
      ¬ Nonempty (RingIso (Center (Clifford RatQ 1 d1)) (Center (Clifford RatQ 1 d2)))) := by
  rcases regime_I_separation with ⟨hR1, hR2, hZ1, hZ2, _, _, hNoAlg, hNoRing⟩
  rcases regime_II_same_dim_separation with ⟨_, _, hC1, hC2, hZC1, hZC2, _, hNoRingC⟩
  exact ⟨⟨2, 1, vec2 1 (-1), vec1 (-1), hR1, hR2, hZ1, hZ2, hNoAlg, hNoRing⟩,
         ⟨vec1 ((1 : RatQ) + 1), vec1 (-1), hC1, hC2, hZC1, hZC2, hNoRingC⟩⟩

end Conjecture00000007610
