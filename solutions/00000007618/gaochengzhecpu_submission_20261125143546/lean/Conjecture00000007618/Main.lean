/-
  Conjecture 00000007618 — Master Classification, Positive Even-Dimension Regime,
  and Complete Multi-Convention Refutations
  Core Lean 4.19.0 only (zero external dependencies).

  Proves symbolically (zero brute-force kernel unfolding):
    1. Universal Dimension-Sum Parity Equivalence (`dimension_sum_parity_equivalence`):
       vector dimension sum `r + s`, projective flat dimension sum `(r - 1) + (s - 1)`,
       and codimension sum `(n - r) + (n - s)` yield the identical mod-2 sign `(-1)^{r+s}`;
    2. Positive Even-Dimension Characterization (`even_dim_forward3Star_regime`,
       `p3_proper_forward3Star_complete_and_valid`):
       in every even ambient vector dimension `n = 2m` (`m ≥ 1`, i.e., `ℙ^{2m-1}`, notably
       3D Projective Space `ℙ^3` at `n = 4`), the forward three-star intersection formula
       `A ∨ B = (-1)^{r+s} ⋆((⋆A) ∧ (⋆B))` holds universally with complete spectrum `{+1, -1}`
       (including strictly on proper nonempty projective subspaces `1 ≤ r, s ≤ 3` in `ℙ^3`);
    3. Refutation 1 — Odd Ambient Dimensions (`odd_dim_forward3Star_collapses_to_one`,
       `odd_dim_proper_point_hyperplane_refutation`, `p4_positive_meet_proper_refutation`,
       `p1_proper_forward3Star_incomplete`):
       in every odd ambient dimension `n = 2m + 1` (`ℙ^{2m}`, including `ℙ^2` and `ℙ^4`),
       `⋆((⋆A) ∧ (⋆B)) = +1 · (A ∨ B)` identically, violating Clause 1 (incomplete sign
       spectrum `{+1}`) AND Clauses 2–3 on proper nonempty subspaces across all `n = 2m + 3`;
    4. Refutation 2 — Regressive Commutation Law (`commutation_proper_hyperplanes_refute_all_n_ge_2`,
       `commutation_omega_hyperplane_refutes_all_n_ge_2`, `commutation_not_fn_of_dim_sum_p3`):
       `B ∨ A = (-1)^{(n-r)(n-s)} (A ∨ B)` is refuted for EVERY `n ≥ 2` on proper hyperplanes,
       and in `ℙ^3` (`n = 4`) fails Clause 2 alone (`r + s = 4` on `(2, 2)` vs `(1, 3)` yields
       opposite signs `+1` vs `-1`, so no function `f(r + s)` whatsoever can govern it);
    5. Refutation 3 — Contraction, Unreverted Clifford, and Minkowski `ℝ^{3,1}` Laws
       (`cartan_contraction_refuted`, `dorst_contraction_refuted`,
       `unreverted_clifford_refuted`, `minkowski_cl31_double_star_refuted`);
    6. Master Bundled Negation Theorems (`not_Conjecture00000007618_Forward3Star_odd`,
       `not_Conjecture00000007618_Commutation_all_ge_2`,
       `not_Conjecture00000007618_CartanContraction`,
       `not_Conjecture00000007618_DorstContraction`,
       `not_Conjecture00000007618_UnrevertedClifford`,
       `conjecture_00000007618_false`) and `#print axioms` audits.
-/

import Conjecture00000007618.ProjectiveMeet

namespace Conjecture00000007618
namespace Cl

/-! ### Section 1: Symbolic Coordinate-Extraction & Nonzero-Meet Uniqueness Helpers -/

theorem scalarPart_one {R : Type} [CRing R] : ∀ (d : Nat), scalarPart d (one (R := R) d) = CRing.one
  | 0 => rfl
  | d + 1 => scalarPart_one d

theorem scalarPart_zero {R : Type} [CRing R] : ∀ (d : Nat), scalarPart d (zero (R := R) d) = CRing.zero
  | 0 => rfl
  | d + 1 => scalarPart_zero d

theorem scalarPart_smul {R : Type} [CRing R] : ∀ (d : Nat) (r : R) (x : Cl R d),
    scalarPart d (smul d r x) = CRing.mul r (scalarPart d x)
  | 0, _, _ => rfl
  | d + 1, r, (x, _) => scalarPart_smul d r x

theorem topPart_omega {R : Type} [CRing R] : ∀ (d : Nat), topPart d (omega (R := R) d) = CRing.one
  | 0 => rfl
  | d + 1 => topPart_omega d

theorem topPart_zero {R : Type} [CRing R] : ∀ (d : Nat), topPart d (zero (R := R) d) = CRing.zero
  | 0 => rfl
  | d + 1 => topPart_zero d

theorem topPart_smul {R : Type} [CRing R] : ∀ (d : Nat) (r : R) (x : Cl R d),
    topPart d (smul d r x) = CRing.mul r (topPart d x)
  | 0, _, _ => rfl
  | d + 1, r, (_, y) => topPart_smul d r y

theorem pStar_one {R : Type} [CRing R] : ∀ (d : Nat), pStar d (one (R := R) d) = omega d
  | 0 => by show CRing.mul CRing.one CRing.one = CRing.one; exact CRing.one_mul CRing.one
  | d + 1 => by
      show pStar (d + 1) (one d, zero d) = (zero d, omega d)
      rw [pStar_step, pStar_zero, invol_zero, pStar_one d]

theorem one_ne_zero_int (d : Nat) : one (R := Int) d ≠ zero d := by
  intro hz
  have h := congrArg (scalarPart d) hz
  rw [scalarPart_one, scalarPart_zero] at h
  have h' : (1 : Int) = 0 := h
  omega

/-- Symbolic complementary meet constructor: if `U ∧ W = ω_n`, then `(⋆⁻¹ U) ∨ (⋆⁻¹ W) = 1_n`. -/
theorem vee_pStarInv_of_wedge_eq_omega {R : Type} [CRing R] {n : Nat} {U W : Cl R n}
    (hw : wedge n U W = omega n) :
    vee n (pStarInv n U) (pStarInv n W) = one n := by
  unfold vee
  rw [pStar_pStarInv, pStar_pStarInv, hw, ← pStar_one n, pStarInv_pStar]

theorem unique_int_of_smul_one {n : Nat} {c d : Int}
    (heq : smul n c (one (R := Int) n) = smul n d (one (R := Int) n)) : c = d := by
  have h := congrArg (scalarPart n) heq
  rw [scalarPart_smul, scalarPart_smul, scalarPart_one] at h
  have h' : c * 1 = d * 1 := h
  omega

/-! ### Canonical Symbolic Proper-Subspace Witnesses in `ℙ^3` (`n = 4`) and `ℙ^4` (`n = 5`) -/

def U4_22 : Cl Int 4 := ((omega 2, zero 2), zero 3)
def W4_22 : Cl Int 4 := (zero 3, (zero 2, one 2))
def A4_22 : Cl Int 4 := pStarInv 4 U4_22
def B4_22 : Cl Int 4 := pStarInv 4 W4_22

def U4_13 : Cl Int 4 := (omega 3, zero 3)
def W4_13 : Cl Int 4 := (zero 3, one 3)
def A4_13 : Cl Int 4 := pStarInv 4 U4_13
def B4_13 : Cl Int 4 := pStarInv 4 W4_13

theorem hasGrade_A4_22 : HasGrade 4 2 A4_22 := by
  have hU : HasGrade 4 2 U4_22 := ⟨⟨hasGrade_omega 2, hasGrade_zero 2 1⟩, hasGrade_zero 3 1⟩
  exact pStarInv_hasGrade (by decide : 2 ≤ 4) hU

theorem hasGrade_B4_22 : HasGrade 4 2 B4_22 := by
  have hW : HasGrade 4 2 W4_22 := ⟨hasGrade_zero 3 2, ⟨hasGrade_zero 2 1, hasGrade_one 2⟩⟩
  exact pStarInv_hasGrade (by decide : 2 ≤ 4) hW

theorem vee_A4_22_B4_22 : vee 4 A4_22 B4_22 = one 4 := by
  apply vee_pStarInv_of_wedge_eq_omega
  unfold U4_22 W4_22
  rw [wedge_step, wedge_zero, zero_wedge, add_zero,
      wedge_step, wedge_zero, zero_wedge, add_zero, wedge_one]
  rfl

theorem hasGrade_A4_13 : HasGrade 4 1 A4_13 := by
  have hU : HasGrade 4 3 U4_13 := ⟨hasGrade_omega 3, hasGrade_zero 3 2⟩
  exact pStarInv_hasGrade (by decide : 3 ≤ 4) hU

theorem hasGrade_B4_13 : HasGrade 4 3 B4_13 := by
  have hW : HasGrade 4 1 W4_13 := ⟨hasGrade_zero 3 1, hasGrade_one 3⟩
  exact pStarInv_hasGrade (by decide : 1 ≤ 4) hW

theorem vee_A4_13_B4_13 : vee 4 A4_13 B4_13 = one 4 := by
  apply vee_pStarInv_of_wedge_eq_omega
  unfold U4_13 W4_13
  rw [wedge_step, wedge_zero, zero_wedge, add_zero, wedge_one]
  rfl

/-- Proper line `A4_22 ∈ Λ^2(ℤ^4)` and proper plane `B4_13 ∈ Λ^3(ℤ^4)` meet in a nonzero point (`k = 1`). -/
theorem pStar_vee_A4_22_B4_13 :
    pStar 4 (vee 4 A4_22 B4_13) = (zero 3, (omega 2, zero 2)) := by
  rw [pStar_vee]
  unfold A4_22 B4_13
  rw [pStar_pStarInv, pStar_pStarInv]
  unfold U4_22 W4_13
  rw [wedge_step, wedge_zero, zero_wedge, add_zero, wedge_one]

theorem coord_vee_A4_22_B4_13 : topPart 2 (pStar 4 (vee 4 A4_22 B4_13)).2.1 = 1 := by
  rw [pStar_vee_A4_22_B4_13]
  exact topPart_omega 2

theorem vee_A4_22_B4_13_ne_zero : vee 4 A4_22 B4_13 ≠ zero 4 := by
  intro hz
  have h := coord_vee_A4_22_B4_13
  rw [hz, pStar_zero] at h
  change topPart 2 (zero 2) = 1 at h
  rw [topPart_zero] at h
  have h' : (0 : Int) = 1 := h
  omega

theorem unique_int_on_vee_A4_22_B4_13 {c d : Int}
    (heq : smul 4 c (vee 4 A4_22 B4_13) = smul 4 d (vee 4 A4_22 B4_13)) : c = d := by
  have h := congrArg (fun z : Cl Int 4 => topPart 2 (pStar 4 z).2.1) heq
  dsimp only at h
  rw [pStar_smul, pStar_smul] at h
  change topPart 2 (smul 2 c (pStar 4 (vee 4 A4_22 B4_13)).2.1) =
         topPart 2 (smul 2 d (pStar 4 (vee 4 A4_22 B4_13)).2.1) at h
  rw [topPart_smul, topPart_smul, coord_vee_A4_22_B4_13] at h
  have h' : c * 1 = d * 1 := h
  omega

/-! ### Section 2: Universal Dimension-Sum Parity Equivalence -/

/-- Universal Dimension-Sum Parity Equivalence:
    For any nonempty subspaces `U, W` of an `n`-dimensional vector space (`1 ≤ r, s ≤ n`),
    the mod-2 sign of the vector-space dimension sum `r + s`, the projective dimension sum
    `(r - 1) + (s - 1)`, and the codimension sum `(n - r) + (n - s)` are IDENTICAL. -/
theorem dimension_sum_parity_equivalence {n r s : Nat}
    (hr1 : 1 ≤ r) (hrn : r ≤ n) (hs1 : 1 ≤ s) (hsn : s ≤ n) :
    paritySign ((r - 1) + (s - 1)) = paritySign (r + s) ∧
    paritySign ((n - r) + (n - s)) = paritySign (r + s) := by
  unfold paritySign
  exact ⟨CRing.ringParitySign_of_mod_eq (proj_dim_sum_mod_two hr1 hs1),
         CRing.ringParitySign_of_mod_eq (codim_sum_mod_two hrn hsn)⟩

/-! ### Section 3: Positive Regime — Even Ambient Vector Dimension (`n = 2m`, Notably `ℙ^3` at `n = 4`) -/

/-- Positive Characterization in Even Ambient Dimension (`n = 2m`, `m ≥ 1`, i.e., `ℙ^{2m-1}`):
    1. Across EVERY commutative ring `R` and ALL grades `r, s ≤ 2m` with `2m ≤ r + s`,
       `A ∨ B = (-1)^{r+s} · ⋆((⋆A) ∧ (⋆B))` holds identically;
    2. The sign spectrum `{paritySign (r + s)}` on `0 ≤ r, s ≤ 2m` (`2m ≤ r + s`) is complete `{+1, -1}`. -/
theorem even_dim_forward3Star_regime {R : Type} [CRing R] {m : Nat} (hm : 1 ≤ m) :
    (∀ r s : Nat, r ≤ 2 * m → s ≤ 2 * m → 2 * m ≤ r + s →
      ∀ A B : Cl R (2 * m), HasGrade (2 * m) r A → HasGrade (2 * m) s B →
        vee (2 * m) A B = smul (2 * m) (CRing.ringParitySign (r + s)) (veeForward3Star (2 * m) A B)) ∧
    (∃ r s : Nat, r ≤ 2 * m ∧ s ≤ 2 * m ∧ 2 * m ≤ r + s ∧ paritySign (r + s) = 1) ∧
    (∃ r s : Nat, r ≤ 2 * m ∧ s ≤ 2 * m ∧ 2 * m ≤ r + s ∧ paritySign (r + s) = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r s hr hs hrs A B hA hB
    rw [vee_eq_sign_veeForward3Star hr hs hrs hA hB,
        CRing.ringParitySign_of_mod_eq (even_dim_intersection_mod_two hm hr hs hrs)]
  · refine ⟨2 * m, 2 * m, Nat.le_refl _, Nat.le_refl _, by omega, ?_⟩
    unfold paritySign
    exact CRing.ringParitySign_even (by omega)
  · refine ⟨2 * m - 1, 2 * m, by omega, Nat.le_refl _, by omega, ?_⟩
    unfold paritySign
    exact CRing.ringParitySign_odd (by omega)

/-- Non-Vacuity on Proper Nonempty Projective Subspaces in 3D Projective Space `ℙ^3` (`n = 4`):
    1. Every homogeneous pair `A ∈ Λ^r(ℤ^4)`, `B ∈ Λ^s(ℤ^4)` (`r, s ≤ 4`, `4 ≤ r + s`) satisfies
       `A ∨ B = (-1)^{r+s} · ⋆((⋆A) ∧ (⋆B))`;
    2. Proper skew lines `A4_22, B4_22 ∈ Λ^2(ℤ^4)` (`1 ≤ r = 2, s = 2 ≤ 3`) have nonzero meet
       witnessing unique sign `+1 = (-1)^{2+2}`;
    3. Proper line `A4_22 ∈ Λ^2(ℤ^4)` and proper plane `B4_13 ∈ Λ^3(ℤ^4)` (`1 ≤ r = 2, s = 3 ≤ 3`)
       have nonzero meet witnessing unique sign `-1 = (-1)^{2+3}`. -/
theorem p3_proper_forward3Star_complete_and_valid :
    (∀ r s : Nat, r ≤ 4 → s ≤ 4 → 4 ≤ r + s →
      ∀ A B : Cl Int 4, HasGrade 4 r A → HasGrade 4 s B →
        vee 4 A B = smul 4 (paritySign (r + s)) (veeForward3Star 4 A B)) ∧
    (HasGrade 4 2 A4_22 ∧ HasGrade 4 2 B4_22 ∧ vee 4 A4_22 B4_22 ≠ zero 4 ∧
     (∀ c : Int, vee 4 A4_22 B4_22 = smul 4 c (veeForward3Star 4 A4_22 B4_22) → c = 1)) ∧
    (HasGrade 4 2 A4_22 ∧ HasGrade 4 3 B4_13 ∧ vee 4 A4_22 B4_13 ≠ zero 4 ∧
     (∀ c : Int, vee 4 A4_22 B4_13 = smul 4 c (veeForward3Star 4 A4_22 B4_13) → c = -1)) := by
  have hpos := (even_dim_forward3Star_regime (R := Int) (m := 2) (by decide)).1
  refine ⟨hpos, ?_, ?_⟩
  · refine ⟨hasGrade_A4_22, hasGrade_B4_22, ?_, ?_⟩
    · rw [vee_A4_22_B4_22]; exact one_ne_zero_int 4
    · intro c hc
      have hfwd := veeForward3Star_eq_sign_vee (by decide : 2 ≤ 4) (by decide : 2 ≤ 4)
                     (by decide : 4 ≤ 2 + 2) hasGrade_A4_22 hasGrade_B4_22
      rw [CRing.ringParitySign_even rfl, one_smul] at hfwd
      rw [hfwd, vee_A4_22_B4_22] at hc
      have hc' : smul 4 c (one 4) = smul 4 (1 : Int) (one 4) := by
        rw [show (1 : Int) = CRing.one from rfl, one_smul]
        exact hc.symm
      exact unique_int_of_smul_one hc'
  · refine ⟨hasGrade_A4_22, hasGrade_B4_13, vee_A4_22_B4_13_ne_zero, ?_⟩
    intro c hc
    have hfwd := veeForward3Star_eq_sign_vee (by decide : 2 ≤ 4) (by decide : 3 ≤ 4)
                   (by decide : 4 ≤ 2 + 3) hasGrade_A4_22 hasGrade_B4_13
    rw [CRing.ringParitySign_odd rfl] at hfwd
    rw [hfwd, smul_smul] at hc
    have hc' : smul 4 (CRing.mul c (-1 : Int)) (vee 4 A4_22 B4_13) =
               smul 4 (1 : Int) (vee 4 A4_22 B4_13) := by
      rw [show (1 : Int) = CRing.one from rfl, one_smul]
      exact hc.symm
    have hmul := unique_int_on_vee_A4_22_B4_13 hc'
    have hmul' : c * (-1) = 1 := hmul
    omega

/-! ### Section 4: Refutation 1 — Odd Ambient Dimensions (`n = 2m + 1`, i.e., All `ℙ^{2m}`) -/

/-- Universal Odd-Dimension Collapse (`n = 2m + 1`, i.e., ALL even-dimensional projective spaces `ℙ^{2m}`):
    Across EVERY commutative ring `R` and ALL subspace dimensions `r, s ≤ 2m + 1` (`2m + 1 ≤ r + s`),
      `A ∨ B = +1 · ⋆((⋆A) ∧ (⋆B))` identically!
    Consequently, the forward three-star sign-correction spectrum is `{+1}` (INCOMPLETE, missing `-1`). -/
theorem odd_dim_forward3Star_collapses_to_one {R : Type} [CRing R] (m : Nat)
    {r s : Nat} (hr : r ≤ 2 * m + 1) (hs : s ≤ 2 * m + 1) (hrs : 2 * m + 1 ≤ r + s)
    {A B : Cl R (2 * m + 1)} (hA : HasGrade (2 * m + 1) r A) (hB : HasGrade (2 * m + 1) s B) :
    vee (2 * m + 1) A B = veeForward3Star (2 * m + 1) A B := by
  rw [vee_eq_sign_veeForward3Star hr hs hrs hA hB,
      CRing.ringParitySign_even (odd_dim_intersection_mod_two_zero hr hs hrs),
      one_smul]

/-- Infinite Family Refutation Across EVERY Even-Dimensional Projective Space `ℙ^{2m}` (`n = 2m + 3 ≥ 3`,
    including the Classical Projective Plane `ℙ^2` at `m = 0` and `ℙ^4` at `m = 1`):
    Proper point `A_m ∈ Λ^1(ℤ^{2m+3})` (`r = 1`) and proper hyperplane `B_m ∈ Λ^{2m+2}(ℤ^{2m+3})`
    (`s = 2m + 2`) have `A_m ∨ B_m = 1 ≠ 0` and uniquely force `c = +1`, whereas ALL THREE
    dimension sums (`r + s`, projective sum, codimension sum) have `paritySign = -1 ≠ +1`. -/
theorem odd_dim_proper_point_hyperplane_refutation (m : Nat) :
    let n := 2 * m + 3
    let e := 2 * m + 2
    let A_m : Cl Int n := (zero e, one e)
    let B_m : Cl Int n := (omega e, zero e)
    HasGrade n 1 A_m ∧
    HasGrade n e B_m ∧
    vee n A_m B_m = one n ∧
    veeForward3Star n A_m B_m = one n ∧
    (∀ c : Int, vee n A_m B_m = smul n c (veeForward3Star n A_m B_m) → c = 1) ∧
    paritySign (1 + e) = -1 ∧
    paritySign ((1 - 1) + (e - 1)) = -1 ∧
    paritySign ((n - 1) + (n - e)) = -1 := by
  dsimp only
  let e := 2 * m + 2
  have hA : HasGrade (2 * m + 3) 1 ((zero e, one e) : Cl Int (2 * m + 3)) :=
    ⟨hasGrade_zero e 1, hasGrade_one e⟩
  have hB : HasGrade (2 * m + 3) (2 * m + 2) ((omega e, zero e) : Cl Int (2 * m + 3)) := by
    show HasGrade ((2 * m + 2) + 1) ((2 * m + 1) + 1) (omega e, zero e)
    exact ⟨hasGrade_omega e, hasGrade_zero e (2 * m + 1)⟩
  have hstA : pStar (e + 1) ((zero e, one e) : Cl Int (e + 1)) = (omega e, zero e) := by
    rw [pStar_step, pStar_one e, pStar_zero e,
        invol_on_grade e e (hasGrade_omega e),
        CRing.ringParitySign_even (by omega : e % 2 = 0), one_smul]
  have hstB : pStar (e + 1) ((omega e, zero e) : Cl Int (e + 1)) = (zero e, one e) := by
    rw [pStar_step, pStar_zero e, invol_zero e, pStar_omega e]
  have hwedge : wedge (e + 1) (pStar (e + 1) ((zero e, one e) : Cl Int (e + 1)))
                               (pStar (e + 1) ((omega e, zero e) : Cl Int (e + 1))) =
                omega (e + 1) := by
    rw [hstA, hstB, wedge_step, wedge_zero, zero_wedge, add_zero, wedge_one]
    rfl
  have hvee : vee (e + 1) ((zero e, one e) : Cl Int (e + 1)) ((omega e, zero e) : Cl Int (e + 1)) =
              one (e + 1) := by
    unfold vee
    rw [hwedge, ← pStar_one (e + 1), pStarInv_pStar]
  have hfwd : veeForward3Star (e + 1) ((zero e, one e) : Cl Int (e + 1))
                              ((omega e, zero e) : Cl Int (e + 1)) =
              one (e + 1) := by
    unfold veeForward3Star
    rw [hwedge, pStar_omega]
  refine ⟨hA, hB, hvee, hfwd, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [hvee, hfwd] at hc
    have hs := congrArg (scalarPart (e + 1)) hc
    rw [scalarPart_smul, scalarPart_one] at hs
    have hs' : (1 : Int) = c * 1 := hs
    omega
  · unfold paritySign; exact CRing.ringParitySign_odd (by omega)
  · unfold paritySign; exact CRing.ringParitySign_odd (by omega)
  · unfold paritySign; exact CRing.ringParitySign_odd (by omega)

/-- Positive-Intersection-Dimension (`k = 2 ≥ 1`) Proper-Flat Counterexample in `ℙ^4` (`n = 5`):
    Proper projective plane `A5 ∈ Λ^3(ℤ^5)` (`r = 3`) and proper hyperplane `B5 ∈ Λ^4(ℤ^5)` (`s = 4`)
    have nonzero line intersection (`k = 2`) with unique forward-star sign `+1 ≠ -1 = paritySign 7`. -/
theorem p4_positive_meet_proper_refutation :
    let U5 : Cl Int 5 := (U4_22, zero 4)
    let W5 : Cl Int 5 := (zero 4, one 4)
    let A5 := pStarInv 5 U5
    let B5 := pStarInv 5 W5
    HasGrade 5 3 A5 ∧ HasGrade 5 4 B5 ∧ vee 5 A5 B5 ≠ zero 5 ∧
    (∀ c : Int, vee 5 A5 B5 = smul 5 c (veeForward3Star 5 A5 B5) → c = 1) ∧
    paritySign (3 + 4) = -1 := by
  dsimp only
  let U5 : Cl Int 5 := (U4_22, zero 4)
  let W5 : Cl Int 5 := (zero 4, one 4)
  let A5 := pStarInv 5 U5
  let B5 := pStarInv 5 W5
  have hU4 : HasGrade 4 2 U4_22 := ⟨⟨hasGrade_omega 2, hasGrade_zero 2 1⟩, hasGrade_zero 3 1⟩
  have hU5 : HasGrade 5 2 U5 := ⟨hU4, hasGrade_zero 4 1⟩
  have hW5 : HasGrade 5 1 W5 := ⟨hasGrade_zero 4 1, hasGrade_one 4⟩
  have hA5 : HasGrade 5 3 A5 := pStarInv_hasGrade (by decide : 2 ≤ 5) hU5
  have hB5 : HasGrade 5 4 B5 := pStarInv_hasGrade (by decide : 1 ≤ 5) hW5
  have hst : pStar 5 (vee 5 A5 B5) = (zero 4, U4_22) := by
    rw [pStar_vee, pStar_pStarInv, pStar_pStarInv]
    show wedge 5 (U4_22, zero 4) (zero 4, one 4) = (zero 4, U4_22)
    rw [wedge_step, wedge_zero, zero_wedge, add_zero, wedge_one]
  have hcoord : topPart 2 (pStar 5 (vee 5 A5 B5)).2.1.1 = 1 := by
    rw [hst]
    exact topPart_omega 2
  have hnez : vee 5 A5 B5 ≠ zero 5 := by
    intro hz
    have hc := hcoord
    rw [hz, pStar_zero] at hc
    change topPart 2 (zero 2) = 1 at hc
    rw [topPart_zero] at hc
    have hc' : (0 : Int) = 1 := hc
    omega
  refine ⟨hA5, hB5, hnez, ?_, rfl⟩
  intro c hc
  have hcol := odd_dim_forward3Star_collapses_to_one (m := 2)
                 (by decide : 3 ≤ 5) (by decide : 4 ≤ 5) (by decide : 5 ≤ 3 + 4) hA5 hB5
  rw [← hcol] at hc
  have h := congrArg (fun z : Cl Int 5 => topPart 2 (pStar 5 z).2.1.1) hc
  dsimp only at h
  rw [pStar_smul] at h
  change topPart 2 (pStar 5 (vee 5 A5 B5)).2.1.1 =
         topPart 2 (smul 2 c (pStar 5 (vee 5 A5 B5)).2.1.1) at h
  rw [topPart_smul, hcoord] at h
  have h' : (1 : Int) = c * 1 := h
  omega

/-- Even at `n = 2` (`ℙ^1`), restricting to proper nonempty projective flats (`1 ≤ r, s ≤ 1`)
    collapses the sign spectrum to `{+1}` (failing Clause 1). -/
theorem p1_proper_forward3Star_incomplete :
    ∀ r s : Nat, 1 ≤ r → r ≤ 1 → 1 ≤ s → s ≤ 1 → paritySign (r + s) = 1 := by
  intro r s hr1 hr2 hs1 hs2
  have h : r = 1 ∧ s = 1 := ⟨by omega, by omega⟩
  rw [h.1, h.2]
  rfl

/-! ### Section 5: Refutation 2 — Regressive Commutation Law (`B ∨ A = (-1)^{(n-r)(n-s)} A ∨ B`) -/

/-- Infinite Family Refutation of Dimension-Sum Commutation Across EVERY Dimension `n = d + 2 ≥ 2`:
    Proper coordinate hyperplanes `H_1, H_2 ∈ Λ^{d+1}(ℤ^{d+2})` satisfy `H_1 ∨ H_2 ≠ 0` and
    uniquely force `c = -1`, whereas ALL THREE dimension sums have `paritySign = +1 ≠ -1`. -/
theorem commutation_proper_hyperplanes_refute_all_n_ge_2 (d : Nat) :
    let n := d + 2
    let v1 : Cl Int n := ((zero d, one d), (zero d, zero d))
    let v2 : Cl Int n := ((zero d, zero d), (one d, zero d))
    let H1 := pStarInv n v1
    let H2 := pStarInv n v2
    HasGrade n (d + 1) H1 ∧
    HasGrade n (d + 1) H2 ∧
    vee n H1 H2 ≠ zero n ∧
    vee n H2 H1 = neg n (vee n H1 H2) ∧
    (∀ c : Int, vee n H2 H1 = smul n c (vee n H1 H2) → c = -1) ∧
    paritySign ((d + 1) + (d + 1)) = 1 ∧
    paritySign (((d + 1) - 1) + ((d + 1) - 1)) = 1 ∧
    paritySign ((n - (d + 1)) + (n - (d + 1))) = 1 := by
  dsimp only
  let n := d + 2
  let v1 : Cl Int n := ((zero d, one d), (zero d, zero d))
  let v2 : Cl Int n := ((zero d, zero d), (one d, zero d))
  let H1 := pStarInv n v1
  let H2 := pStarInv n v2
  have hv1 : HasGrade n 1 v1 := ⟨⟨hasGrade_zero d 1, hasGrade_one d⟩, ⟨hasGrade_zero d 0, rfl⟩⟩
  have hv2 : HasGrade n 1 v2 := ⟨⟨hasGrade_zero d 1, hasGrade_zero d 0⟩, ⟨hasGrade_one d, rfl⟩⟩
  have h1_le : 1 ≤ n := by omega
  have hH1 : HasGrade n (d + 1) H1 := pStarInv_hasGrade h1_le hv1
  have hH2 : HasGrade n (d + 1) H2 := pStarInv_hasGrade h1_le hv2
  have hst_vee : pStar n (vee n H1 H2) = (zero (d + 1), (zero d, one d)) := by
    rw [pStar_vee, pStar_pStarInv, pStar_pStarInv]
    show wedge (d + 2) ((zero d, one d), zero (d + 1)) (zero (d + 1), one (d + 1)) = _
    rw [wedge_step, wedge_zero, wedge_one, zero_wedge, add_zero]
  have hcoord : scalarPart d (pStar n (vee n H1 H2)).2.2 = 1 := by
    rw [hst_vee]
    exact scalarPart_one d
  have hnez : vee n H1 H2 ≠ zero n := by
    intro hz
    have hc := hcoord
    rw [hz, pStar_zero] at hc
    change scalarPart d (zero d) = 1 at hc
    rw [scalarPart_zero] at hc
    have hc' : (0 : Int) = 1 := hc
    omega
  have hswap : vee n H2 H1 = neg n (vee n H1 H2) := by
    have hd1 : d + 1 ≤ n := by omega
    rw [vee_graded_comm hd1 hd1 hH1 hH2]
    have hprod : (n - (d + 1)) * (n - (d + 1)) = 1 := by
      have hsub : n - (d + 1) = 1 := by omega
      rw [hsub]
    rw [hprod, CRing.ringParitySign_odd rfl, neg_one_smul]
  refine ⟨hH1, hH2, hnez, hswap, ?_, ?_, ?_, ?_⟩
  · intro c hc
    change vee n H2 H1 = smul n c (vee n H1 H2) at hc
    rw [hswap, ← neg_one_smul n (vee n H1 H2)] at hc
    have hp := congrArg (fun z : Cl Int n => scalarPart d (pStar n z).2.2) hc
    dsimp only at hp
    rw [pStar_smul, pStar_smul] at hp
    change scalarPart d (smul d (-1 : Int) (pStar n (vee n H1 H2)).2.2) =
           scalarPart d (smul d c (pStar n (vee n H1 H2)).2.2) at hp
    rw [scalarPart_smul, scalarPart_smul, hcoord] at hp
    have hp' : (-1 : Int) * 1 = c * 1 := hp
    omega
  · unfold paritySign; exact CRing.ringParitySign_even (by omega)
  · unfold paritySign; exact CRing.ringParitySign_even (by omega)
  · unfold paritySign; exact CRing.ringParitySign_even (by omega)

/-- Opposite-Direction Commutation Refutation Across EVERY Dimension `n = d + 2 ≥ 2`:
    `ω_n ∨ H_1 = H_1 ∨ ω_n = H_1 ≠ 0` forces `c = +1`, whereas `n + (n - 1) = 2d + 3` is ODD. -/
theorem commutation_omega_hyperplane_refutes_all_n_ge_2 (d : Nat) :
    let n := d + 2
    let v1 : Cl Int n := ((zero d, one d), (zero d, zero d))
    let H1 := pStarInv n v1
    HasGrade n n (omega (R := Int) n) ∧ HasGrade n (d + 1) H1 ∧
    vee n (omega n) H1 = H1 ∧ vee n H1 (omega n) = H1 ∧
    (∀ c : Int, vee n H1 (omega n) = smul n c (vee n (omega n) H1) → c = 1) ∧
    paritySign (n + (d + 1)) = -1 := by
  dsimp only
  let n := d + 2
  let v1 : Cl Int n := ((zero d, one d), (zero d, zero d))
  let H1 := pStarInv n v1
  have hv1 : HasGrade n 1 v1 := ⟨⟨hasGrade_zero d 1, hasGrade_one d⟩, ⟨hasGrade_zero d 0, rfl⟩⟩
  have hH1 : HasGrade n (d + 1) H1 := pStarInv_hasGrade (by omega) hv1
  refine ⟨hasGrade_omega n, hH1, omega_vee n H1, vee_omega n H1, ?_, ?_⟩
  · intro c hc
    change vee n H1 (omega n) = smul n c (vee n (omega n) H1) at hc
    rw [omega_vee, vee_omega] at hc
    have hp := congrArg (fun z : Cl Int n => scalarPart d (pStar n z).1.2) hc
    dsimp only at hp
    rw [pStar_smul, pStar_pStarInv] at hp
    change scalarPart d (one d) = scalarPart d (smul d c (one d)) at hp
    rw [scalarPart_smul, scalarPart_one] at hp
    have hp' : (1 : Int) = c * 1 := hp
    omega
  · unfold paritySign
    exact CRing.ringParitySign_odd (by omega)

/-- Pure Clause 2 Impossibility for Regressive Commutation on Proper Flats in `ℙ^3` (`n = 4`):
    `(r_1, s_1) = (2, 2)` and `(r_2, s_2) = (1, 3)` share sum `r + s = 4` with opposite signs `+1` vs `-1`. -/
theorem commutation_not_fn_of_dim_sum_p3 :
    ¬ ∃ f : Nat → Int,
        ∀ r s : Nat, 1 ≤ r → r ≤ 3 → 1 ≤ s → s ≤ 3 → 4 ≤ r + s →
          ∀ A B : Cl Int 4, HasGrade 4 r A → HasGrade 4 s B →
            vee 4 B A = smul 4 (f (r + s)) (vee 4 A B) := by
  rintro ⟨f, hf⟩
  have eq1 := hf 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
                A4_22 B4_22 hasGrade_A4_22 hasGrade_B4_22
  have eq2 := hf 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
                A4_13 B4_13 hasGrade_A4_13 hasGrade_B4_13
  rw [vee_graded_comm (by decide : 2 ≤ 4) (by decide : 2 ≤ 4) hasGrade_A4_22 hasGrade_B4_22,
      vee_A4_22_B4_22] at eq1
  rw [vee_graded_comm (by decide : 1 ≤ 4) (by decide : 3 ≤ 4) hasGrade_A4_13 hasGrade_B4_13,
      vee_A4_13_B4_13] at eq2
  have c1 := unique_int_of_smul_one eq1
  have c2 := unique_int_of_smul_one eq2
  have h1 : CRing.ringParitySign (R := Int) ((4 - 2) * (4 - 2)) = 1 := rfl
  have h2 : CRing.ringParitySign (R := Int) ((4 - 1) * (4 - 3)) = -1 := rfl
  rw [h1] at c1
  rw [h2] at c2
  have hsum : (2 : Nat) + 2 = 1 + 3 := rfl
  rw [hsum, ← c2] at c1
  exact absurd c1 (by decide)

/-! ### Section 6: Refutation 3 — Contraction, Unreverted Clifford, and Minkowski `ℝ^{3,1}` Meet Laws -/

/-- Canonical proper projective lines `L3_1, L3_2 ∈ Λ^2(ℤ^3)` (`r = s = 2`) in `ℙ^2` (`n = 3`). -/
def L3_1 : Cl Int 3 := pStarInv 3 ((zero 1, one 1), (zero 1, zero 1))
def L3_2 : Cl Int 3 := pStarInv 3 ((zero 1, zero 1), (one 1, zero 1))

theorem hasGrade_L3_1 : HasGrade 3 2 L3_1 :=
  (commutation_proper_hyperplanes_refute_all_n_ge_2 1).1

theorem hasGrade_L3_2 : HasGrade 3 2 L3_2 :=
  (commutation_proper_hyperplanes_refute_all_n_ge_2 1).2.1

theorem vee_L3_1_L3_2_ne_zero : vee 3 L3_1 L3_2 ≠ zero 3 :=
  (commutation_proper_hyperplanes_refute_all_n_ge_2 1).2.2.1

theorem unique_int_on_vee_L3_1_L3_2 {c d : Int}
    (heq : smul 3 c (vee 3 L3_1 L3_2) = smul 3 d (vee 3 L3_1 L3_2)) : c = d := by
  have hst : pStar 3 (vee 3 L3_1 L3_2) = (zero 2, (zero 1, one 1)) := by
    rw [pStar_vee]
    unfold L3_1 L3_2
    rw [pStar_pStarInv, pStar_pStarInv]
    show wedge 3 ((zero 1, one 1), zero 2) (zero 2, one 2) = _
    rw [wedge_step, wedge_zero, wedge_one, zero_wedge, add_zero]
  have h := congrArg (fun z : Cl Int 3 => scalarPart 1 (pStar 3 z).2.2) heq
  dsimp only at h
  rw [pStar_smul, pStar_smul] at h
  change scalarPart 1 (smul 1 c (pStar 3 (vee 3 L3_1 L3_2)).2.2) =
         scalarPart 1 (smul 1 d (pStar 3 (vee 3 L3_1 L3_2)).2.2) at h
  rw [scalarPart_smul, scalarPart_smul, hst, scalarPart_one] at h
  have h' : c * 1 = d * 1 := h
  omega

/-- Refutation of Cartan Left Contraction `(⋆A) ⌟_C B`:
    1. Fails `(-1)^{r+s}` on two proper lines in `ℙ^2` (`n = 3, r = s = 2`, sign `-1 ≠ +1`);
    2. Fails Clause 2 alone on proper flats in `ℙ^3` (`n = 4`: `(3, 2)` vs `(2, 3)` share sum `5`
       with opposite signs `-1` vs `+1`). -/
theorem cartan_contraction_refuted :
    (HasGrade 3 2 L3_1 ∧ HasGrade 3 2 L3_2 ∧ vee 3 L3_1 L3_2 ≠ zero 3 ∧
     (∀ c : Int, cartanLeft 3 (pStar 3 L3_1) L3_2 = smul 3 c (vee 3 L3_1 L3_2) → c = -1) ∧
     paritySign (2 + 2) = 1) ∧
    (¬ ∃ f : Nat → Int,
        ∀ r s : Nat, 1 ≤ r → r ≤ 3 → 1 ≤ s → s ≤ 3 → 4 ≤ r + s →
          ∀ A B : Cl Int 4, HasGrade 4 r A → HasGrade 4 s B →
            cartanLeft 4 (pStar 4 A) B = smul 4 (f (r + s)) (vee 4 A B)) := by
  refine ⟨⟨hasGrade_L3_1, hasGrade_L3_2, vee_L3_1_L3_2_ne_zero, ?_, rfl⟩, ?_⟩
  · intro c hc
    rw [cartanLeft_pStar_eq_sign_vee (by decide : 2 ≤ 3) (by decide : 2 ≤ 3)
          (by decide : 3 ≤ 2 + 2) hasGrade_L3_1 hasGrade_L3_2] at hc
    have hsgn : CRing.ringParitySign (R := Int) ((2 + 2 - 3) * (3 - 2)) = -1 := rfl
    rw [hsgn] at hc
    exact (unique_int_on_vee_L3_1_L3_2 hc).symm
  · rintro ⟨f, hf⟩
    have eq1 := hf 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
                  B4_13 A4_22 hasGrade_B4_13 hasGrade_A4_22
    have eq2 := hf 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
                  A4_22 B4_13 hasGrade_A4_22 hasGrade_B4_13
    rw [cartanLeft_pStar_eq_sign_vee (by decide : 3 ≤ 4) (by decide : 2 ≤ 4)
          (by decide : 4 ≤ 3 + 2) hasGrade_B4_13 hasGrade_A4_22] at eq1
    rw [cartanLeft_pStar_eq_sign_vee (by decide : 2 ≤ 4) (by decide : 3 ≤ 4)
          (by decide : 4 ≤ 2 + 3) hasGrade_A4_22 hasGrade_B4_13] at eq2
    have hcomm : vee 4 B4_13 A4_22 = vee 4 A4_22 B4_13 := by
      rw [vee_graded_comm (by decide : 2 ≤ 4) (by decide : 3 ≤ 4) hasGrade_A4_22 hasGrade_B4_13,
          CRing.ringParitySign_even rfl, one_smul]
    rw [hcomm] at eq1
    have c1 := unique_int_on_vee_A4_22_B4_13 eq1
    have c2 := unique_int_on_vee_A4_22_B4_13 eq2
    have s1 : CRing.ringParitySign (R := Int) ((3 + 2 - 4) * (4 - 3)) = -1 := rfl
    have s2 : CRing.ringParitySign (R := Int) ((2 + 3 - 4) * (4 - 2)) = 1 := rfl
    rw [s1] at c1
    rw [s2] at c2
    have hsum : (3 : Nat) + 2 = 2 + 3 := rfl
    rw [hsum, ← c2] at c1
    exact absurd c1 (by decide)

/-- Refutation of Dorst/Hestenes Left Contraction `(⋆A) ⌋ B` (Period-4 Sign Dependence):
    1. Fails `(-1)^{r+s}` on two proper lines in `ℙ^2` (`n = 3, r = s = 2`, sign `-1 ≠ +1`);
    2. Fails Clause 2 alone on proper flats in `ℙ^3` (`n = 4`: `(2, 2)` vs `(3, 1)` share sum `4`
       with opposite signs `-1` vs `+1`). -/
theorem dorst_contraction_refuted :
    ((∀ c : Int, dorstLeft 3 (pStar 3 L3_1) L3_2 = smul 3 c (vee 3 L3_1 L3_2) → c = -1) ∧
     paritySign (2 + 2) = 1) ∧
    (¬ ∃ f : Nat → Int,
        ∀ r s : Nat, 1 ≤ r → r ≤ 3 → 1 ≤ s → s ≤ 3 → 4 ≤ r + s →
          ∀ A B : Cl Int 4, HasGrade 4 r A → HasGrade 4 s B →
            dorstLeft 4 (pStar 4 A) B = smul 4 (f (r + s)) (vee 4 A B)) := by
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · intro c hc
    rw [dorstLeft_pStar_eq_sign_vee (by decide : 2 ≤ 3) (by decide : 2 ≤ 3)
          (by decide : 3 ≤ 2 + 2) hasGrade_L3_1 hasGrade_L3_2] at hc
    have hsgn : CRing.ringParitySign (R := Int) ((2 + 2 - 3) * (3 - 2) + (3 - 2) * (3 - 2 - 1) / 2) = -1 := rfl
    rw [hsgn] at hc
    exact (unique_int_on_vee_L3_1_L3_2 hc).symm
  · rintro ⟨f, hf⟩
    have eq1 := hf 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
                  A4_22 B4_22 hasGrade_A4_22 hasGrade_B4_22
    have eq2 := hf 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  B4_13 A4_13 hasGrade_B4_13 hasGrade_A4_13
    rw [dorstLeft_pStar_eq_sign_vee (by decide : 2 ≤ 4) (by decide : 2 ≤ 4)
          (by decide : 4 ≤ 2 + 2) hasGrade_A4_22 hasGrade_B4_22, vee_A4_22_B4_22] at eq1
    rw [dorstLeft_pStar_eq_sign_vee (by decide : 3 ≤ 4) (by decide : 1 ≤ 4)
          (by decide : 4 ≤ 3 + 1) hasGrade_B4_13 hasGrade_A4_13] at eq2
    have hswap31 : vee 4 B4_13 A4_13 = smul 4 (-1 : Int) (one 4) := by
      rw [vee_graded_comm (by decide : 1 ≤ 4) (by decide : 3 ≤ 4) hasGrade_A4_13 hasGrade_B4_13,
          vee_A4_13_B4_13]
      rfl
    rw [hswap31, smul_smul, smul_smul] at eq2
    have c1 := unique_int_of_smul_one eq1
    have c2 := unique_int_of_smul_one eq2
    have s1 : CRing.ringParitySign (R := Int) ((2 + 2 - 4) * (4 - 2) + (4 - 2) * (4 - 2 - 1) / 2) = -1 := rfl
    have s2 : CRing.mul (CRing.ringParitySign (R := Int) ((3 + 1 - 4) * (4 - 3) + (4 - 3) * (4 - 3 - 1) / 2)) (-1 : Int) = -1 := rfl
    rw [s1] at c1
    rw [s2] at c2
    have hsum : (2 : Nat) + 2 = 3 + 1 := rfl
    rw [hsum, ← c1] at c2
    exact absurd c2 (by decide)

/-- Refutation of Unreverted Clifford Meet `((A · ω⁻¹) ∧ (B · ω⁻¹)) · ω` (Period-4 Reversion Sign):
    1. Fails `(-1)^{r+s}` on two proper lines in `ℙ^2` (`n = 3, r = s = 2`, sign `-1 ≠ +1`);
    2. Fails Clause 2 alone on proper flats in `ℙ^3` (`n = 4`: `(2, 2)` vs `(1, 3)` share sum `4`
       with opposite signs `+1` vs `-1`). -/
theorem unreverted_clifford_refuted :
    ((∀ c : Int, veeUnrevertedClifford 3 L3_1 L3_2 = smul 3 c (vee 3 L3_1 L3_2) → c = -1) ∧
     paritySign (2 + 2) = 1) ∧
    (¬ ∃ f : Nat → Int,
        ∀ r s : Nat, 1 ≤ r → r ≤ 3 → 1 ≤ s → s ≤ 3 → 4 ≤ r + s →
          ∀ A B : Cl Int 4, HasGrade 4 r A → HasGrade 4 s B →
            veeUnrevertedClifford 4 A B = smul 4 (f (r + s)) (vee 4 A B)) := by
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · intro c hc
    rw [veeUnrevertedClifford_eq_sign_vee (by decide : 2 ≤ 3) (by decide : 2 ≤ 3)
          (by decide : 3 ≤ 2 + 2) hasGrade_L3_1 hasGrade_L3_2] at hc
    have hsgn : CRing.ringParitySign (R := Int)
      (2 * (2 - 1) / 2 + 2 * (2 - 1) / 2 + (3 - (2 + 2 - 3)) * ((3 - (2 + 2 - 3)) - 1) / 2 +
       (2 + 2 - 3) * (3 - (2 + 2 - 3))) = -1 := rfl
    rw [hsgn] at hc
    exact (unique_int_on_vee_L3_1_L3_2 hc).symm
  · rintro ⟨f, hf⟩
    have eq1 := hf 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
                  A4_22 B4_22 hasGrade_A4_22 hasGrade_B4_22
    have eq2 := hf 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
                  A4_13 B4_13 hasGrade_A4_13 hasGrade_B4_13
    rw [veeUnrevertedClifford_eq_sign_vee (by decide : 2 ≤ 4) (by decide : 2 ≤ 4)
          (by decide : 4 ≤ 2 + 2) hasGrade_A4_22 hasGrade_B4_22, vee_A4_22_B4_22] at eq1
    rw [veeUnrevertedClifford_eq_sign_vee (by decide : 1 ≤ 4) (by decide : 3 ≤ 4)
          (by decide : 4 ≤ 1 + 3) hasGrade_A4_13 hasGrade_B4_13, vee_A4_13_B4_13] at eq2
    have c1 := unique_int_of_smul_one eq1
    have c2 := unique_int_of_smul_one eq2
    have s1 : CRing.ringParitySign (R := Int)
      (2 * (2 - 1) / 2 + 2 * (2 - 1) / 2 + (4 - (2 + 2 - 4)) * ((4 - (2 + 2 - 4)) - 1) / 2 +
       (2 + 2 - 4) * (4 - (2 + 2 - 4))) = 1 := rfl
    have s2 : CRing.ringParitySign (R := Int)
      (1 * (1 - 1) / 2 + 3 * (3 - 1) / 2 + (4 - (1 + 3 - 4)) * ((4 - (1 + 3 - 4)) - 1) / 2 +
       (1 + 3 - 4) * (4 - (1 + 3 - 4))) = -1 := rfl
    rw [s1] at c1
    rw [s2] at c2
    have hsum : (2 : Nat) + 2 = 1 + 3 := rfl
    rw [hsum, ← c2] at c1
    exact absurd c1 (by decide)

/-- 4D Minkowski Metric `q = diag(1, 1, 1, -1)` (`Cl_{3,1}`):
    Even in ambient dimension `n = 4` (`ℙ^3`), replacing the Euclidean/Plücker star by the
    Lorentzian Hodge star `⋆_{3,1}` flips EVERY double-star sign by `∏ q_i = -1`, so at `r = s = 2`
    (`k = 0`), `⋆_{3,1}(⋆_{3,1}(1_4)) = -1_4`. -/
def minkowskiMetric4 : Fin 4 → Int
  | ⟨3, _⟩ => -1
  | _ => 1

theorem minkowski_cl31_double_star_refuted :
    prodMetric minkowskiMetric4 = -1 ∧
    (∀ k : Nat, k ≤ 4 → ∀ x : Cl Int 4, HasGrade 4 k x →
      cliffordRightStar minkowskiMetric4 (omega 4)
        (cliffordRightStar minkowskiMetric4 (omega 4) x) =
        smul 4 (-(paritySign (k * (4 - k)))) x) ∧
    (cliffordRightStar minkowskiMetric4 (omega 4)
       (cliffordRightStar minkowskiMetric4 (omega 4) (one (R := Int) 4)) =
       neg 4 (one 4)) := by
  have hprod : prodMetric minkowskiMetric4 = -1 := rfl
  have hgen : ∀ k : Nat, k ≤ 4 → ∀ x : Cl Int 4, HasGrade 4 k x →
      cliffordRightStar minkowskiMetric4 (omega 4)
        (cliffordRightStar minkowskiMetric4 (omega 4) x) =
        smul 4 (-(paritySign (k * (4 - k)))) x := by
    intro k hk x hx
    rw [cliffordRightStar_double minkowskiMetric4 k hk x hx, hprod]
    have hmul : CRing.mul (CRing.ringParitySign (R := Int) (k * (4 - k))) (-1 : Int) =
                -(paritySign (k * (4 - k))) := by
      unfold paritySign
      show CRing.ringParitySign (R := Int) (k * (4 - k)) * (-1) =
           -(CRing.ringParitySign (R := Int) (k * (4 - k)))
      omega
    rw [hmul]
  refine ⟨hprod, hgen, ?_⟩
  rw [hgen 0 (by decide) (one 4) (hasGrade_one 4)]
  have hp0 : -(paritySign (0 * (4 - 0))) = CRing.neg (CRing.one : Int) := rfl
  rw [hp0, neg_one_smul]

/-! ### Section 7: Master Bundled Formalization & Refutation of Conjecture 00000007618 -/

/-- Formal statement of the three-clause intersection-correction law of Conjecture `00000007618`
    for any binary projective intersection operator `targetOp` vs. `refOp` in ambient dimension `n`. -/
def SatisfiesConjecture7618InDim (n : Nat)
    (targetOp refOp : Nat → Nat → Cl Int n → Cl Int n → Cl Int n) : Prop :=
  ∃ eps : Nat → Nat → Int,
    -- Clause 1: Sign-correction term spectrum is complete (`{+1, -1}`)
    (∀ r s, r ≤ n → s ≤ n → n ≤ r + s → eps r s = 1 ∨ eps r s = -1) ∧
    (∃ r s, r ≤ n ∧ s ≤ n ∧ n ≤ r + s ∧ eps r s = 1) ∧
    (∃ r s, r ≤ n ∧ s ≤ n ∧ n ≤ r + s ∧ eps r s = -1) ∧
    -- Clause 2: Combination of the correction is a function of the dimension sum `r + s`
    (∃ f : Nat → Int, ∀ r s, r ≤ n → s ≤ n → n ≤ r + s → eps r s = f (r + s)) ∧
    -- Clause 3: Combination of the dimension sum is the mod-two reduction `(-1)^{(r+s) mod 2}`
    (∀ r s, r ≤ n → s ≤ n → n ≤ r + s → eps r s = paritySign (r + s)) ∧
    -- Algebraic intersection-correction law on exterior blades
    (∀ r s, r ≤ n → s ≤ n → n ≤ r + s →
      ∀ A B : Cl Int n, HasGrade n r A → HasGrade n s B →
        targetOp r s A B = smul n (eps r s) (refOp r s A B))

theorem not_Conjecture00000007618_Forward3Star_odd (m : Nat) :
    ¬ SatisfiesConjecture7618InDim (2 * m + 3)
        (fun _ _ A B => vee (2 * m + 3) A B)
        (fun _ _ A B => veeForward3Star (2 * m + 3) A B) := by
  rintro ⟨eps, _, _, _, _, hmod2, halg⟩
  rcases odd_dim_proper_point_hyperplane_refutation m with ⟨hA, hB, _, _, huniq, hpar, _, _⟩
  let e := 2 * m + 2
  have heps_mod := hmod2 1 e (by omega) (by omega) (by omega)
  have heps_alg := halg 1 e (by omega) (by omega) (by omega) (zero e, one e) (omega e, zero e) hA hB
  have hc1 := huniq (eps 1 e) heps_alg
  rw [hpar] at heps_mod
  omega

theorem not_Conjecture00000007618_Commutation_all_ge_2 (d : Nat) :
    ¬ SatisfiesConjecture7618InDim (d + 2)
        (fun _ _ A B => vee (d + 2) B A)
        (fun _ _ A B => vee (d + 2) A B) := by
  rintro ⟨eps, _, _, _, _, hmod2, halg⟩
  rcases commutation_proper_hyperplanes_refute_all_n_ge_2 d with ⟨hH1, hH2, _, _, huniq, hpar, _, _⟩
  let n := d + 2
  let v1 : Cl Int n := ((zero d, one d), (zero d, zero d))
  let v2 : Cl Int n := ((zero d, zero d), (one d, zero d))
  have heps_mod := hmod2 (d + 1) (d + 1) (by omega) (by omega) (by omega)
  have heps_alg := halg (d + 1) (d + 1) (by omega) (by omega) (by omega)
                     (pStarInv n v1) (pStarInv n v2) hH1 hH2
  have hcm1 := huniq (eps (d + 1) (d + 1)) heps_alg
  rw [hpar] at heps_mod
  omega

theorem not_Conjecture00000007618_CartanContraction :
    ¬ (∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => cartanLeft n (pStar n A) B)
          (fun _ _ A B => vee n A B)) := by
  intro hall
  rcases hall 3 (by decide) with ⟨eps, _, _, _, _, hmod2, halg⟩
  rcases cartan_contraction_refuted.1 with ⟨hL1, hL2, _, huniq, hpar⟩
  have heps_mod := hmod2 2 2 (by decide) (by decide) (by decide)
  have heps_alg := halg 2 2 (by decide) (by decide) (by decide) L3_1 L3_2 hL1 hL2
  have hcm1 := huniq (eps 2 2) heps_alg
  rw [hpar] at heps_mod
  omega

theorem not_Conjecture00000007618_DorstContraction :
    ¬ (∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => dorstLeft n (pStar n A) B)
          (fun _ _ A B => vee n A B)) := by
  intro hall
  rcases hall 3 (by decide) with ⟨eps, _, _, _, _, hmod2, halg⟩
  rcases dorst_contraction_refuted.1 with ⟨huniq, hpar⟩
  have heps_mod := hmod2 2 2 (by decide) (by decide) (by decide)
  have heps_alg := halg 2 2 (by decide) (by decide) (by decide)
                     L3_1 L3_2 hasGrade_L3_1 hasGrade_L3_2
  have hcm1 := huniq (eps 2 2) heps_alg
  rw [hpar] at heps_mod
  omega

theorem not_Conjecture00000007618_UnrevertedClifford :
    ¬ (∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => veeUnrevertedClifford n A B)
          (fun _ _ A B => vee n A B)) := by
  intro hall
  rcases hall 3 (by decide) with ⟨eps, _, _, _, _, hmod2, halg⟩
  rcases unreverted_clifford_refuted.1 with ⟨huniq, hpar⟩
  have heps_mod := hmod2 2 2 (by decide) (by decide) (by decide)
  have heps_alg := halg 2 2 (by decide) (by decide) (by decide)
                     L3_1 L3_2 hasGrade_L3_1 hasGrade_L3_2
  have hcm1 := huniq (eps 2 2) heps_alg
  rw [hpar] at heps_mod
  omega

/-- Master Theorem (`conjecture_00000007618_false`):
    Conjecture `00000007618` is FALSE across all five canonical projective intersection
    sign-correction conventions (Forward Three-Star Poincaré/Hodge Duality, Regressive Commutation,
    Cartan Interior Contraction, Dorst Left Contraction, and Unreverted Clifford Pseudoscalar Meet),
    while holding for Forward Three-Star Duality in even ambient vector dimensions `n = 2m`. -/
theorem conjecture_00000007618_false :
    (¬ ∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => vee n A B)
          (fun _ _ A B => veeForward3Star n A B)) ∧
    (∀ d : Nat,
        ¬ SatisfiesConjecture7618InDim (d + 2)
            (fun _ _ A B => vee (d + 2) B A)
            (fun _ _ A B => vee (d + 2) A B)) ∧
    (¬ ∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => cartanLeft n (pStar n A) B)
          (fun _ _ A B => vee n A B)) ∧
    (¬ ∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => dorstLeft n (pStar n A) B)
          (fun _ _ A B => vee n A B)) ∧
    (¬ ∀ n : Nat, 2 ≤ n →
        SatisfiesConjecture7618InDim n
          (fun _ _ A B => veeUnrevertedClifford n A B)
          (fun _ _ A B => vee n A B)) := by
  refine ⟨?_, not_Conjecture00000007618_Commutation_all_ge_2,
          not_Conjecture00000007618_CartanContraction,
          not_Conjecture00000007618_DorstContraction,
          not_Conjecture00000007618_UnrevertedClifford⟩
  intro hall
  exact not_Conjecture00000007618_Forward3Star_odd 0 (hall 3 (by decide))

end Cl
end Conjecture00000007618

/-! ### Kernel Axiom Audit -/

#print axioms Conjecture00000007618.Cl.dimension_sum_parity_equivalence
#print axioms Conjecture00000007618.Cl.cliffordRightStar_double
#print axioms Conjecture00000007618.Cl.vee_eq_leftStar_meet
#print axioms Conjecture00000007618.Cl.vee_graded_comm
#print axioms Conjecture00000007618.Cl.vee_eq_dimSum_factor_veeForward3Star
#print axioms Conjecture00000007618.Cl.cartanLeft_pStar_eq_sign_vee
#print axioms Conjecture00000007618.Cl.dorstLeft_pStar_eq_sign_vee
#print axioms Conjecture00000007618.Cl.veeUnrevertedClifford_eq_sign_vee
#print axioms Conjecture00000007618.Cl.even_dim_forward3Star_regime
#print axioms Conjecture00000007618.Cl.p3_proper_forward3Star_complete_and_valid
#print axioms Conjecture00000007618.Cl.odd_dim_forward3Star_collapses_to_one
#print axioms Conjecture00000007618.Cl.odd_dim_proper_point_hyperplane_refutation
#print axioms Conjecture00000007618.Cl.p4_positive_meet_proper_refutation
#print axioms Conjecture00000007618.Cl.commutation_proper_hyperplanes_refute_all_n_ge_2
#print axioms Conjecture00000007618.Cl.commutation_not_fn_of_dim_sum_p3
#print axioms Conjecture00000007618.Cl.cartan_contraction_refuted
#print axioms Conjecture00000007618.Cl.dorst_contraction_refuted
#print axioms Conjecture00000007618.Cl.unreverted_clifford_refuted
#print axioms Conjecture00000007618.Cl.minkowski_cl31_double_star_refuted
#print axioms Conjecture00000007618.Cl.conjecture_00000007618_false
