/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Complete refutations and sharp structural characterizations for Conjecture 00000007624:
1. Positive-definite Clifford nilpotents under BOTH `+Q` (`Cl_{2,0}`) and `-Q` (`Cl_{0,4}`),
   despite zero nonzero isotropic vectors, plus the complete `(p, q)` classification theorem
   `Cl_{p,q}(R)` has nonzero nilpotents ↔ `(p, q) ∉ {(0,0), (1,0), (0,1), (0,2), (0,3)}`.
2. Refutation of the null-vector sum construction in `Cl_{1,1}(R)` (`u^2 = w^2 = 0` and
   `u^2 + w^2 = 0`, yet `(u + w)^2 = 4 · 1` is non-nilpotent), alongside the exact polar
   orthogonality criterion `(u + w)^2 = 0 ↔ B_g(u, w) = 0`.
3. Refutations of the signature condition over degenerate forms `(p, 0, r)` (`r ≥ 1`),
   Gaussian integers `ℤ[i]` (complex sums of squares), finite prime fields `𝔽_3` and `𝔽_5`,
   and rational/integer indefinite Hasse–Minkowski obstructions `x^2 - 2 y^2` and
   `x^2 + y^2 - 3 z^2`.
-/
import Conjecture00000007624.Clifford

namespace Conjecture00000007624

/-! ## Part 1: Positive-Definite Clifford Nilpotents & Complete `(p, q)` Classification -/

section PositiveDefiniteNilpotents

variable {R : Type u} [OrderedDomain R]

private theorem scalar_neg_one_eq {g : List R} : scalar g (-1 : R) = -(1 : Cl R g) := by
  have hsum : scalar g (-1 : R) + scalar g 1 = 0 := by
    rw [← scalar_add, neg_add_cancel_eq, scalar_zero]
  rw [scalar_one] at hsum
  have h : -(scalar g (-1 : R)) = 1 := neg_eq_of_add_eq_zero hsum
  calc
    scalar g (-1 : R) = -(-(scalar g (-1 : R))) := (neg_neg_eq _).symm
    _ = -(1 : Cl R g) := congrArg Neg.neg h

private theorem clSmul_neg_one_eq {g : List R} (z : Cl R g) : clSmul (-1 : R) z = -z := by
  rw [← scalar_mul_cl, scalar_neg_one_eq, neg_mul_eq, one_mul_eq]

private theorem clSmul_one_eq {g : List R} (z : Cl R g) : clSmul (1 : R) z = z := by
  rw [← scalar_mul_cl, scalar_one, one_mul_eq]

/-- Helper: if `w : Cl R gs` satisfies `w * clInvol w = 0`, then `(0, w) : Cl R (c :: gs)`
    is square-zero! -/
private theorem sq_zero_of_mul_invol_eq_zero (c : R) {gs : List R} {w : Cl R gs}
    (hw : w * clInvol w = 0) : @IsSqZero (Cl R (c :: gs)) _ (0, w) := by
  unfold IsSqZero
  apply Prod.ext
  · change (0 : Cl R gs) * 0 + clSmul c (w * clInvol w) = 0
    rw [mul_zero_eq, zero_add_eq, hw, ← scalar_mul_cl, mul_zero_eq]
  · change (0 : Cl R gs) * w + w * clInvol (clZero gs) = 0
    rw [zero_mul_eq, clInvol_zero gs]
    change (0 : Cl R gs) + w * 0 = 0
    rw [mul_zero_eq, add_zero_eq]

/-- Helper: in any associative ring, if `u * u = 1`, then `(1 + u) * (1 - u) = 0`. -/
private theorem one_add_mul_one_sub_of_sq_one {A : Type u} [AssocRing A] {u : A}
    (hu : u * u = 1) : (1 + u) * (1 - u) = 0 := by
  let o : A := 1
  change (o + u) * (o - u) = 0
  rw [AssocRing.right_distrib, one_mul_eq, mul_sub_distrib, mul_one_eq, hu,
      AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg]
  calc
    (o + -u) + (u + -o)
      = o + (-u + (u + -o)) := AssocRing.add_assoc o (-u) (u + -o)
    _ = o + ((-u + u) + -o) := by rw [← AssocRing.add_assoc (-u) u (-o)]
    _ = o + (0 + -o) := by rw [neg_add_cancel_eq]
    _ = o + -o := by rw [zero_add_eq]
    _ = 0 := add_neg_cancel o

/-- Explicit nonzero multivector `x = (1 + e_1) e_0 = e_0 + e_1 e_0` in positive-definite
    Euclidean `Cl_{2,0}(R) = Cl R [1, 1]`. -/
def nilpotentCl20 : Cl R (sigList R 2 0) :=
  let e1 : Cl R [1] := ((0 : R), (1 : R))
  ((0 : Cl R [1]), (1 : Cl R [1]) + e1)

theorem nilpotentCl20_ne_zero : (nilpotentCl20 : Cl R (sigList R 2 0)) ≠ 0 := by
  intro h0
  have hsp := congrArg (fun z : Cl R [1, 1] => scalarPart [1] z.2) h0
  dsimp only [nilpotentCl20] at hsp
  change (1 : R) + 0 = 0 at hsp
  rw [add_zero_eq] at hsp
  exact IntegralDomain.zero_ne_one hsp.symm

theorem nilpotentCl20_sq_zero : IsSqZero (nilpotentCl20 : Cl R (sigList R 2 0)) := by
  let e1 : Cl R [1] := ((0 : R), (1 : R))
  have he1_sq : e1 * e1 = 1 := by
    apply Prod.ext
    · change (0 : R) * 0 + 1 * (1 * (1 : R)) = 1
      rw [mul_zero_eq (A := R), zero_add_eq (A := R), one_mul_eq (A := R), one_mul_eq (A := R)]
    · change (0 : R) * 1 + 1 * (0 : R) = 0
      rw [zero_mul_eq (A := R), mul_zero_eq (A := R), add_zero_eq (A := R)]
  have he1_inv : clInvol e1 = -e1 := by
    apply Prod.ext
    · exact (neg_zero_eq (A := R)).symm
    · rfl
  let w : Cl R [1] := 1 + e1
  have hw_inv : clInvol w = 1 - e1 := by
    change clInvol (clAdd (clOne [1]) e1) = 1 - e1
    rw [clInvol_add, clInvol_one, he1_inv]
    exact (AssocRing.sub_eq_add_neg (1 : Cl R [1]) e1).symm
  have hw_prod : w * clInvol w = 0 := by
    rw [hw_inv]
    exact one_add_mul_one_sub_of_sq_one he1_sq
  exact sq_zero_of_mul_invol_eq_zero (c := 1) (gs := [1]) hw_prod

/-- **Counterexample Theorem 1A (`+Q` convention, signature `(2, 0)`):**
    In strictly positive-definite `2`-dimensional Euclidean space `sigList R 2 0`,
    there are **zero** nonzero isotropic vectors, yet `Cl_{2,0}(R)` possesses an explicit
    nonzero square-zero (nilpotent) multivector `nilpotentCl20`. -/
theorem refutation_pos_def_plus_conv :
    ¬ HasIsotropic (sigList R 2 0) ∧
    ∃ z : Cl R (sigList R 2 0), z ≠ 0 ∧ IsSqZero z ∧ IsNilpotent z := by
  refine ⟨?_, nilpotentCl20, nilpotentCl20_ne_zero, nilpotentCl20_sq_zero,
          isNilpotent_of_isSqZero nilpotentCl20_sq_zero⟩
  intro hiso
  have ⟨_, hq⟩ := (hasIsotropic_sigList_iff (R := R) 2 0).mp hiso
  omega

/-- Volume element `ω₂ = e_1 e_2` of `Cl_{0,2}(R) = Cl R [-1, -1]`. -/
private def omegaCl02 : Cl R [-1, -1] :=
  ((0 : Cl R [-1]), ((0 : R), (1 : R)))

private theorem omegaCl02_invol :
    clInvol (omegaCl02 : Cl R [-1, -1]) = omegaCl02 := by
  let f2 : Cl R [-1] := ((0 : R), (1 : R))
  have hf2_inv : clInvol f2 = -f2 := Prod.ext (neg_zero_eq (A := R)).symm rfl
  apply Prod.ext
  · exact clInvol_zero [-1]
  · change clNeg (clInvol f2) = f2
    rw [hf2_inv]
    exact neg_neg_eq f2

private theorem omegaCl02_sq :
    (omegaCl02 : Cl R [-1, -1]) * omegaCl02 = -1 := by
  let f2 : Cl R [-1] := ((0 : R), (1 : R))
  have hf2_inv : clInvol f2 = -f2 := Prod.ext (neg_zero_eq (A := R)).symm rfl
  have hf2_sq : f2 * f2 = -1 := by
    apply Prod.ext
    · change (0 : R) * 0 + (-1 : R) * (1 * (1 : R)) = -1
      rw [mul_zero_eq (A := R), zero_add_eq (A := R), one_mul_eq (A := R), mul_one_eq (A := R)]
    · change (0 : R) * 1 + 1 * (0 : R) = -(0 : R)
      rw [zero_mul_eq (A := R), mul_zero_eq (A := R), add_zero_eq (A := R), neg_zero_eq (A := R)]
  apply Prod.ext
  · change (0 : Cl R [-1]) * 0 + clSmul (-1 : R) (f2 * clInvol f2) = -(1 : Cl R [-1])
    rw [mul_zero_eq, zero_add_eq, hf2_inv, mul_neg_eq, hf2_sq, neg_neg_eq, clSmul_neg_one_eq]
  · change (0 : Cl R [-1]) * f2 + f2 * clInvol (clZero [-1]) = -(0 : Cl R [-1])
    rw [zero_mul_eq, clInvol_zero [-1]]
    change (0 : Cl R [-1]) + f2 * 0 = -(0 : Cl R [-1])
    rw [mul_zero_eq, add_zero_eq, neg_zero_eq]

/-- Volume element `ω₃ = e_1 e_2 e_3` in `Cl_{0,3}(R) = Cl R [-1, -1, -1]`. -/
private def omegaCl03 : Cl R [-1, -1, -1] :=
  ((0 : Cl R [-1, -1]), omegaCl02)

private theorem omegaCl03_invol :
    clInvol (omegaCl03 : Cl R [-1, -1, -1]) = -omegaCl03 := by
  apply Prod.ext
  · change clInvol (clZero [-1, -1]) = -(0 : Cl R [-1, -1])
    rw [clInvol_zero]
    exact (neg_zero_eq : -(0 : Cl R [-1, -1]) = 0).symm
  · change -(clInvol (omegaCl02 : Cl R [-1, -1])) = -omegaCl02
    rw [omegaCl02_invol]

private theorem omegaCl03_sq_one :
    (omegaCl03 : Cl R [-1, -1, -1]) * omegaCl03 = 1 := by
  apply Prod.ext
  · change (0 : Cl R [-1, -1]) * 0 + clSmul (-1 : R) (omegaCl02 * clInvol omegaCl02) = 1
    rw [mul_zero_eq, zero_add_eq, omegaCl02_invol, omegaCl02_sq, clSmul_neg_one_eq, neg_neg_eq]
  · change (0 : Cl R [-1, -1]) * omegaCl02 + omegaCl02 * clInvol (clZero [-1, -1]) = 0
    rw [zero_mul_eq, clInvol_zero]
    change (0 : Cl R [-1, -1]) + omegaCl02 * 0 = 0
    rw [mul_zero_eq, add_zero_eq]

/-- Explicit nonzero multivector `y = (1 + e_1 e_2 e_3) e_0 = e_0 + e_1 e_2 e_3 e_0`
    in positive-definite `Cl_{0,4}(R) = Cl R [-1, -1, -1, -1]` (`-Q` convention). -/
def nilpotentCl04 : Cl R (sigList R 0 4) :=
  ((0 : Cl R [-1, -1, -1]), (1 : Cl R [-1, -1, -1]) + omegaCl03)

theorem nilpotentCl04_ne_zero : (nilpotentCl04 : Cl R (sigList R 0 4)) ≠ 0 := by
  intro h0
  have hsp := congrArg (fun z : Cl R [-1, -1, -1, -1] => scalarPart [-1, -1, -1] z.2) h0
  dsimp only [nilpotentCl04] at hsp
  change (1 : R) + 0 = 0 at hsp
  rw [add_zero_eq] at hsp
  exact IntegralDomain.zero_ne_one hsp.symm

theorem nilpotentCl04_sq_zero : IsSqZero (nilpotentCl04 : Cl R (sigList R 0 4)) := by
  let w : Cl R [-1, -1, -1] := 1 + omegaCl03
  have hw_inv : clInvol w = 1 - omegaCl03 := by
    change clInvol (clAdd (clOne [-1, -1, -1]) omegaCl03) = 1 - omegaCl03
    rw [clInvol_add, clInvol_one, omegaCl03_invol]
    exact (AssocRing.sub_eq_add_neg (1 : Cl R [-1, -1, -1]) omegaCl03).symm
  have hw_prod : w * clInvol w = 0 := by
    rw [hw_inv]
    exact one_add_mul_one_sub_of_sq_one omegaCl03_sq_one
  exact sq_zero_of_mul_invol_eq_zero (c := -1) (gs := [-1, -1, -1]) hw_prod

/-- **Counterexample Theorem 1B (`-Q` convention, Euclidean `4`-space `Cl_{0,4}(R)`):**
    Under the opposite sign convention `v^2 = -Q(v)` (`sigList R 0 4 = negSig (sigList R 4 0)`),
    `4`-dimensional positive-definite Euclidean space still has **zero** nonzero isotropic
    vectors, yet `Cl_{0,4}(R)` possesses the explicit nonzero square-zero multivector
    `nilpotentCl04`. -/
theorem refutation_pos_def_minus_conv :
    ¬ HasIsotropic (sigList R 4 0) ∧
    ¬ HasIsotropic (sigList R 0 4) ∧
    ∃ z : Cl R (sigList R 0 4), z ≠ 0 ∧ IsSqZero z ∧ IsNilpotent z := by
  refine ⟨?_, ?_, nilpotentCl04, nilpotentCl04_ne_zero, nilpotentCl04_sq_zero,
          isNilpotent_of_isSqZero nilpotentCl04_sq_zero⟩
  · intro hiso
    have ⟨_, hq⟩ := (hasIsotropic_sigList_iff (R := R) 4 0).mp hiso
    omega
  · intro hiso
    have ⟨hp, _⟩ := (hasIsotropic_sigList_iff (R := R) 0 4).mp hiso
    omega

/-! ### Reducedness of the Five Exceptional Signatures `(0,0), (1,0), (0,1), (0,2), (0,3)` -/

theorem cl00_no_sq_zero (z : Cl R (sigList R 0 0)) (hz : IsSqZero z) : z = 0 := by
  let r : R := z
  have hr : r * r = 0 := hz
  exact (sq_eq_zero_iff r).mp hr

theorem cl10_no_sq_zero (z : Cl R (sigList R 1 0)) (hz : IsSqZero z) : z = 0 := by
  match z with
  | (a, b) =>
    let a' : R := a
    let b' : R := b
    have hfst : a' * a' + (1 : R) * (b' * b') = 0 := congrArg Prod.fst hz
    rw [one_mul_eq] at hfst
    have ⟨ha, hb⟩ := sum_two_sq_eq_zero hfst
    exact Prod.ext ha hb

theorem cl01_comm (u v : Cl R [-1]) : u * v = v * u := by
  match u, v with
  | (a1, b1), (a2, b2) =>
    let a1' : R := a1; let b1' : R := b1; let a2' : R := a2; let b2' : R := b2
    apply Prod.ext
    · change a1' * a2' + (-1 : R) * (b1' * b2') = a2' * a1' + (-1 : R) * (b2' * b1')
      rw [CommRing.mul_comm a1' a2', CommRing.mul_comm b1' b2']
    · change a1' * b2' + b1' * a2' = a2' * b1' + b2' * a1'
      rw [CommRing.mul_comm a1' b2', CommRing.mul_comm b1' a2', AssocRing.add_comm]

theorem cl01_no_sq_zero (z : Cl R (sigList R 0 1)) (hz : IsSqZero z) : z = 0 := by
  match z with
  | (a, b) =>
    let a' : R := a
    let b' : R := b
    have hfst : a' * a' + (-1 : R) * (b' * b') = 0 := congrArg Prod.fst hz
    have hsnd : a' * b' + b' * a' = 0 := congrArg Prod.snd hz
    rw [CommRing.mul_comm b' a'] at hsnd
    have hab : a' * b' = 0 := eq_zero_of_add_self_eq_zero hsnd
    cases IntegralDomain.mul_eq_zero a' b' hab with
    | inl ha =>
      have ha0 : a = (0 : R) := ha
      rw [ha, zero_mul_eq, zero_add_eq, neg_mul_eq, one_mul_eq] at hfst
      have hb2 : b' * b' = 0 := eq_zero_of_neg_eq_zero hfst
      have hb0 : b = (0 : R) := (sq_eq_zero_iff b').mp hb2
      exact Prod.ext ha0 hb0
    | inr hb =>
      have hb0 : b = (0 : R) := hb
      rw [hb, mul_zero_eq, mul_zero_eq, add_zero_eq] at hfst
      have ha0 : a = (0 : R) := (sq_eq_zero_iff a').mp hfst
      exact Prod.ext ha0 hb0

private def normCl01 (u : Cl R [-1]) : R :=
  let a : R := u.1
  let b : R := u.2
  a * a + b * b

private theorem cl01_mul_invol (u : Cl R [-1]) :
    u * clInvol u = scalar [-1] (normCl01 u) := by
  match u with
  | (a, b) =>
    let a' : R := a
    let b' : R := b
    apply Prod.ext
    · change a' * a' + (-1 : R) * (b' * -b') = (a' * a' + b' * b') * 1
      rw [mul_neg_eq, neg_mul_neg, one_mul_eq, mul_one_eq]
    · change a' * -b' + b' * a' = (a' * a' + b' * b') * 0
      rw [mul_neg_eq, CommRing.mul_comm b' a', neg_add_cancel_eq, mul_zero_eq]

private def conjCl02 (z : Cl R [-1, -1]) : Cl R [-1, -1] :=
  (clInvol z.1, -z.2)

private def normCl02 (z : Cl R [-1, -1]) : R :=
  normCl01 z.1 + normCl01 z.2

private theorem cl02_mul_conj (z : Cl R [-1, -1]) :
    z * conjCl02 z = scalar [-1, -1] (normCl02 z) := by
  match z with
  | (u, v) =>
    unfold conjCl02 normCl02
    rw [scalar_cons]
    apply Prod.ext
    · change u * clInvol u + clSmul (-1 : R) (v * clInvol (clNeg v)) =
        scalar [-1] (normCl01 u + normCl01 v)
      rw [clInvol_neg]
      change u * clInvol u + clSmul (-1 : R) (v * -(clInvol v)) =
        scalar [-1] (normCl01 u + normCl01 v)
      rw [mul_neg_eq, clSmul_neg_one_eq, neg_neg_eq,
          cl01_mul_invol u, cl01_mul_invol v, ← scalar_add]
    · change u * (-v) + v * clInvol (clInvol u) = (0 : Cl R [-1])
      rw [clInvol_invol, mul_neg_eq, cl01_comm v u, neg_add_cancel_eq]

private theorem cl02_no_sq_zero_aux (z : Cl R [-1, -1]) (hz : z * z = 0) : z = 0 := by
  have hprod : (z * z) * (conjCl02 z * conjCl02 z) =
      scalar [-1, -1] (normCl02 z * normCl02 z) := by
    calc
      (z * z) * (conjCl02 z * conjCl02 z)
        = z * (z * (conjCl02 z * conjCl02 z)) := AssocRing.mul_assoc z z _
      _ = z * ((z * conjCl02 z) * conjCl02 z) := by rw [← AssocRing.mul_assoc z (conjCl02 z)]
      _ = z * (scalar [-1, -1] (normCl02 z) * conjCl02 z) := by rw [cl02_mul_conj]
      _ = z * clSmul (normCl02 z) (conjCl02 z) := by rw [scalar_mul_cl]
      _ = z * (conjCl02 z * scalar [-1, -1] (normCl02 z)) := by rw [← cl_mul_scalar]
      _ = (z * conjCl02 z) * scalar [-1, -1] (normCl02 z) := by rw [← AssocRing.mul_assoc]
      _ = scalar [-1, -1] (normCl02 z) * scalar [-1, -1] (normCl02 z) := by rw [cl02_mul_conj]
      _ = scalar [-1, -1] (normCl02 z * normCl02 z) := (scalar_mul [-1, -1] _ _).symm
  rw [hz, zero_mul_eq] at hprod
  have hN2 : normCl02 z * normCl02 z = 0 := (scalar_eq_zero_iff [-1, -1] _).mp hprod.symm
  have hN : normCl02 z = 0 := (sq_eq_zero_iff (normCl02 z)).mp hN2
  match z, hN with
  | ((a, b), (c, d)), h4 =>
    let a' : R := a; let b' : R := b; let c' : R := c; let d' : R := d
    have h4' : (a' * a' + b' * b') + (c' * c' + d' * d') = 0 := h4
    have ⟨ha, hb, hc, hd⟩ := sum_four_sq_eq_zero h4'
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)

theorem cl02_no_sq_zero (z : Cl R (sigList R 0 2)) (hz : IsSqZero z) : z = 0 :=
  cl02_no_sq_zero_aux z hz

private theorem omegaCl02_invol_comm (w : Cl R [-1, -1]) :
    omegaCl02 * w = clInvol w * omegaCl02 := by
  match w with
  | (u, v) =>
    let e2 : Cl R [-1] := ((0 : R), (1 : R))
    have he2_inv : clInvol e2 = -e2 := Prod.ext (neg_zero_eq (A := R)).symm rfl
    apply Prod.ext
    · change (0 : Cl R [-1]) * u + clSmul (-1 : R) (e2 * clInvol v) =
        clInvol u * 0 + clSmul (-1 : R) ((-clInvol v) * clInvol e2)
      rw [zero_mul_eq, mul_zero_eq, zero_add_eq, zero_add_eq, he2_inv, neg_mul_neg,
          cl01_comm (clInvol v) e2]
    · change (0 : Cl R [-1]) * v + e2 * clInvol u =
        clInvol u * e2 + (-clInvol v) * clInvol (clZero [-1])
      rw [zero_mul_eq, zero_add_eq, clInvol_zero [-1]]
      change e2 * clInvol u = clInvol u * e2 + (-clInvol v) * 0
      rw [mul_zero_eq, add_zero_eq, cl01_comm e2 (clInvol u)]

private theorem projCl03_hom (sgn : Cl R [-1, -1]) (hsgn_sq : sgn * sgn = -1)
    (hsgn_comm : ∀ w : Cl R [-1, -1], sgn * w = clInvol w * sgn)
    (z1 z2 : Cl R [-1, -1, -1]) :
    (z1 * z2).1 + (z1 * z2).2 * sgn = (z1.1 + z1.2 * sgn) * (z2.1 + z2.2 * sgn) := by
  match z1, z2 with
  | (u1, v1), (u2, v2) =>
    change (u1 * u2 + clSmul (-1 : R) (v1 * clInvol v2)) + (u1 * v2 + v1 * clInvol u2) * sgn =
      (u1 + v1 * sgn) * (u2 + v2 * sgn)
    have ht1 : (v1 * sgn) * u2 = (v1 * clInvol u2) * sgn := by
      rw [AssocRing.mul_assoc, hsgn_comm u2, ← AssocRing.mul_assoc]
    have ht2 : (v1 * sgn) * (v2 * sgn) = clSmul (-1 : R) (v1 * clInvol v2) := by
      calc
        (v1 * sgn) * (v2 * sgn)
          = v1 * (sgn * (v2 * sgn)) := AssocRing.mul_assoc v1 sgn (v2 * sgn)
        _ = v1 * ((sgn * v2) * sgn) := by rw [← AssocRing.mul_assoc sgn v2 sgn]
        _ = v1 * ((clInvol v2 * sgn) * sgn) := by rw [hsgn_comm v2]
        _ = v1 * (clInvol v2 * (sgn * sgn)) := by rw [AssocRing.mul_assoc (clInvol v2) sgn sgn]
        _ = v1 * (clInvol v2 * (-1)) := by rw [hsgn_sq]
        _ = (v1 * clInvol v2) * (-1) := by rw [← AssocRing.mul_assoc]
        _ = -((v1 * clInvol v2) * 1) := mul_neg_eq _ 1
        _ = -(v1 * clInvol v2) := by rw [mul_one_eq]
        _ = clSmul (-1 : R) (v1 * clInvol v2) := (clSmul_neg_one_eq _).symm
    rw [AssocRing.right_distrib (u1 * v2) (v1 * clInvol u2) sgn, AssocRing.mul_assoc u1 v2 sgn,
        AssocRing.right_distrib u1 (v1 * sgn) (u2 + v2 * sgn),
        AssocRing.left_distrib u1 u2 (v2 * sgn),
        AssocRing.left_distrib (v1 * sgn) u2 (v2 * sgn), ht1, ht2]
    let A := u1 * u2
    let B := clSmul (-1 : R) (v1 * clInvol v2)
    let C := u1 * (v2 * sgn)
    let D := (v1 * clInvol u2) * sgn
    calc
      (A + B) + (C + D)
        = A + (B + (C + D)) := AssocRing.add_assoc A B (C + D)
      _ = A + ((C + D) + B) := by rw [AssocRing.add_comm B (C + D)]
      _ = A + (C + (D + B)) := by rw [AssocRing.add_assoc C D B]
      _ = (A + C) + (D + B) := by rw [← AssocRing.add_assoc A C (D + B)]

private theorem cl03_no_sq_zero_aux (z : Cl R [-1, -1, -1]) (hz : z * z = 0) : z = 0 := by
  have hp_hom := projCl03_hom (R := R) omegaCl02 omegaCl02_sq omegaCl02_invol_comm z z
  have hm_sq : (-omegaCl02 : Cl R [-1, -1]) * (-omegaCl02) = -1 := by
    rw [neg_mul_neg, omegaCl02_sq]
  have hm_comm : ∀ w : Cl R [-1, -1], (-omegaCl02) * w = clInvol w * (-omegaCl02) := by
    intro w
    rw [neg_mul_eq, mul_neg_eq, omegaCl02_invol_comm w]
  have hm_hom := projCl03_hom (R := R) (-omegaCl02) hm_sq hm_comm z z
  rw [hz] at hp_hom hm_hom
  have hz0_lhs1 : (0 : Cl R [-1, -1, -1]).1 + (0 : Cl R [-1, -1, -1]).2 * omegaCl02 = 0 := by
    change (0 : Cl R [-1, -1]) + 0 * omegaCl02 = 0
    rw [zero_mul_eq, add_zero_eq]
  have hz0_lhs2 : (0 : Cl R [-1, -1, -1]).1 + (0 : Cl R [-1, -1, -1]).2 * (-omegaCl02) = 0 := by
    change (0 : Cl R [-1, -1]) + 0 * (-omegaCl02) = 0
    rw [zero_mul_eq, add_zero_eq]
  rw [hz0_lhs1] at hp_hom
  rw [hz0_lhs2] at hm_hom
  have hp0 : z.1 + z.2 * omegaCl02 = 0 := cl02_no_sq_zero_aux _ hp_hom.symm
  have hm0 : z.1 + z.2 * (-omegaCl02) = 0 := cl02_no_sq_zero_aux _ hm_hom.symm
  rw [mul_neg_eq] at hm0
  have h2u : z.1 + z.1 = 0 := by
    calc
      z.1 + z.1 = z.1 + (z.1 + (z.2 * omegaCl02 + -(z.2 * omegaCl02))) := by
        rw [add_neg_cancel, add_zero_eq]
      _ = z.1 + ((z.1 + z.2 * omegaCl02) + -(z.2 * omegaCl02)) := by
        rw [← AssocRing.add_assoc z.1 (z.2 * omegaCl02)]
      _ = z.1 + ((z.2 * omegaCl02 + z.1) + -(z.2 * omegaCl02)) := by
        rw [AssocRing.add_comm z.1 (z.2 * omegaCl02)]
      _ = z.1 + (z.2 * omegaCl02 + (z.1 + -(z.2 * omegaCl02))) := by
        rw [AssocRing.add_assoc (z.2 * omegaCl02) z.1]
      _ = (z.1 + z.2 * omegaCl02) + (z.1 + -(z.2 * omegaCl02)) := by
        rw [← AssocRing.add_assoc z.1 (z.2 * omegaCl02)]
      _ = 0 + 0 := by rw [hp0, hm0]
      _ = 0 := add_zero_eq 0
  have hu0 : z.1 = 0 := by
    match z.1, h2u with
    | ((a, b), (c, d)), h =>
      let a' : R := a; let b' : R := b; let c' : R := c; let d' : R := d
      have ha : a' = 0 := eq_zero_of_add_self_eq_zero (R := R) (congrArg (fun q => q.1.1) h)
      have hb : b' = 0 := eq_zero_of_add_self_eq_zero (R := R) (congrArg (fun q => q.1.2) h)
      have hc : c' = 0 := eq_zero_of_add_self_eq_zero (R := R) (congrArg (fun q => q.2.1) h)
      have hd : d' = 0 := eq_zero_of_add_self_eq_zero (R := R) (congrArg (fun q => q.2.2) h)
      exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
  rw [hu0, zero_add_eq] at hp0
  have hv0 : z.2 = 0 := by
    have hv_sq := congrArg (fun q => q * omegaCl02) hp0
    dsimp only at hv_sq
    rw [zero_mul_eq, AssocRing.mul_assoc, omegaCl02_sq, mul_neg_eq, mul_one_eq] at hv_sq
    exact eq_zero_of_neg_eq_zero hv_sq
  match z with
  | (u, v) => exact Prod.ext hu0 hv0

theorem cl03_no_sq_zero (z : Cl R (sigList R 0 3)) (hz : IsSqZero z) : z = 0 :=
  cl03_no_sq_zero_aux z hz

/-- Lift a nonzero square-zero element along `sigList R p 0` (`p ≥ 2`). -/
private theorem exists_sq_zero_pos_def : ∀ k : Nat,
    ∃ z : Cl R (sigList R (k + 2) 0), z ≠ 0 ∧ IsSqZero z
  | 0 => ⟨nilpotentCl20, nilpotentCl20_ne_zero, nilpotentCl20_sq_zero⟩
  | k + 1 => by
    have ⟨z, hz_ne, hz_sq⟩ := exists_sq_zero_pos_def k
    exact ⟨embedSub 1 z, embedSub_ne_zero hz_ne, embedSub_sq_zero hz_sq⟩

/-- Lift a nonzero square-zero element along `sigList R 0 q` (`q ≥ 4`). -/
private theorem exists_sq_zero_neg_def : ∀ k : Nat,
    ∃ z : Cl R (sigList R 0 (k + 4)), z ≠ 0 ∧ IsSqZero z
  | 0 => ⟨nilpotentCl04, nilpotentCl04_ne_zero, nilpotentCl04_sq_zero⟩
  | k + 1 => by
    have ⟨z, hz_ne, hz_sq⟩ := exists_sq_zero_neg_def k
    exact ⟨embedSub (-1) z, embedSub_ne_zero hz_ne, embedSub_sq_zero hz_sq⟩

/-- The five exceptional signatures `(0,0), (1,0), (0,1), (0,2), (0,3)` where `Cl_{p,q}(R)`
    is reduced (`ℝ`, `ℝ ⊕ ℝ`, `ℂ`, `ℍ`, `ℍ ⊕ ℍ`). -/
def IsReducedSignature (p q : Nat) : Prop :=
  (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 0 ∧ q = 2) ∨ (p = 0 ∧ q = 3)

/-- **Sharp Classification Theorem (`Cl_{p,q}(R)` Nilpotent Existence):**
    Over any ordered integral domain `R` (including `ℤ`, `ℚ`, and `ℝ`), the full Clifford
    algebra `Cl_{p,q}(R)` contains a nonzero nilpotent element (of arbitrary index `k ≥ 1`,
    equivalently of index `2`) if and only if `(p, q)` is NOT one of the five low-dimensional
    reduced signatures `(0,0), (1,0), (0,1), (0,2), (0,3)`. -/
theorem cl_has_nilpotent_iff (p q : Nat) :
    (∃ z : Cl R (sigList R p q), z ≠ 0 ∧ IsNilpotent z) ↔ ¬ IsReducedSignature p q := by
  rw [exists_nonzero_nilpotent_iff_exists_nonzero_sq_zero]
  constructor
  · intro ⟨z, hz_ne, hz_sq⟩ hred
    rcases hred with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hz_ne (cl00_no_sq_zero z hz_sq)
    · exact hz_ne (cl10_no_sq_zero z hz_sq)
    · exact hz_ne (cl01_no_sq_zero z hz_sq)
    · exact hz_ne (cl02_no_sq_zero z hz_sq)
    · exact hz_ne (cl03_no_sq_zero z hz_sq)
  · intro hnot
    match p, q with
    | 0, 0 => exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    | 1, 0 => exact False.elim (hnot (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    | 0, 1 => exact False.elim (hnot (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    | 0, 2 => exact False.elim (hnot (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    | 0, 3 => exact False.elim (hnot (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    | p' + 2, 0 => exact exists_sq_zero_pos_def p'
    | 0, q' + 4 => exact exists_sq_zero_neg_def q'
    | p' + 1, q' + 1 =>
      have ⟨v, hiso⟩ := (hasIsotropic_sigList_iff (R := R) (p' + 1) (q' + 1)).mpr ⟨by omega, by omega⟩
      exact ⟨embedVec v, (grade1_sq_zero_iff v).mpr hiso⟩

end PositiveDefiniteNilpotents

/-! ## Part 2: Null-Vector Sum Refutation & Polar Orthogonality Criterion -/

section NullVectorSum

variable {R : Type u} [OrderedDomain R]

/-- **Polar Orthogonality Criterion for Sums of Two Null Vectors:**
    If `Q_g(u) = 0` and `Q_g(w) = 0`, then in `Cl R g`, `(embedVec u + embedVec w)` is
    nilpotent (or square-zero) if and only if `polarForm g u w = 0`. -/
theorem null_vector_sum_sq_zero_iff {g : List R} {u w : Vec R g}
    (hu : quadForm g u = 0) (hw : quadForm g w = 0) :
    IsSqZero (embedVec u + embedVec w) ↔ polarForm g u w = 0 := by
  unfold IsSqZero
  rw [← embedVec_add, embedVec_sq, polarization_identity, hu, hw,
      add_zero_eq, zero_add_eq, scalar_eq_zero_iff]
  constructor
  · exact eq_zero_of_two_mul_eq_zero
  · intro hp
    rw [hp, mul_zero_eq]

theorem null_vector_sum_nilpotent_iff {g : List R} {u w : Vec R g}
    (hu : quadForm g u = 0) (hw : quadForm g w = 0) :
    IsNilpotent (embedVec u + embedVec w) ↔ polarForm g u w = 0 := by
  constructor
  · intro hnil
    by_cases hsum0 : embedVec u + embedVec w = 0
    · apply (null_vector_sum_sq_zero_iff hu hw).mp
      unfold IsSqZero
      rw [hsum0, zero_mul_eq]
    · rw [← embedVec_add] at hsum0 hnil
      have hiso : IsIsotropic g (u + w) := (grade1_nilpotent_iff (u + w)).mp ⟨hsum0, hnil⟩
      have hsq : IsSqZero (embedVec u + embedVec w) := by
        rw [← embedVec_add]
        exact ((grade1_sq_zero_iff (u + w)).mpr hiso).2
      exact (null_vector_sum_sq_zero_iff hu hw).mp hsq
  · intro hp
    exact isNilpotent_of_isSqZero ((null_vector_sum_sq_zero_iff hu hw).mpr hp)

/-- Explicit null vector `u = e_1 + e_2` in `sigList R 1 1 = [1, -1]`. -/
def nullVecPlus : Vec R (sigList R 1 1) := (1, (1, PUnit.unit))

/-- Explicit null vector `w = e_1 - e_2` in `sigList R 1 1 = [1, -1]`. -/
def nullVecMinus : Vec R (sigList R 1 1) := (1, (-1, PUnit.unit))

/-- **Counterexample Theorem 2 (Refutation of the Null-Vector Sum Construction):**
    In `Cl_{1,1}(R)`, `u = e_1 + e_2` and `w = e_1 - e_2` are both nonzero isotropic (null)
    vectors satisfying `(embedVec u)^2 = 0`, `(embedVec w)^2 = 0`, and even
    `(embedVec u)^2 + (embedVec w)^2 = 0`; YET their sum `embedVec u + embedVec w` satisfies
    `(embedVec u + embedVec w)^2 = scalar [1, -1] ((1 + 1) * (1 + 1)) ≠ 0`, is NOT nilpotent
    of ANY index `k ≥ 1`, and `u + w` is NOT isotropic! -/
theorem refutation_null_vector_sum :
    IsIsotropic (sigList R 1 1) nullVecPlus ∧
    IsIsotropic (sigList R 1 1) nullVecMinus ∧
    IsSqZero (embedVec (nullVecPlus : Vec R (sigList R 1 1))) ∧
    IsSqZero (embedVec (nullVecMinus : Vec R (sigList R 1 1))) ∧
    (embedVec (nullVecPlus : Vec R (sigList R 1 1)) * embedVec nullVecPlus +
     embedVec (nullVecMinus : Vec R (sigList R 1 1)) * embedVec nullVecMinus = 0) ∧
    ((embedVec (nullVecPlus : Vec R (sigList R 1 1)) + embedVec nullVecMinus) *
     (embedVec nullVecPlus + embedVec nullVecMinus) = scalar (sigList R 1 1) ((1 + 1) * (1 + 1))) ∧
    ¬ IsNilpotent (embedVec (nullVecPlus : Vec R (sigList R 1 1)) + embedVec nullVecMinus) ∧
    ¬ IsIsotropic (sigList R 1 1) (nullVecPlus + nullVecMinus) := by
  have hu_iso : IsIsotropic (sigList R 1 1) (nullVecPlus : Vec R (sigList R 1 1)) := by
    refine ⟨?_, ?_⟩
    · intro h0; injection h0 with h10 _; exact IntegralDomain.zero_ne_one h10.symm
    · change (1 : R) * (1 * 1) + ((-1 : R) * (1 * 1) + 0) = 0
      rw [add_zero_eq, one_mul_eq, one_mul_eq, neg_mul_eq, one_mul_eq, add_neg_cancel]
  have hw_iso : IsIsotropic (sigList R 1 1) (nullVecMinus : Vec R (sigList R 1 1)) := by
    refine ⟨?_, ?_⟩
    · intro h0; injection h0 with h10 _; exact IntegralDomain.zero_ne_one h10.symm
    · change (1 : R) * (1 * 1) + ((-1 : R) * ((-1 : R) * (-1)) + 0) = 0
      rw [add_zero_eq, neg_mul_neg, one_mul_eq, one_mul_eq, neg_mul_eq, one_mul_eq, add_neg_cancel]
  have hu_sq : IsSqZero (embedVec (nullVecPlus : Vec R (sigList R 1 1))) :=
    ((grade1_sq_zero_iff nullVecPlus).mpr hu_iso).2
  have hw_sq : IsSqZero (embedVec (nullVecMinus : Vec R (sigList R 1 1))) :=
    ((grade1_sq_zero_iff nullVecMinus).mpr hw_iso).2
  have hsum_sq_eq : embedVec (nullVecPlus : Vec R (sigList R 1 1)) * embedVec nullVecPlus +
      embedVec (nullVecMinus : Vec R (sigList R 1 1)) * embedVec nullVecMinus = 0 := by
    change IsSqZero _ at hu_sq hw_sq
    rw [hu_sq, hw_sq, add_zero_eq]
  have hpolar : polarForm (sigList R 1 1) (nullVecPlus : Vec R (sigList R 1 1)) nullVecMinus = 1 + 1 := by
    change (1 : R) * (1 * 1) + ((-1 : R) * (1 * -1) + 0) = 1 + 1
    rw [add_zero_eq, one_mul_eq, one_mul_eq, mul_neg_eq, one_mul_eq, neg_mul_neg, one_mul_eq]
  have hsq_sum : (embedVec (nullVecPlus : Vec R (sigList R 1 1)) + embedVec nullVecMinus) *
      (embedVec nullVecPlus + embedVec nullVecMinus) =
      scalar (sigList R 1 1) ((1 + 1) * (1 + 1)) := by
    rw [← embedVec_add, embedVec_sq, polarization_identity, hu_iso.2, hw_iso.2,
        add_zero_eq, zero_add_eq, hpolar]
  have hnot_nil : ¬ IsNilpotent (embedVec (nullVecPlus : Vec R (sigList R 1 1)) + embedVec nullVecMinus) := by
    rw [null_vector_sum_nilpotent_iff hu_iso.2 hw_iso.2, hpolar]
    exact two_ne_zero
  have hnot_iso : ¬ IsIsotropic (sigList R 1 1) ((nullVecPlus : Vec R (sigList R 1 1)) + nullVecMinus) := by
    intro ⟨_, hq⟩
    rw [polarization_identity, hu_iso.2, hw_iso.2, add_zero_eq, zero_add_eq, hpolar] at hq
    exact two_ne_zero (eq_zero_of_two_mul_eq_zero hq)
  exact ⟨hu_iso, hw_iso, hu_sq, hw_sq, hsum_sq_eq, hsq_sum, hnot_nil, hnot_iso⟩

end NullVectorSum

/-! ## Part 3: Field-Theoretic, Degenerate, and Hasse–Minkowski Refutations of Signature -/

/-- **Counterexample Theorem 3A (Degenerate Inertia `(p, 0, r)` with `r ≥ 1`):**
    Over any ordered domain `R`, a positive-semidefinite degenerate form `inertiaList R p 0 r`
    with `r ≥ 1` has **zero negative squares** (`q = 0`), violating the nondegenerate indefinite
    condition `p ≥ 1 ∧ q ≥ 1`, yet still possesses a nonzero isotropic vector and a nonzero
    grade-1 Clifford nilpotent! -/
theorem refutation_degenerate_semidefinite {R : Type u} [OrderedDomain R] (p r : Nat) (hr : r ≥ 1) :
    ¬ (p ≥ 1 ∧ (0 : Nat) ≥ 1) ∧
    HasIsotropic (inertiaList R p 0 r) ∧
    ∃ v : Vec R (inertiaList R p 0 r), embedVec v ≠ 0 ∧ IsSqZero (embedVec v) := by
  have hiso : HasIsotropic (inertiaList R p 0 r) :=
    (hasIsotropic_inertiaList_iff (R := R) p 0 r).mpr (Or.inr hr)
  refine ⟨by omega, hiso, ?_⟩
  rcases hiso with ⟨v, hv⟩
  exact ⟨v, (grade1_sq_zero_iff v).mpr hv⟩

/-- **Counterexample Theorem 3B (Complex / Gaussian Integer Unsigned Sum of Squares):**
    Over `GaussInt = ℤ[i]`, the pure unsigned sum of two squares `Q(z_1, z_2) = z_1^2 + z_2^2`
    (`g = [1, 1]`, no negative terms!) admits the explicit nonzero isotropic vector `(1, i)`
    and nonzero grade-1 Clifford nilpotent `embedVec (1, i)`. -/
theorem refutation_complex_sum_of_squares :
    HasIsotropic ([1, 1] : List GaussInt) ∧
    ∃ v : Vec GaussInt [1, 1], embedVec v ≠ 0 ∧ IsSqZero (embedVec v) := by
  let v : Vec GaussInt [1, 1] := (1, (GaussInt.iUnit, PUnit.unit))
  have hv_ne : v ≠ 0 := by
    intro h0; injection h0 with h10 _; exact absurd h10 (by decide)
  have hv_iso : IsIsotropic ([1, 1] : List GaussInt) v := ⟨hv_ne, by decide⟩
  exact ⟨⟨v, hv_iso⟩, v, (grade1_sq_zero_iff v).mpr hv_iso⟩

/-- **Counterexample Theorem 3C (Finite Prime Fields `𝔽_5` and `𝔽_3` Sums of Squares):**
    Over `𝔽_5`, the pure sum of two squares `x_1^2 + x_2^2` has nonzero isotropic vector `(1, 2)`;
    over `𝔽_3`, the pure sum of three squares `x_1^2 + x_2^2 + x_3^2` has nonzero isotropic
    vector `(1, 1, 1)` (Chevalley–Warning phenomenon). -/
theorem refutation_finite_fields_sum_of_squares :
    (HasIsotropic ([1, 1] : List F5) ∧
     ∃ v : Vec F5 [1, 1], embedVec v ≠ 0 ∧ IsSqZero (embedVec v)) ∧
    (HasIsotropic ([1, 1, 1] : List F3) ∧
     ∃ w : Vec F3 [1, 1, 1], embedVec w ≠ 0 ∧ IsSqZero (embedVec w)) := by
  let v5 : Vec F5 [1, 1] := (1, (2, PUnit.unit))
  have hv5_ne : v5 ≠ 0 := by
    intro h0; injection h0 with h10 _; exact absurd h10 (by decide)
  have hv5 : IsIsotropic ([1, 1] : List F5) v5 := ⟨hv5_ne, by decide⟩
  let w3 : Vec F3 [1, 1, 1] := (1, (1, (1, PUnit.unit)))
  have hw3_ne : w3 ≠ 0 := by
    intro h0; injection h0 with h10 _; exact absurd h10 (by decide)
  have hw3 : IsIsotropic ([1, 1, 1] : List F3) w3 := ⟨hw3_ne, by decide⟩
  exact ⟨⟨⟨v5, hv5⟩, v5, (grade1_sq_zero_iff v5).mpr hv5⟩,
         ⟨⟨w3, hw3⟩, w3, (grade1_sq_zero_iff w3).mpr hw3⟩⟩

/-! ### Hasse–Minkowski Indefinite Obstructions over `ℤ` and `ℚ` -/

private def absNat : Int → Nat
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

private theorem absNat_sq_eq (a : Int) : ((absNat a * absNat a : Nat) : Int) = a * a := by
  cases a <;> rfl

private theorem eq_zero_of_absNat_eq_zero {a : Int} (h : absNat a = 0) : a = 0 := by
  cases a with
  | ofNat n =>
    change n = 0 at h
    subst h
    rfl
  | negSucc n =>
    change n + 1 = 0 at h
    omega

private theorem nat_mod2_sq (n : Nat) :
    (∃ q : Nat, n = q + q ∧ n * n = 4 * (q * q)) ∨
    (∃ q : Nat, n = q + q + 1 ∧ n * n = 4 * (q * q) + 4 * q + 1) := by
  let q := n / 2
  have hrem : n % 2 = 0 ∨ n % 2 = 1 := by omega
  cases hrem with
  | inl h0 =>
    left
    refine ⟨q, by omega, ?_⟩
    have hn : n = q + q := by omega
    rw [hn]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  | inr h1 =>
    right
    refine ⟨q, by omega, ?_⟩
    have hn : n = q + q + 1 := by omega
    rw [hn]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

private theorem nat_sq_eq_two_sq : ∀ n m : Nat, n * n = 2 * (m * m) → n = 0 ∧ m = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m h
    by_cases hn0 : n = 0
    · subst hn0
      have hm2 : m * m = 0 := by omega
      cases Nat.mul_eq_zero.mp hm2 with
      | inl hm => exact ⟨rfl, hm⟩
      | inr hm => exact ⟨rfl, hm⟩
    · cases nat_mod2_sq n with
      | inr hodd =>
        rcases hodd with ⟨q, _, hsq⟩
        omega
      | inl heven =>
        rcases heven with ⟨q, hn_eq, hsq⟩
        have hmq : m * m = 2 * (q * q) := by omega
        if hlt : m < n then
          have ⟨hm0, hq0⟩ := ih m hlt q hmq
          omega
        else
          have hnm : n ≤ m := by omega
          have hle_sq : n * n ≤ m * m := Nat.mul_le_mul hnm hnm
          have hn_pos : n * n > 0 := Nat.mul_pos (by omega) (by omega)
          omega

theorem int_sq_sub_two_sq_eq_zero {a b : Int} (h : a * a - 2 * (b * b) = 0) :
    a = 0 ∧ b = 0 := by
  have key (A B : Nat) (hk : (A : Int) - 2 * (B : Int) = 0) :
      A = 2 * B := by omega
  rw [← absNat_sq_eq a, ← absNat_sq_eq b] at h
  have hnat : absNat a * absNat a = 2 * (absNat b * absNat b) := key _ _ h
  have ⟨hna, hnb⟩ := nat_sq_eq_two_sq (absNat a) (absNat b) hnat
  exact ⟨eq_zero_of_absNat_eq_zero hna, eq_zero_of_absNat_eq_zero hnb⟩

private theorem nat_mod3_sq (x : Nat) :
    (∃ q : Nat, x = 3 * q ∧ x * x = 9 * (q * q)) ∨
    (∃ q : Nat, x = 3 * q + 1 ∧ x * x = 9 * (q * q) + 6 * q + 1) ∨
    (∃ q : Nat, x = 3 * q + 2 ∧ x * x = 9 * (q * q) + 12 * q + 4) := by
  let q := x / 3
  have hrem : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · left
    refine ⟨q, by omega, ?_⟩
    have hx : x = q + q + q := by omega
    rw [hx]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  · right; left
    refine ⟨q, by omega, ?_⟩
    have hx : x = q + q + q + 1 := by omega
    rw [hx]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · right; right
    refine ⟨q, by omega, ?_⟩
    have hx : x = q + q + q + 1 + 1 := by omega
    rw [hx]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

private theorem nat_two_sq_eq_three_sq :
    ∀ s a b c : Nat, a + b + c = s → a * a + b * b = 3 * (c * c) →
    a = 0 ∧ b = 0 ∧ c = 0 := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro a b c hs heq
    by_cases hs0 : s = 0
    · omega
    · rcases nat_mod3_sq a with ⟨qa, ha_eq, ha_sq⟩ | ⟨qa, _, ha_sq⟩ | ⟨qa, _, ha_sq⟩ <;>
      rcases nat_mod3_sq b with ⟨qb, hb_eq, hb_sq⟩ | ⟨qb, _, hb_sq⟩ | ⟨qb, _, hb_sq⟩
      · -- Only `(0 mod 3, 0 mod 3)` survives:
        rcases nat_mod3_sq c with ⟨qc, hc_eq, hc_sq⟩ | ⟨qc, _, hc_sq⟩ | ⟨qc, _, hc_sq⟩
        · have hsub_eq : qa * qa + qb * qb = 3 * (qc * qc) := by omega
          have hlt : qa + qb + qc < s := by omega
          have ⟨hqa, hqb, hqc⟩ := ih (qa + qb + qc) hlt qa qb qc rfl hsub_eq
          omega
        · omega
        · omega
      all_goals omega

theorem int_two_sq_sub_three_sq_eq_zero {a b c : Int}
    (h : a * a + b * b - 3 * (c * c) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have key (A B C : Nat)
      (hk : (A : Int) + (B : Int) - 3 * (C : Int) = 0) :
      A + B = 3 * C := by omega
  rw [← absNat_sq_eq a, ← absNat_sq_eq b, ← absNat_sq_eq c] at h
  have hnat : absNat a * absNat a + absNat b * absNat b = 3 * (absNat c * absNat c) :=
    key _ _ _ h
  have ⟨hna, hnb, hnc⟩ := nat_two_sq_eq_three_sq _ (absNat a) (absNat b) (absNat c) rfl hnat
  exact ⟨eq_zero_of_absNat_eq_zero hna, eq_zero_of_absNat_eq_zero hnb,
         eq_zero_of_absNat_eq_zero hnc⟩

/-- **Counterexample Theorem 3D (Hasse–Minkowski Obstructions in Indefinite Signatures):**
    Even over ordered domains/fields (`ℤ` and `ℚ`, via homogeneous clearing of denominators),
    indefinite real signature (`p ≥ 1 ∧ q ≥ 1`) is NOT sufficient for isotropy:
    1) `Q(x_1, x_2) = x_1^2 - 2 x_2^2` has signature `(1, 1)` (`1 > 0`, `-2 < 0`), yet admits
       no nonzero integer or rational isotropic vector!
    2) `Q(x_1, x_2, x_3) = x_1^2 + x_2^2 - 3 x_3^2` has signature `(2, 1)` (`1, 1 > 0`, `-3 < 0`),
       yet admits no nonzero integer or rational isotropic vector! -/
theorem refutation_hasse_minkowski_indefinite :
    ¬ HasIsotropic ([1, -2] : List Int) ∧
    (∀ a1 d1 a2 d2 : Int, d1 ≠ 0 → d2 ≠ 0 →
      (a1 * d2) * (a1 * d2) - 2 * ((a2 * d1) * (a2 * d1)) = 0 → a1 = 0 ∧ a2 = 0) ∧
    ¬ HasIsotropic ([1, 1, -3] : List Int) ∧
    (∀ a1 d1 a2 d2 a3 d3 : Int, d1 ≠ 0 → d2 ≠ 0 → d3 ≠ 0 →
      (a1 * d2 * d3) * (a1 * d2 * d3) + (a2 * d1 * d3) * (a2 * d1 * d3) -
      3 * ((a3 * d1 * d2) * (a3 * d1 * d2)) = 0 → a1 = 0 ∧ a2 = 0 ∧ a3 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨a, b, PUnit.unit⟩, hne, hq⟩
    change 1 * (a * a) + (-2 * (b * b) + 0) = 0 at hq
    have hq' : a * a - 2 * (b * b) = 0 := by omega
    have ⟨ha, hb⟩ := int_sq_sub_two_sq_eq_zero hq'
    exact hne (Prod.ext ha (Prod.ext hb rfl))
  · intro a1 d1 a2 d2 hd1 hd2 hrat
    have ⟨hx, hy⟩ := int_sq_sub_two_sq_eq_zero hrat
    have ha1 : a1 = 0 := by
      cases Int.mul_eq_zero.mp hx with
      | inl h => exact h
      | inr h => exact False.elim (hd2 h)
    have ha2 : a2 = 0 := by
      cases Int.mul_eq_zero.mp hy with
      | inl h => exact h
      | inr h => exact False.elim (hd1 h)
    exact ⟨ha1, ha2⟩
  · intro ⟨⟨a, b, c, PUnit.unit⟩, hne, hq⟩
    change 1 * (a * a) + (1 * (b * b) + (-3 * (c * c) + 0)) = 0 at hq
    have hq' : a * a + b * b - 3 * (c * c) = 0 := by omega
    have ⟨ha, hb, hc⟩ := int_two_sq_sub_three_sq_eq_zero hq'
    exact hne (Prod.ext ha (Prod.ext hb (Prod.ext hc rfl)))
  · intro a1 d1 a2 d2 a3 d3 hd1 hd2 hd3 hrat
    have ⟨hx, hy, hz⟩ := int_two_sq_sub_three_sq_eq_zero hrat
    have cancel2 {u v w : Int} (hv : v ≠ 0) (hw : w ≠ 0) (h : u * v * w = 0) : u = 0 := by
      cases Int.mul_eq_zero.mp h with
      | inr hw0 => exact False.elim (hw hw0)
      | inl huv =>
        cases Int.mul_eq_zero.mp huv with
        | inl hu0 => exact hu0
        | inr hv0 => exact False.elim (hv hv0)
    exact ⟨cancel2 hd2 hd3 hx, cancel2 hd1 hd3 hy, cancel2 hd1 hd2 hz⟩

/-! ## Part 4: Concrete Non-Vacuity Instantiations on `Int` -/

theorem nonvacuous_int_grade1_iff (p q : Nat) :
    (∃ v : Vec Int (sigList Int p q), embedVec v ≠ 0 ∧ IsNilpotent (embedVec v)) ↔
    (p ≥ 1 ∧ q ≥ 1) :=
  grade1_nilpotent_exists_iff_indefinite (R := Int) p q

theorem nonvacuous_int_cl_classification (p q : Nat) :
    (∃ z : Cl Int (sigList Int p q), z ≠ 0 ∧ IsNilpotent z) ↔ ¬ IsReducedSignature p q :=
  cl_has_nilpotent_iff (R := Int) p q

theorem nonvacuous_int_pos_def_nilpotents :
    (¬ HasIsotropic (sigList Int 2 0) ∧
     ∃ x : Cl Int (sigList Int 2 0), x ≠ 0 ∧ IsSqZero x) ∧
    (¬ HasIsotropic (sigList Int 0 4) ∧
     ∃ y : Cl Int (sigList Int 0 4), y ≠ 0 ∧ IsSqZero y) := by
  have ⟨h20_iso, x, hx_ne, hx_sq, _⟩ := refutation_pos_def_plus_conv (R := Int)
  have ⟨_, h04_iso, y, hy_ne, hy_sq, _⟩ := refutation_pos_def_minus_conv (R := Int)
  exact ⟨⟨h20_iso, x, hx_ne, hx_sq⟩, ⟨h04_iso, y, hy_ne, hy_sq⟩⟩

end Conjecture00000007624
