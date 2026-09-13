import Mathlib

/-!
# Conjecture 00000000088 is false

Conjecture 00000000088 asserts that every prime `p ≥ 2` is the stretch factor of
a pseudo-Anosov element of some mapping class group. No prime is: **no stretch
factor is rational at all.**

The geometric half of the argument is in the accompanying paper
(`main.tex`, §4): a pseudo-Anosov homeomorphism `φ` of a finite-type surface
has, after passing to the double cover that orients its invariant foliations, a
transverse measure class in `H¹` that is an eigenvector of the induced action
with eigenvalue `±λ^{±1}`; that action is an automorphism of a finitely
generated free abelian group, i.e. an integer matrix of determinant `±1`. So
every stretch factor satisfies the predicate `IsUnimodularEigenvalue` below.
Measured foliations and Teichmüller theory are not available in Mathlib, so that
step is not formalized; it is classical (Thurston, Fried).

This file formalizes the arithmetic half, which is where the conjecture dies:

* `rat_eq_one_or_neg_one` — a *rational* number satisfying
  `IsUnimodularEigenvalue` is `1` or `-1`;
* `irrational_of_isUnimodularEigenvalue` — hence every such number `> 1` is
  irrational;
* `prime_not_isUnimodularEigenvalue` — hence no prime `p` satisfies it, which
  refutes the conjecture.

The mechanism: the characteristic polynomial of an integer matrix `A` is monic
with constant coefficient `±det A`, so if `det A = ±1` any integer root divides
`1`. This is the statement "stretch factors are algebraic units", specialized to
rational stretch factors.

The last section checks, formally, the two facts recorded in the research notes
about the candidate matrix `!![2, 1; p - 2, p - 1]`: its characteristic
polynomial is `(X - p)(X - 1)`, and its determinant is `p`. The second is
exactly why the candidate cannot be a homological action — the special case,
for that matrix, of the general obstruction proved here.
-/

namespace Conjecture00000000088

open Matrix Polynomial

variable {m : ℕ}

/-! ## The homological shadow of a stretch factor -/

/-- `IsUnimodularEigenvalue lam`: the real number `lam` is an eigenvalue of an
automorphism of a finitely generated free abelian group — an integer matrix `A`
with `det A` a unit, together with a nonzero real eigenvector for `lam`.

This is what the geometry supplies for a pseudo-Anosov stretch factor: the
action on `H¹` of the surface (or of the double cover orienting the invariant
foliations) preserves the integral lattice, hence is unimodular, and the
transverse measure class is an eigenvector with eigenvalue `±λ^{±1}`. Both
negation and inversion preserve the conclusion below, so no generality is lost
by writing the eigenvalue as `lam`. -/
def IsUnimodularEigenvalue (lam : ℝ) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (v : Fin m → ℝ),
    IsUnit A.det ∧ v ≠ 0 ∧ A.map (fun a : ℤ => (a : ℝ)) *ᵥ v = lam • v

/-! ## The arithmetic core -/

/-- An integer root of an integer polynomial divides its constant coefficient:
`f a = 0` and `a ∣ f a - f 0` give `a ∣ f 0`. -/
theorem int_root_dvd_coeff_zero {f : ℤ[X]} {a : ℤ} (h : f.eval a = 0) :
    a ∣ f.coeff 0 := by
  have hd : a - 0 ∣ f.eval a - f.eval 0 := Polynomial.sub_dvd_eval_sub a 0 f
  rw [sub_zero, h, zero_sub, ← Polynomial.coeff_zero_eq_eval_zero] at hd
  exact dvd_neg.mp hd

/-- The constant coefficient of the characteristic polynomial of an integer
matrix is `± det`, so for a unimodular matrix it is a unit. -/
theorem isUnit_charpoly_coeff_zero {A : Matrix (Fin m) (Fin m) ℤ} (hA : IsUnit A.det) :
    IsUnit (A.charpoly.coeff 0) := by
  rw [A.det_eq_sign_charpoly_coeff] at hA
  exact isUnit_of_mul_isUnit_right hA

/-- **An integer eigenvalue of a unimodular integer matrix is `±1`.** -/
theorem eq_one_or_neg_one_of_charpoly_eval {A : Matrix (Fin m) (Fin m) ℤ}
    (hA : IsUnit A.det) {n : ℤ} (hn : A.charpoly.eval n = 0) : n = 1 ∨ n = -1 :=
  Int.isUnit_iff.mp
    (isUnit_of_dvd_unit (int_root_dvd_coeff_zero hn) (isUnit_charpoly_coeff_zero hA))

/-! ## From a real eigenvector down to `ℤ` -/

/-- An eigenvector for `lam` makes the characteristic polynomial, read over `ℝ`,
vanish at `lam`. -/
theorem exists_charpoly_map_eval_eq_zero {lam : ℝ} (h : IsUnimodularEigenvalue lam) :
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ), IsUnit A.det ∧
      (A.charpoly.map (Int.castRingHom ℝ)).eval lam = 0 := by
  obtain ⟨m, A, v, hA, hv, hmul⟩ := h
  refine ⟨m, A, hA, ?_⟩
  set B : Matrix (Fin m) (Fin m) ℝ := A.map (Int.castRingHom ℝ) with hB
  have hmul' : B *ᵥ v = lam • v := hmul
  have hker : (Matrix.scalar (Fin m) lam - B) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hmul']
    funext i
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin m) lam - B).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hker⟩
  calc (A.charpoly.map (Int.castRingHom ℝ)).eval lam
      = B.charpoly.eval lam := by rw [hB, Matrix.charpoly_map]
    _ = (Matrix.scalar (Fin m) lam - B).det := Matrix.eval_charpoly _ _
    _ = 0 := hdet

/-- **A rational number satisfying `IsUnimodularEigenvalue` is `1` or `-1`.**

`ℤ` is integrally closed in `ℚ`, so a rational root of the (monic) characteristic
polynomial is an integer, and an integer root divides the unit constant
coefficient. -/
theorem rat_eq_one_or_neg_one {q : ℚ} (h : IsUnimodularEigenvalue (q : ℝ)) :
    q = 1 ∨ q = -1 := by
  obtain ⟨m, A, hA, hroot⟩ := exists_charpoly_map_eval_eq_zero h
  -- Read the characteristic polynomial over `ℚ` instead of over `ℝ`.
  set g : ℚ[X] := A.charpoly.map (Int.castRingHom ℚ) with hg
  have hmapeq : A.charpoly.map (Int.castRingHom ℝ) = g.map (Rat.castHom ℝ) := by
    rw [hg, Polynomial.map_map]
    congr 1
  have hgq : g.eval q = 0 := by
    rw [hmapeq] at hroot
    have h1 : (Rat.castHom ℝ) (g.eval q) = 0 := by
      rw [← Polynomial.eval₂_hom (Rat.castHom ℝ) q, ← Polynomial.eval_map]
      exact hroot
    simpa using h1
  -- A rational root of a monic integer polynomial is an integer.
  have hint : IsIntegral ℤ q := by
    refine ⟨A.charpoly, A.charpoly_monic, ?_⟩
    rw [algebraMap_int_eq, ← Polynomial.eval_map]
    exact hgq
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [algebraMap_int_eq] at hn
  have hnq : (n : ℚ) = q := hn
  have hz : A.charpoly.eval n = 0 := by
    have h1 : (Int.castRingHom ℚ) (A.charpoly.eval n) = 0 := by
      rw [← Polynomial.eval₂_hom (Int.castRingHom ℚ) n, ← Polynomial.eval_map, ← hg, hn]
      exact hgq
    simpa using h1
  rcases eq_one_or_neg_one_of_charpoly_eval hA hz with rfl | rfl
  · left; exact_mod_cast hnq.symm
  · right; exact_mod_cast hnq.symm

/-- Every number `> 1` satisfying `IsUnimodularEigenvalue` is irrational. Applied
to a pseudo-Anosov stretch factor (which is `> 1` by definition), this says that
**no stretch factor is rational**. -/
theorem irrational_of_isUnimodularEigenvalue {lam : ℝ} (h : IsUnimodularEigenvalue lam)
    (h1 : 1 < lam) : Irrational lam := by
  rintro ⟨q, rfl⟩
  rcases rat_eq_one_or_neg_one h with rfl | rfl <;> norm_num at h1

/-- No integer `≥ 2` satisfies `IsUnimodularEigenvalue`. -/
theorem natCast_not_isUnimodularEigenvalue {p : ℕ} (hp : 2 ≤ p) :
    ¬ IsUnimodularEigenvalue (p : ℝ) := by
  intro h
  have hcast : ((p : ℚ) : ℝ) = (p : ℝ) := by push_cast; ring
  rcases rat_eq_one_or_neg_one (q := (p : ℚ)) (by rwa [hcast]) with h1 | h1
  · have : p = 1 := by exact_mod_cast h1
    omega
  · have hnn : (0 : ℚ) ≤ (p : ℚ) := by positivity
    rw [h1] at hnn
    norm_num at hnn

/-- **Main theorem.** No prime satisfies `IsUnimodularEigenvalue`.

With §4 of the paper — every pseudo-Anosov stretch factor is an eigenvalue of a
unimodular integer matrix — this refutes conjecture 00000000088, and refutes it
for *every* prime `p ≥ 2`, not merely for one. -/
theorem prime_not_isUnimodularEigenvalue {p : ℕ} (hp : p.Prime) :
    ¬ IsUnimodularEigenvalue (p : ℝ) :=
  natCast_not_isUnimodularEigenvalue hp.two_le

/-! ## The predicate is not vacuous -/

/-- The golden ratio `(1 + √5)/2` — the stretch factor of the Anosov map of the
torus with matrix `!![1, 1; 1, 0]`, and of a pseudo-Anosov map of the
once-punctured torus — does satisfy `IsUnimodularEigenvalue`. So the theorems
above are not vacuous: what they exclude is rationality, nothing more. -/
theorem goldenRatio_isUnimodularEigenvalue :
    IsUnimodularEigenvalue Real.goldenRatio := by
  refine ⟨2, !![1, 1; 1, 0], ![Real.goldenRatio, 1], ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of, Int.isUnit_iff]
    norm_num
  · intro hv
    have h1 := congrFun hv 1
    norm_num at h1
  · have hsq : Real.goldenRatio * Real.goldenRatio = Real.goldenRatio + 1 := by
      rw [← pow_two]; exact Real.goldenRatio_sq
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsq]

/-! ## The Perron–Frobenius candidate of the research notes

The notes in `research/00000000088/` propose `!![2, 1; p - 2, p - 1]` as a
transition matrix with Perron root `p`. Both computations recorded there are
confirmed below. The determinant is `p`, so by `eq_one_or_neg_one_of_charpoly_eval`
this matrix is not the action of any homeomorphism on homology once `p ≥ 2` —
the special case, for this matrix, of the general obstruction. -/

/-- The candidate matrix of the research notes. -/
def cand (p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; p - 2, p - 1]

theorem cand_det (p : ℤ) : (cand p).det = p := by
  simp only [cand, Matrix.det_fin_two_of]
  ring

/-- Its characteristic polynomial is `(X - p)(X - 1)`: the Perron root is `p`, as
the research notes claim. -/
theorem cand_charpoly (p : ℤ) : (cand p).charpoly = (X - C p) * (X - 1) := by
  have ht : (cand p).trace = p + 1 := by
    simp only [cand, Matrix.trace_fin_two_of]
    ring
  rw [Matrix.charpoly_fin_two, ht, cand_det, Polynomial.C_add, Polynomial.C_1]
  ring

/-- But `det = p`, so for `p ≥ 2` the candidate is not unimodular: it cannot be
the action of a homeomorphism on the first homology of a surface. -/
theorem cand_not_unimodular {p : ℤ} (hp : 2 ≤ p) : ¬ IsUnit (cand p).det := by
  rw [cand_det, Int.isUnit_iff]
  omega

/-! ## The repaired candidate

Lowering the top-left entry of `cand p` by one makes it unimodular, at the cost of
moving `p` from the spectrum to the trace: the Perron root becomes
`(p + √(p² - 4))/2`, which does satisfy `IsUnimodularEigenvalue`. §7 of the paper
identifies the corresponding mapping class on the once-punctured torus; that
identification is geometry and is not formalized here. -/

/-- The research notes' candidate with its top-left entry lowered by one. -/
def repaired (p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; p - 2, p - 1]

theorem repaired_det (p : ℤ) : (repaired p).det = 1 := by
  simp only [repaired, Matrix.det_fin_two_of]
  ring

/-- Its characteristic polynomial is `X² - pX + 1`: the trace is `p`, the
determinant is `1`. -/
theorem repaired_charpoly (p : ℤ) : (repaired p).charpoly = X ^ 2 - C p * X + 1 := by
  have ht : (repaired p).trace = p := by
    simp only [repaired, Matrix.trace_fin_two_of]
    ring
  rw [Matrix.charpoly_fin_two, ht, repaired_det, Polynomial.C_1]

/-- The larger root of `X² - pX + 1` satisfies `IsUnimodularEigenvalue`: for it the
arithmetic obstruction of `prime_not_isUnimodularEigenvalue` is absent. -/
theorem repaired_isUnimodularEigenvalue {p : ℤ} (hp : 2 ≤ p) :
    IsUnimodularEigenvalue (((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 - 4)) / 2) := by
  have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set lam : ℝ := ((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 - 4)) / 2 with hlam
  have hD : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 4 := by nlinarith
  have hsqrt : Real.sqrt ((p : ℝ) ^ 2 - 4) ^ 2 = (p : ℝ) ^ 2 - 4 := Real.sq_sqrt hD
  have hkey : lam * lam = (p : ℝ) * lam - 1 := by
    rw [hlam]
    nlinarith [hsqrt]
  refine ⟨2, repaired p, ![1, lam - 1], ?_, ?_, ?_⟩
  · rw [repaired_det]
    exact isUnit_one
  · intro hv
    have h0 := congrFun hv 0
    norm_num at h0
  · funext i
    fin_cases i
    · simp [repaired, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [repaired, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -hkey

end Conjecture00000000088
