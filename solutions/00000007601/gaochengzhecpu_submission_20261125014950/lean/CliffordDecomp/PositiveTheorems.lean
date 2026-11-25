/-
  CliffordDecomp/PositiveTheorems.lean
  Positive theorems and exact grade-parity characterization:
  1. For grade-1 vectors `u, v ∈ K^n` in ANY Clifford algebra `Cl(n, q)` over a
     commutative ring `K` with invertible `2`:
     - `vec u * vec v = symPart + antisymPart`
     - `symPart(vec u, vec v) = B_Q(u, v) · 1` (agrees with left, right, Hestenes contractions)
     - `antisymPart(vec u, vec v) = vec u ∧ vec v` (exterior outer product, pure grade 2)
     - Metric orthogonality `⟨symPart, antisymPart⟩_{Q~} = 0`
     - Lagrange–Pythagoras identity `⟨uv, uv⟩_{Q~} = ⟨symPart, symPart⟩_{Q~} + ⟨antisymPart, antisymPart⟩_{Q~} = Q(u) Q(v)`
     - Metric orthogonality criterion `B_Q(u, v) = 0 ↔ symPart(vec u, vec v) = 0 ↔ uv = -vu`
  2. Exact homogeneous grade-parity sign law:
     For `X ∈ Cl^r(n, q)` and `Y ∈ Cl^s(n, q)`, and `m + 2j = r + s`,
     `⟨Y X⟩_m = (-1)^{r s + j} ⟨X Y⟩_m`.
  3. Concrete non-vacuity witness in `Cl_{2,0}(ℚ)`.
-/
import CliffordDecomp.GradingAndProducts

namespace CliffordDecomp
namespace ClSpace

section GradeOnePositive
variable {K : Type u} [CommRing2 K]

/-- **Grade-1 Symmetric Part Theorem:** For all vectors `u, v ∈ K^n`, the symmetric
    anticommutator part `(1/2){u, v}` equals the metric inner product `B_Q(u, v) · 1`. -/
theorem vec_symPart_eq_polar {n : Nat} (q u v : Fin n → K) :
    symPart q (vec u) (vec v) = scalar (polarForm q u v) := by
  unfold symPart anticomm
  rw [vec_anticomm_eq_polar, scalar_smul, smul_smul, CommRing2.half_mul_two, one_smul]

theorem vec_symPart_hasGrade_zero {n : Nat} (q u v : Fin n → K) :
    HasGrade 0 (symPart q (vec u) (vec v)) := by
  unfold HasGrade
  rw [vec_symPart_eq_polar, gradeProj_scalar_zero]

/-- On grade-1 vectors (with `1 ≤ n`), `symPart` agrees with all three standard inner
    contractions (`leftContract`, `rightContract`, and `hestenesInner`). -/
theorem vec_symPart_eq_contractions {n : Nat} (hn : 1 ≤ n) (q u v : Fin n → K) :
    leftContract q (vec u) (vec v) = symPart q (vec u) (vec v) ∧
    rightContract q (vec u) (vec v) = symPart q (vec u) (vec v) ∧
    hestenesInner q (vec u) (vec v) = symPart q (vec u) (vec v) := by
  have hu : HasGrade 1 (vec u) := gradeProj_vec_one u
  have hv : HasGrade 1 (vec v) := gradeProj_vec_one v
  have hg0 : gradeProj 0 (mul q (vec u) (vec v)) = scalar (polarForm q u v) := by
    rw [gradeProj_zero_eq_scalar]
    have hrev : mul q (vec u) (vec v) = mul q (rev (vec u)) (vec v) := by rw [rev_vec]
    rw [hrev]
    exact congrArg scalar (metricForm_vec q u v)
  have h1 : leftContract q (vec u) (vec v) = symPart q (vec u) (vec v) := by
    rw [leftContract_of_hasGrade q hn hn hu hv, if_pos (Nat.le_refl 1), Nat.sub_self,
        hg0, vec_symPart_eq_polar]
  have h2 : rightContract q (vec u) (vec v) = symPart q (vec u) (vec v) := by
    rw [rightContract_of_hasGrade q hn hn hu hv, if_pos (Nat.le_refl 1), Nat.sub_self,
        hg0, vec_symPart_eq_polar]
  have h3 : hestenesInner q (vec u) (vec v) = symPart q (vec u) (vec v) := by
    rw [hestenesInner_of_hasGrade q (Nat.le_refl 1) hn (Nat.le_refl 1) hn hu hv,
        if_pos (Nat.le_refl 1), Nat.sub_self, hg0, vec_symPart_eq_polar]
  exact ⟨h1, h2, h3⟩

/-- **Direct Hestenes Vector Product Formula:** `u v = B_Q(u, v) · 1 + u ∧ v`. -/
theorem vec_mul_eq_polar_add_wedge {n : Nat} (q u v : Fin n → K) :
    mul q (vec u) (vec v) = add (scalar (polarForm q u v)) (wedge (vec u) (vec v)) := by
  induction n with
  | zero =>
    dsimp [vec, mul, polarForm, scalar, wedge, zeroForm, add]
    rw [CommRing2.zero_mul, CommRing2.add_zero]
  | succ n ih =>
    dsimp [vec, mul, polarForm, scalar, wedge, zeroForm, finHead, finTail]
    have hzf : finTail (zeroForm : Fin (n + 1) → K) = zeroForm := rfl
    apply Prod.ext
    · dsimp [add]
      rw [ih, invol_smul, invol_one, smul_mul, mul_smul, one_mul,
          smul_smul, smul_smul, zero_smul, add_zero, CommRing2.mul_assoc (q 0) (u 0) (v 0)]
      have hsc : smul (q 0 * (u 0 * v 0)) (one : ClSpace K n) =
                 scalar (q 0 * (u 0 * v 0)) := by
        rw [← scalar_one, ← scalar_smul, CommRing2.mul_one]
      rw [hsc, scalar_add, hzf]
      unfold wedge
      simp only [add_assoc, add_left_comm, add_comm]
    · dsimp [add]
      rw [smul_mul, one_mul, smul_mul, one_mul,
          mul_smul, mul_one, mul_smul, mul_one, zero_add]

/-- **Grade-1 Antisymmetric Part Theorem:** For all vectors `u, v ∈ K^n`, the antisymmetric
    commutator part `(1/2)[u, v]` equals the exterior wedge product `u ∧ v` (grade 2). -/
theorem vec_antisymPart_eq_wedge {n : Nat} (q u v : Fin n → K) :
    antisymPart q (vec u) (vec v) = wedge (vec u) (vec v) := by
  apply add_left_cancel (x := scalar (polarForm q u v))
  rw [← vec_symPart_eq_polar q u v, ← mul_eq_symPart_add_antisymPart q (vec u) (vec v),
      vec_mul_eq_polar_add_wedge q u v, vec_symPart_eq_polar q u v]

theorem vec_antisymPart_hasGrade_two {n : Nat} (q u v : Fin n → K) :
    HasGrade 2 (antisymPart q (vec u) (vec v)) := by
  rw [vec_antisymPart_eq_wedge]
  have h := (homogeneous_mul_top_grade q (gradeProj_vec_one u) (gradeProj_vec_one v)).2.2
  exact h

/-- **Metric Orthogonality of the Grade-1 Decomposition:** Under the canonical metric
    bilinear form `⟨X, Y⟩_{Q~} = ⟨X~ Y⟩_0`, the symmetric and antisymmetric parts of `u v`
    are mutually orthogonal. -/
theorem vec_decomp_metric_orthog {n : Nat} (q u v : Fin n → K) :
    metricForm q (symPart q (vec u) (vec v)) (antisymPart q (vec u) (vec v)) = 0 := by
  have hs := vec_symPart_hasGrade_zero q u v
  have ha := vec_antisymPart_hasGrade_two q u v
  rw [← hs, ← ha]
  exact metricForm_grade_orthog q (by decide : 0 ≠ 2) _ _

/-- **Lagrange–Pythagoras Norm Identity:**
    `⟨u v, u v⟩_{Q~} = ⟨symPart, symPart⟩_{Q~} + ⟨antisymPart, antisymPart⟩_{Q~} = Q(u) Q(v)`. -/
theorem vec_lagrange_pythagoras {n : Nat} (q u v : Fin n → K) :
    metricForm q (mul q (vec u) (vec v)) (mul q (vec u) (vec v)) =
      metricForm q (symPart q (vec u) (vec v)) (symPart q (vec u) (vec v)) +
      metricForm q (antisymPart q (vec u) (vec v)) (antisymPart q (vec u) (vec v)) ∧
    metricForm q (mul q (vec u) (vec v)) (mul q (vec u) (vec v)) =
      quadForm q u * quadForm q v := by
  let S := symPart q (vec u) (vec v)
  let A := antisymPart q (vec u) (vec v)
  have horth : metricForm q S A = 0 := vec_decomp_metric_orthog q u v
  have horth2 : metricForm q A S = 0 := by rw [metricForm_symm, horth]
  constructor
  · conv => lhs; rw [mul_eq_symPart_add_antisymPart q (vec u) (vec v)]
    change metricForm q (add S A) (add S A) = metricForm q S S + metricForm q A A
    rw [metricForm_add_left, metricForm_add_right, metricForm_add_right,
        horth, horth2, CommRing2.add_zero, CommRing2.zero_add]
  · unfold metricForm
    rw [rev_mul, rev_vec, rev_vec, mul_assoc, ← mul_assoc q (vec u) (vec u) (vec v),
        vec_sq_eq_quad, scalar_mul, mul_smul, vec_sq_eq_quad,
        ← scalar_smul, scalarPart_scalar]

/-- **Metric Orthogonality Criterion for Vectors:** Two vectors `u, v ∈ K^n` are orthogonal
    with respect to `B_Q` iff `symPart(u, v) = 0`, iff `u v = - v u`. -/
theorem vec_orthog_iff_symPart_zero {n : Nat} (q u v : Fin n → K) :
    polarForm q u v = 0 ↔ symPart q (vec u) (vec v) = zero := by
  rw [vec_symPart_eq_polar, ← scalar_zero (n := n)]
  exact ⟨fun h => congrArg scalar h, fun h => scalar_injective h⟩

theorem vec_orthog_iff_anticomm {n : Nat} (q u v : Fin n → K) :
    polarForm q u v = 0 ↔ mul q (vec u) (vec v) = neg (mul q (vec v) (vec u)) := by
  rw [vec_orthog_iff_symPart_zero]
  constructor
  · intro h
    have h2 : smul ((1 : K) + 1) (symPart q (vec u) (vec v)) = smul ((1 : K) + 1) zero :=
      congrArg (smul ((1 : K) + 1)) h
    unfold symPart anticomm at h2
    rw [smul_smul, CommRing2.two_mul_half, one_smul, smul_zero] at h2
    apply add_left_cancel (x := mul q (vec v) (vec u))
    rw [add_comm, h2, add_neg_cancel]
  · intro h
    unfold symPart anticomm
    rw [h, neg_add_cancel, smul_zero]

/-! ### Exact Homogeneous Grade-Parity Law -/

/-- Reversion-derived commutation law at output grade `m` for `X ∈ Cl^r`, `Y ∈ Cl^s`:
    `⟨Y X⟩_m = (-1)^{triNum r + triNum s + triNum m} ⟨X Y⟩_m`. -/
theorem gradeProj_mul_swap {n : Nat} (q : Fin n → K)
    {r s : Nat} (m : Nat) {x y : ClSpace K n}
    (hx : HasGrade r x) (hy : HasGrade s y) :
    gradeProj m (mul q y x) =
      smul (CommRing2.signPow K (triNum r + triNum s + triNum m))
           (gradeProj m (mul q x y)) := by
  have h1 : rev (gradeProj m (mul q y x)) =
            smul (CommRing2.signPow K (triNum m)) (gradeProj m (mul q y x)) :=
    rev_gradeProj m (mul q y x)
  have h2 : rev (gradeProj m (mul q y x)) =
            smul (CommRing2.signPow K (triNum r + triNum s)) (gradeProj m (mul q x y)) := by
    rw [← gradeProj_rev, rev_mul, rev_of_hasGrade hx, rev_of_hasGrade hy,
        smul_mul, mul_smul, smul_smul, gradeProj_smul, ← CommRing2.signPow_add]
  have heq : smul (CommRing2.signPow K (triNum m)) (gradeProj m (mul q y x)) =
             smul (CommRing2.signPow K (triNum r + triNum s)) (gradeProj m (mul q x y)) := by
    rw [← h1, h2]
  have hmul := congrArg (smul (CommRing2.signPow K (triNum m))) heq
  rw [smul_smul, CommRing2.signPow_sq, one_smul, smul_smul,
      CommRing2.mul_comm (CommRing2.signPow K (triNum m)),
      ← CommRing2.signPow_add] at hmul
  exact hmul

omit [CommRing2 K] in
private theorem two_triNum_add_self (k : Nat) : 2 * triNum k + k = k * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [triNum]
    have h : 2 * (triNum k + k) + (k + 1) = (2 * triNum k + k) + (2 * k + 1) := by omega
    rw [h, ih]
    have hsq : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by
      rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]
      omega
    exact hsq.symm

/-- Combinatorial parity identity: when `m + 2j = r + s`,
    `(-1)^{triNum r + triNum s + triNum m} = (-1)^{r s + j}`. -/
theorem signPow_triNum_eq_rs_add_j {r s m j : Nat} (hm : m + 2 * j = r + s) :
    CommRing2.signPow K (triNum r + triNum s + triNum m) =
    CommRing2.signPow K (r * s + j) := by
  have hsq : (m + 2 * j) * (m + 2 * j) = (r + s) * (r + s) := congrArg (fun t => t * t) hm
  have lhs_exp : (m + 2 * j) * (m + 2 * j) = m * m + 4 * (m * j) + 4 * (j * j) := by
    rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]
    have h1 : m * (2 * j) = 2 * (m * j) := by
      rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
    have h2 : (2 * j) * m = 2 * (m * j) := by
      rw [Nat.mul_comm (2 * j) m, h1]
    have h3 : (2 * j) * (2 * j) = 4 * (j * j) := by
      calc
        (2 * j) * (2 * j) = 2 * (j * (2 * j)) := Nat.mul_assoc 2 j (2 * j)
        _ = 2 * (2 * (j * j)) := by rw [← Nat.mul_assoc j 2 j, Nat.mul_comm j 2, Nat.mul_assoc]
        _ = 4 * (j * j) := by rw [← Nat.mul_assoc]
    rw [h1, h2, h3]
    omega
  have rhs_exp : (r + s) * (r + s) = r * r + 2 * (r * s) + s * s := by
    rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm s r]
    omega
  rw [lhs_exp, rhs_exp, ← two_triNum_add_self m, ← two_triNum_add_self r,
      ← two_triNum_add_self s] at hsq
  have hlin : triNum r + triNum s + triNum m + 2 * (m * j + j * j) =
              2 * (triNum r + triNum s) + (r * s + j) := by
    omega
  have hs1 : CommRing2.signPow K (triNum r + triNum s + triNum m + 2 * (m * j + j * j)) =
             CommRing2.signPow K (triNum r + triNum s + triNum m) := by
    rw [CommRing2.signPow_add, CommRing2.signPow_even, CommRing2.mul_one]
  have hs2 : CommRing2.signPow K (2 * (triNum r + triNum s) + (r * s + j)) =
             CommRing2.signPow K (r * s + j) := by
    rw [CommRing2.signPow_add, CommRing2.signPow_even, CommRing2.one_mul]
  rw [← hs1, hlin, hs2]

/-- **Exact Homogeneous Grade-Parity Sign Theorem:**
    For `X ∈ Cl^r(n, q)`, `Y ∈ Cl^s(n, q)`, and `m + 2j = r + s`,
    `⟨Y X⟩_m = (-1)^{r s + j} ⟨X Y⟩_m`. -/
theorem gradeProj_mul_parity {n : Nat} (q : Fin n → K)
    {r s m j : Nat} (hm : m + 2 * j = r + s) {x y : ClSpace K n}
    (hx : HasGrade r x) (hy : HasGrade s y) :
    gradeProj m (mul q y x) =
      smul (CommRing2.signPow K (r * s + j)) (gradeProj m (mul q x y)) := by
  rw [gradeProj_mul_swap q m hx hy, signPow_triNum_eq_rs_add_j hm]

end GradeOnePositive

/-! ### Concrete Non-Vacuity Theorem over `ℚ` in `Cl_{2,0}(ℚ)` -/

/-- Euclidean signature `(1, 1)` on `ℚ^2`. -/
def qEuclid2 : Fin 2 → RatQ := fun _ => 1

/-- Non-collinear, non-orthogonal vectors `u = (1, 2)` and `v = (3, -1)` in `ℚ^2`. -/
def uNonVac : Fin 2 → RatQ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2

def vNonVac : Fin 2 → RatQ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => -(1 : RatQ)

/-- **Non-Vacuity Witness:** For `u = e_1 + 2 e_2` and `v = 3 e_1 - e_2` in `Cl_{2,0}(ℚ)`,
    both `symPart` (`= 1 ≠ 0`) and `antisymPart` (`= -7 e_1 e_2 ≠ 0`) are strictly nonzero,
    inner/outer identifications hold, and their Euclidean metric inner product vanishes. -/
theorem grade1_rational_nonvacuity :
    symPart qEuclid2 (vec uNonVac) (vec vNonVac) ≠ zero ∧
    antisymPart qEuclid2 (vec uNonVac) (vec vNonVac) ≠ zero ∧
    symPart qEuclid2 (vec uNonVac) (vec vNonVac) =
      hestenesInner qEuclid2 (vec uNonVac) (vec vNonVac) ∧
    antisymPart qEuclid2 (vec uNonVac) (vec vNonVac) =
      wedge (vec uNonVac) (vec vNonVac) ∧
    metricForm qEuclid2
      (symPart qEuclid2 (vec uNonVac) (vec vNonVac))
      (antisymPart qEuclid2 (vec uNonVac) (vec vNonVac)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vec_symPart_eq_polar]
    intro h
    have hp : polarForm qEuclid2 uNonVac vNonVac = 0 := scalar_injective h
    exact RatQ.ne_of_sub_isZero_false rfl hp
  · intro h
    have h2 : smul ((1 : RatQ) + 1) (antisymPart qEuclid2 (vec uNonVac) (vec vNonVac)) = zero := by
      rw [h, smul_zero]
    unfold antisymPart comm at h2
    rw [smul_smul, CommRing2.two_mul_half, one_smul] at h2
    have he12 : ((sub (mul qEuclid2 (vec uNonVac) (vec vNonVac))
                      (mul qEuclid2 (vec vNonVac) (vec uNonVac))).2.2 : RatQ) = 0 := by
      rw [h2]; rfl
    exact RatQ.ne_of_sub_isZero_false rfl he12
  · exact (vec_symPart_eq_contractions (by decide) qEuclid2 uNonVac vNonVac).2.2.symm
  · exact vec_antisymPart_eq_wedge qEuclid2 uNonVac vNonVac
  · exact vec_decomp_metric_orthog qEuclid2 uNonVac vNonVac

end ClSpace
end CliffordDecomp
