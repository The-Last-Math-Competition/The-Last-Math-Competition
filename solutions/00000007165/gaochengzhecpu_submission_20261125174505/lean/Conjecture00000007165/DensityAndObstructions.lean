/-
  Conjecture 00000007165 — Domain 5 (Density-Matrix Extremal Faces) & Structural Obstructions
  Core Lean 4.19.0 (zero external dependencies).

  Establishes:
  1. Domain 5 (Density-Matrix State Spaces `𝒟_n(ℝ)` and `𝒟_n(ℂ)`):
     - Exact PSD trace-1 extremal face predicates `InRealExtremalFace` and `InComplexExtremalFace`.
     - Exact geometric tangent equivalence at the maximally mixed extremal state `ρ₀ = (1/m) P_m`:
       bilateral feasible perturbations `ρ₀ ± (1/d) H ∈ F_max(A)` coincide with `TracelessSymBlock n m`
       (over `ℝ`) and `TracelessHermBlock n m` (over `ℂ`).
     - Exact dimensions proved for ALL `1 ≤ m ≤ n` via border-splitting direct-sum induction:
       * `dim_ℝ F_max^ℂ(A) = m² - 1 ≠ m` for EVERY `m ≥ 1` (`m² - m - 1 ≠ 0` over `ℤ`).
       * `dim_ℝ F_max^ℝ(A) = m(m+1)/2 - 1 ≠ m` for `m = 1` and EVERY `m ≥ 3`.
  2. Structural Obstruction 6A (Non-Normal Matrices):
     `A = [[0, 2], [0, 0]]` has `χ_A(μ) = μ²` (unique eigenvalue `0` of algebraic multiplicity `2`,
     geometric multiplicity `1`), yet `max R_A = 1 ≠ 0` is attained on a unique projective ray
     `[(1, 1)ᵀ]` of dimension `0 ∉ {1, 2}`.
  3. Structural Obstruction 6B (Joint Rayleigh Quotient / 1D Extremal Face):
     `A₁ = diag(1,1,0,0)`, `A₂ = diag(0,0,1,0)` have a genuine 1D extremal face `u + v = 1`
     whose supporting operator `A₁ + A₂ = diag(1,1,1,0)` has multiplicity `3`, while contact
     dimensions across `S³`, `ℝℙ³`, `S⁷`, `ℂℙ³`, `𝒟₄(ℂ)`, `𝒟₄(ℝ)` are `2, 2, 5, 2/4, 8, 5 ≠ 3`.
  4. Structural Obstruction 6C (Interior Eigenvalue Singularity):
     For `A = diag(1, 0, -1)` at interior eigenvalue `λ₂ = 0` (`m = 1`), the Zariski tangent
     dimension on `S² ∩ R_A⁻¹(0)` jumps from `1` at `(2/3, 1/3, 2/3)` to `2` at `(0, 1, 0)`,
     proving the level set is singular (not a smooth manifold).
-/

import Conjecture00000007165.ContactDomains

namespace Conjecture00000007165

/-! ## 1. Domain 5A: Real Symmetric Density-Matrix Extremal Faces `𝒟_n(ℝ)` -/

def subMat {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j - B i j

def trProd {n : Nat} (A B : Mat n) : Int :=
  intSum n (fun i => intSum n (fun j => A i j * B j i))

/-- Scaled rational real density matrix `(1 / d) R ∈ 𝒟_n(ℝ)`: `d > 0`, `Rᵀ = R`, `tr(R) = d`, `R ⪰ 0`. -/
def IsRealDensity {n : Nat} (R : Mat n) (d : Int) : Prop :=
  0 < d ∧ IsSym R ∧ trMat R = d ∧ ∀ x : Vec n, 0 ≤ dot x (matVec R x)

def InRealExtremalFace {n : Nat} (A : Mat n) (lamMax : Int) (R : Mat n) (d : Int) : Prop :=
  IsRealDensity R d ∧ trProd A R = lamMax * d

def projBlock (n m : Nat) : Mat n :=
  fun i j => if i = j ∧ i.val < m then 1 else 0

def TracelessSymBlock (n m : Nat) (H : Mat n) : Prop :=
  IsSym H ∧ trMat H = 0 ∧ ∀ i j : Fin n, (m ≤ i.val ∨ m ≤ j.val) → H i j = 0

/-- Bilateral feasible tangent vector `H` at `ρ₀ = (1/m) P_m` inside `F_max^ℝ(A)`:
    there exists `d > 0` such that `(1/m) P_m ± (1/d) H ∈ F_max^ℝ(A)`. -/
def IsRealFaceTangent {n : Nat} (A : Mat n) (lamMax : Int) (m : Nat) (H : Mat n) : Prop :=
  ∃ d : Int, 0 < d ∧
    InRealExtremalFace A lamMax (addMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) ((m : Int) * d) ∧
    InRealExtremalFace A lamMax (subMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) ((m : Int) * d)

theorem dot_stdBasis_matVec_stdBasis {n : Nat} (R : Mat n) (i j : Fin n) :
    dot (stdBasis n i) (matVec R (stdBasis n j)) = R i j := by
  rw [dot_stdBasis_left]
  unfold matVec stdBasis
  have hcong : intSum n (fun k => R i k * (if k = j then 1 else 0)) =
      intSum n (fun k => if k = j then R i k else 0) := by
    apply intSum_congr
    intro k
    by_cases h : k = j <;> simp [h]
  rw [hcong, intSum_ite_eq]

theorem quad_bilinear_sym {n : Nat} {R : Mat n} (hR : IsSym R) (u v : Vec n) (t : Int) :
    dot (addVec u (smulVec t v)) (matVec R (addVec u (smulVec t v))) =
      dot u (matVec R u) + 2 * t * dot u (matVec R v) + (t * t) * dot v (matVec R v) := by
  have hmv_add : ∀ x y : Vec n, matVec R (addVec x y) = addVec (matVec R x) (matVec R y) := by
    intro x y; funext i; unfold matVec addVec
    rw [← intSum_add]
    apply intSum_congr; intro j; exact Int.mul_add _ _ _
  have hdot_add_l : ∀ a b w : Vec n, dot (addVec a b) w = dot a w + dot b w := by
    intro a b w; unfold dot addVec
    rw [← intSum_add]
    apply intSum_congr; intro i; exact Int.add_mul _ _ _
  have hdot_add_r : ∀ a b w : Vec n, dot a (addVec b w) = dot a b + dot a w := by
    intro a b w; rw [dot_comm, hdot_add_l, dot_comm b a, dot_comm w a]
  have hsym_uv : dot v (matVec R u) = dot u (matVec R v) := by
    unfold dot matVec
    have h1 : intSum n (fun i => v i * intSum n (fun j => R i j * u j)) =
        intSum n (fun i => intSum n (fun j => u j * (R j i * v i))) := by
      apply intSum_congr; intro i
      rw [← intSum_mul_left]
      apply intSum_congr; intro j
      rw [hR i j]
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [h1, intSum_comm]
    apply intSum_congr; intro j
    rw [← intSum_mul_left]
  rw [hmv_add, matVec_smulVec, hdot_add_l, hdot_add_r, hdot_add_r]
  rw [dot_smulVec, dot_smulVec, dot_comm u (smulVec t _), dot_smulVec, dot_comm (matVec R v) u]
  rw [dot_comm v (smulVec t _), dot_smulVec, dot_comm (matVec R v) v, hsym_uv]
  have : dot u (matVec R u) + t * dot u (matVec R v) +
      (t * dot u (matVec R v) + t * (t * dot v (matVec R v))) =
      dot u (matVec R u) + 2 * t * dot u (matVec R v) + (t * t) * dot v (matVec R v) := by
    have h2t : 2 * t * dot u (matVec R v) = t * dot u (matVec R v) + t * dot u (matVec R v) := by
      calc 2 * t * dot u (matVec R v)
          = (t + t) * dot u (matVec R v) := by
              have h2 : (2 : Int) * t = t + t := by omega
              rw [h2]
        _ = t * dot u (matVec R v) + t * dot u (matVec R v) := Int.add_mul t t _
    rw [h2t, Int.mul_assoc t t _]
    omega
  exact this

/-- PSD off-diagonal vanishing: if `R ⪰ 0`, `Rᵀ = R`, and `R j j = 0`, then `R i j = 0` for all `i`. -/
theorem psd_offdiag_zero_of_diag_zero {n : Nat} {R : Mat n}
    (hR : IsSym R) (hpsd : ∀ x : Vec n, 0 ≤ dot x (matVec R x))
    {j : Fin n} (hjj : R j j = 0) (i : Fin n) : R i j = 0 := by
  have hii_nonneg : 0 ≤ R i i := by
    have h := hpsd (stdBasis n i)
    rw [dot_stdBasis_matVec_stdBasis] at h
    exact h
  let t : Int := -((R i i + 1) * R i j)
  have htest := hpsd (addVec (stdBasis n i) (smulVec t (stdBasis n j)))
  rw [quad_bilinear_sym hR, dot_stdBasis_matVec_stdBasis,
      dot_stdBasis_matVec_stdBasis, dot_stdBasis_matVec_stdBasis, hjj] at htest
  simp only [Int.mul_zero, Int.add_zero] at htest
  by_cases h0 : R i j = 0
  · exact h0
  · have hsq_pos : 1 ≤ R i j * R i j := by
      have hnn := int_sq_nonneg (R i j)
      have hnz : R i j * R i j ≠ 0 := fun hz => h0 ((int_sq_eq_zero_iff _).mp hz)
      omega
    have hprod : 2 * (R i i + 1) ≤ 2 * (R i i + 1) * (R i j * R i j) := by
      have hpos : 0 ≤ 2 * (R i i + 1) := by omega
      calc 2 * (R i i + 1)
          = 2 * (R i i + 1) * 1 := by simp
        _ ≤ 2 * (R i i + 1) * (R i j * R i j) := Int.mul_le_mul_of_nonneg_left hsq_pos hpos
    have heq_t : 2 * t * R i j = - (2 * (R i i + 1) * (R i j * R i j)) := by
      simp only [t]
      simp [Int.mul_neg, Int.neg_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [heq_t] at htest
    omega

theorem trProd_diagMat {n : Nat} (eigs : Fin n → Int) (R : Mat n) :
    trProd (diagMat eigs) R = intSum n (fun i => eigs i * R i i) := by
  unfold trProd diagMat
  apply intSum_congr
  intro i
  have hcong : intSum n (fun j => (if i = j then eigs i else 0) * R j i) =
      intSum n (fun j => if j = i then eigs i * R j i else 0) := by
    apply intSum_congr
    intro j
    by_cases h : j = i
    · subst h; simp
    · have h' : i ≠ j := fun heq => h heq.symm
      simp [h, h']
  rw [hcong, intSum_ite_eq]

/-- Every state in `F_max^ℝ(diagMat eigs)` vanishes outside the upper-left `m × m` block. -/
theorem inRealExtremalFace_support {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) {R : Mat n} {d : Int}
    (hface : InRealExtremalFace (diagMat eigs) lamMax R d) :
    ∀ i j : Fin n, (m ≤ i.val ∨ m ≤ j.val) → R i j = 0 := by
  rcases hface with ⟨⟨_hd, hsym, htr, hpsd⟩, htrA⟩
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  rw [trProd_diagMat, ← htr] at htrA
  unfold trMat at htrA
  rw [← intSum_mul_left] at htrA
  have hsub : ∀ k : Nat, (f g : Fin k → Int) →
      intSum k f - intSum k g = intSum k (fun r => f r - g r) := by
    intro k f g
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [intSum]
      have := ih (fun r => f ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                 (fun r => g ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
      omega
  have hgap0 : intSum n (fun r => (lamMax - eigs r) * R r r) = 0 := by
    have hdiff : intSum n (fun r => lamMax * R r r) - intSum n (fun r => eigs r * R r r) = 0 := by
      omega
    rw [hsub] at hdiff
    rw [← hdiff]
    apply intSum_congr; intro r; rw [Int.sub_mul]
  have hterm_nn : ∀ r : Fin n, 0 ≤ (lamMax - eigs r) * R r r := by
    intro r
    have hrr : 0 ≤ R r r := by
      have h := hpsd (stdBasis n r)
      rw [dot_stdBasis_matVec_stdBasis] at h; exact h
    by_cases hr : r.val < m
    · rw [h_eq r hr]; simp
    · exact Int.mul_nonneg (by have := h_lt r (by omega); omega) hrr
  have hall := (intSum_eq_zero_iff_of_nonneg hterm_nn).mp hgap0
  have hdiag_zero : ∀ r : Fin n, m ≤ r.val → R r r = 0 := by
    intro r hr
    have hr0 := hall r
    have hne : lamMax - eigs r ≠ 0 := by have := h_lt r hr; omega
    cases Int.mul_eq_zero.mp hr0 with
    | inl h0 => exact absurd h0 hne
    | inr h0 => exact h0
  intro i j hij
  cases hij with
  | inl hi =>
    rw [hsym i j]
    exact psd_offdiag_zero_of_diag_zero hsym hpsd (hdiag_zero i hi) j
  | inr hj =>
    exact psd_offdiag_zero_of_diag_zero hsym hpsd (hdiag_zero j hj) i

def iabs (a : Int) : Int := if 0 ≤ a then a else -a

theorem iabs_nonneg (a : Int) : 0 ≤ iabs a := by
  unfold iabs; by_cases h : 0 ≤ a <;> simp [h] <;> omega

theorem iabs_quad_bound (h a b : Int) :
    0 ≤ iabs h * (a * a + b * b) + 2 * h * a * b ∧
    0 ≤ iabs h * (a * a + b * b) - 2 * h * a * b := by
  have hplus : 0 ≤ (a + b) * (a + b) := int_sq_nonneg (a + b)
  have hminus : 0 ≤ (a - b) * (a - b) := int_sq_nonneg (a - b)
  have hexp_p : (a + b) * (a + b) = a * a + b * b + 2 * a * b := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
    have : 2 * a * b = a * b + a * b := by
      have h2 : (2 : Int) * a = a + a := by omega
      rw [h2, Int.add_mul]
    omega
  have hexp_m : (a - b) * (a - b) = a * a + b * b - 2 * a * b := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
    have : 2 * a * b = a * b + a * b := by
      have h2 : (2 : Int) * a = a + a := by omega
      rw [h2, Int.add_mul]
    omega
  have hc : h * (2 * a * b) = 2 * h * a * b := by
    calc h * (2 * a * b)
        = (h * (2 * a)) * b := (Int.mul_assoc h (2 * a) b).symm
      _ = ((h * 2) * a) * b := by rw [← Int.mul_assoc h 2 a]
      _ = 2 * h * a * b := by rw [Int.mul_comm h 2]
  unfold iabs
  by_cases hh : 0 ≤ h
  · simp only [hh, ↓reduceIte]
    have h1 := Int.mul_nonneg hh hplus
    have h2 := Int.mul_nonneg hh hminus
    rw [hexp_p, Int.mul_add, hc] at h1
    rw [hexp_m, Int.mul_sub, hc] at h2
    exact ⟨h1, h2⟩
  · simp only [hh, ↓reduceIte]
    have hnh : 0 ≤ -h := by omega
    have h1 := Int.mul_nonneg hnh hminus
    have h2 := Int.mul_nonneg hnh hplus
    rw [hexp_m, Int.mul_sub, Int.neg_mul h (2 * a * b), hc] at h1
    rw [hexp_p, Int.mul_add, Int.neg_mul h (2 * a * b), hc] at h2
    constructor <;> omega

theorem sum_first_m_ones {n m : Nat} (hmn : m ≤ n) :
    intSum n (fun i => if i.val < m then (1 : Int) else 0) = (m : Int) := by
  induction m with
  | zero =>
    simp [intSum_zero_fn]
  | succ m ih =>
    have hmn' : m ≤ n := by omega
    let idx_m : Fin n := ⟨m, by omega⟩
    have hsplit : intSum n (fun i : Fin n => if i.val < m + 1 then (1 : Int) else 0) =
        intSum n (fun i : Fin n => (if i.val < m then (1 : Int) else 0) + (if i = idx_m then 1 else 0)) := by
      apply intSum_congr
      intro i
      by_cases him : i.val < m
      · have hne : i ≠ idx_m := by intro heq; have hv := congrArg Fin.val heq; simp [idx_m] at hv; omega
        have him1 : i.val < m + 1 := by omega
        simp [him, him1, hne]
      · by_cases heq : i.val = m
        · have hi_eq : i = idx_m := Fin.ext heq
          have him1 : i.val < m + 1 := by omega
          rw [if_pos him1, if_neg him, if_pos hi_eq]
          omega
        · have hne : i ≠ idx_m := fun hc => heq (congrArg Fin.val hc)
          have him1 : ¬ (i.val < m + 1) := by omega
          simp [him, him1, hne]
    rw [hsplit, intSum_add, ih hmn', intSum_ite_eq]
    omega

theorem term_le_intSum_of_nonneg {n : Nat} {f : Fin n → Int}
    (hnn : ∀ k, 0 ≤ f k) (i : Fin n) : f i ≤ intSum n f := by
  have hsplit : intSum n f =
      intSum n (fun k => if k = i then f k else 0) +
      intSum n (fun k => if k = i then 0 else f k) := by
    rw [← intSum_add]
    apply intSum_congr
    intro k
    by_cases hk : k = i <;> simp [hk]
  have hrest : 0 ≤ intSum n (fun k => if k = i then 0 else f k) := by
    apply intSum_nonneg
    intro k
    by_cases hk : k = i
    · simp [hk]
    · simp [hk]; exact hnn k
  rw [hsplit, intSum_ite_eq]
  omega

/-- Exact equivalence between geometric bilateral tangents of `F_max^ℝ(A)` at `ρ₀` and `TracelessSymBlock n m`. -/
theorem isRealFaceTangent_iff_tracelessSymBlock {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) (H : Mat n) :
    IsRealFaceTangent (diagMat eigs) lamMax m H ↔ TracelessSymBlock n m H := by
  have hm1 : 1 ≤ m := hspec.1
  have hmn : m ≤ n := hspec.2.1
  constructor
  · rintro ⟨d, _hd, hplus, hminus⟩
    have hsup_p := inRealExtremalFace_support hspec hplus
    have hsup_m := inRealExtremalFace_support hspec hminus
    rcases hplus with ⟨⟨_, hsym_p, htr_p, _⟩, _⟩
    rcases hminus with ⟨⟨_, hsym_m, _htr_m, _⟩, _⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hp := hsym_p i j
      have hm := hsym_m i j
      simp only [addMat, subMat, smulMat] at hp hm
      have hm_eq : (m : Int) * H i j = (m : Int) * H j i := by omega
      have hne : (m : Int) ≠ 0 := by omega
      exact Int.eq_of_mul_eq_mul_left hne hm_eq
    · have htr_proj : trMat (projBlock n m) = (m : Int) := by
        unfold trMat projBlock
        have hcong : intSum n (fun i => if i = i ∧ i.val < m then (1 : Int) else 0) =
            intSum n (fun i => if i.val < m then (1 : Int) else 0) := by
          apply intSum_congr; intro i; simp
        rw [hcong, sum_first_m_ones hmn]
      have htr_expand : trMat (addMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) =
          d * trMat (projBlock n m) + (m : Int) * trMat H := by
        unfold trMat addMat smulMat
        rw [intSum_add, intSum_mul_left, intSum_mul_left]
      rw [htr_expand, htr_proj, Int.mul_comm d (m : Int)] at htr_p
      have hm_tr : (m : Int) * trMat H = 0 := by omega
      have hm_ne : (m : Int) ≠ 0 := by omega
      cases Int.mul_eq_zero.mp hm_tr with
      | inl h0 => exact absurd h0 hm_ne
      | inr h0 => exact h0
    · intro i j hij
      have hp := hsup_p i j hij
      have hm := hsup_m i j hij
      simp only [addMat, subMat, smulMat] at hp hm
      have hm0 : (m : Int) * H i j = 0 := by omega
      have hne : (m : Int) ≠ 0 := by omega
      cases Int.mul_eq_zero.mp hm0 with
      | inl h0 => exact absurd h0 hne
      | inr h0 => exact h0
  · rintro ⟨hsym, htr0, hsup⟩
    let B : Int := intSum n (fun i => intSum n (fun j => iabs (H i j)))
    have hB_nn : 0 ≤ B := intSum_nonneg (fun _ => intSum_nonneg (fun _ => iabs_nonneg _))
    let d : Int := (m : Int) * (B + 1)
    have hd_pos : 0 < d := by
      have hm_pos : 0 < (m : Int) := by omega
      exact Int.mul_pos hm_pos (by omega)
    have htr_proj : trMat (projBlock n m) = (m : Int) := by
      unfold trMat projBlock
      have hcong : intSum n (fun i => if i = i ∧ i.val < m then (1 : Int) else 0) =
          intSum n (fun i => if i.val < m then (1 : Int) else 0) := by
        apply intSum_congr; intro i; simp
      rw [hcong, sum_first_m_ones hmn]
    have hpsd_both : ∀ x : Vec n,
        0 ≤ dot x (matVec (addMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) x) ∧
        0 ≤ dot x (matVec (subMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) x) := by
      intro x
      let S : Int := intSum n (fun k => if k.val < m then x k * x k else 0)
      have hS_nn : 0 ≤ S := by
        apply intSum_nonneg; intro k
        by_cases hk : k.val < m
        · simp [hk]; exact int_sq_nonneg (x k)
        · simp [hk]
      have hxk_le : ∀ k : Fin n, k.val < m → x k * x k ≤ S := by
        intro k hk
        have hle := term_le_intSum_of_nonneg (f := fun r : Fin n => if r.val < m then x r * x r else 0)
          (fun r => by by_cases hr : r.val < m <;> simp [hr, int_sq_nonneg]) k
        simpa [hk] using hle
      have hdot_proj : dot x (matVec (projBlock n m) x) = S := by
        unfold dot matVec projBlock S
        apply intSum_congr; intro i
        have hcong : intSum n (fun j => (if i = j ∧ i.val < m then 1 else 0) * x j) =
            intSum n (fun j => if j = i then (if i.val < m then x j else 0) else 0) := by
          apply intSum_congr; intro j
          by_cases hji : j = i
          · subst hji; by_cases him : j.val < m <;> simp [him]
          · have hij : i ≠ j := fun hc => hji hc.symm
            simp [hji, hij]
        rw [hcong, intSum_ite_eq]
        by_cases him : i.val < m <;> simp [him]
      have hdot_H : dot x (matVec H x) = intSum n (fun i => intSum n (fun j => H i j * x i * x j)) := by
        unfold dot matVec
        apply intSum_congr; intro i
        rw [← intSum_mul_left]
        apply intSum_congr; intro j
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      have hbound : 0 ≤ 2 * B * S + 2 * dot x (matVec H x) ∧
                    0 ≤ 2 * B * S - 2 * dot x (matVec H x) := by
        have hBS : 2 * B * S = intSum n (fun i => intSum n (fun j => 2 * iabs (H i j) * S)) := by
          dsimp only [B]
          rw [← intSum_mul_left n 2, ← intSum_mul_right n _ S]
          apply intSum_congr; intro i
          rw [← intSum_mul_left n 2, ← intSum_mul_right n _ S]
        rw [hBS, hdot_H]
        have h2H : 2 * intSum n (fun i => intSum n (fun j => H i j * x i * x j)) =
            intSum n (fun i => intSum n (fun j => 2 * H i j * x i * x j)) := by
          rw [← intSum_mul_left]
          apply intSum_congr; intro i
          rw [← intSum_mul_left]
          apply intSum_congr; intro j
          simp [Int.mul_assoc]
        rw [h2H]
        have hsub2 : ∀ (f g : Fin n → Fin n → Int),
            intSum n (fun i => intSum n (fun j => f i j)) -
            intSum n (fun i => intSum n (fun j => g i j)) =
            intSum n (fun i => intSum n (fun j => f i j - g i j)) := by
          intro f g
          have hs1 : ∀ k : Nat, (p q : Fin k → Int) →
              intSum k p - intSum k q = intSum k (fun r => p r - q r) := by
            intro k p q
            induction k with
            | zero => rfl
            | succ k ih =>
              simp only [intSum]
              have := ih (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                         (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
              omega
          rw [hs1]
          apply intSum_congr; intro i; rw [hs1]
        have hadd2 : ∀ (f g : Fin n → Fin n → Int),
            intSum n (fun i => intSum n (fun j => f i j)) +
            intSum n (fun i => intSum n (fun j => g i j)) =
            intSum n (fun i => intSum n (fun j => f i j + g i j)) := by
          intro f g
          rw [← intSum_add]
          apply intSum_congr; intro i; rw [← intSum_add]
        rw [hadd2, hsub2]
        constructor
        · apply intSum_nonneg; intro i; apply intSum_nonneg; intro j
          by_cases hij : i.val < m ∧ j.val < m
          · have hxi := hxk_le i hij.1
            have hxj := hxk_le j hij.2
            have hsum_le : x i * x i + x j * x j ≤ 2 * S := by omega
            have hmul_le := Int.mul_le_mul_of_nonneg_left hsum_le (iabs_nonneg (H i j))
            have hq := (iabs_quad_bound (H i j) (x i) (x j)).1
            have hc : iabs (H i j) * (2 * S) = 2 * iabs (H i j) * S := by
              simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            rw [hc] at hmul_le
            omega
          · have hor : m ≤ i.val ∨ m ≤ j.val := by omega
            rw [hsup i j hor]; simp [iabs]
        · apply intSum_nonneg; intro i; apply intSum_nonneg; intro j
          by_cases hij : i.val < m ∧ j.val < m
          · have hxi := hxk_le i hij.1
            have hxj := hxk_le j hij.2
            have hsum_le : x i * x i + x j * x j ≤ 2 * S := by omega
            have hmul_le := Int.mul_le_mul_of_nonneg_left hsum_le (iabs_nonneg (H i j))
            have hq := (iabs_quad_bound (H i j) (x i) (x j)).2
            have hc : iabs (H i j) * (2 * S) = 2 * iabs (H i j) * S := by
              simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            rw [hc] at hmul_le
            omega
          · have hor : m ≤ i.val ∨ m ≤ j.val := by omega
            rw [hsup i j hor]; simp [iabs]
      have hexp_p : dot x (matVec (addMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) x) =
          d * S + (m : Int) * dot x (matVec H x) := by
        rw [← hdot_proj]
        have hrow : ∀ i : Fin n,
            x i * intSum n (fun j => (d * projBlock n m i j + (m : Int) * H i j) * x j) =
            d * (x i * intSum n (fun j => projBlock n m i j * x j)) +
            (m : Int) * (x i * intSum n (fun j => H i j * x j)) := by
          intro i
          have h1 : intSum n (fun j => (d * projBlock n m i j + (m : Int) * H i j) * x j) =
              d * intSum n (fun j => projBlock n m i j * x j) +
              (m : Int) * intSum n (fun j => H i j * x j) := by
            rw [← intSum_mul_left, ← intSum_mul_left, ← intSum_add]
            apply intSum_congr; intro j
            rw [Int.add_mul, Int.mul_assoc d (projBlock n m i j) (x j), Int.mul_assoc (m : Int) (H i j) (x j)]
          rw [h1, Int.mul_add]
          have ha : x i * (d * intSum n (fun j => projBlock n m i j * x j)) =
              d * (x i * intSum n (fun j => projBlock n m i j * x j)) := by
            rw [← Int.mul_assoc, Int.mul_comm (x i) d, Int.mul_assoc]
          have hb : x i * ((m : Int) * intSum n (fun j => H i j * x j)) =
              (m : Int) * (x i * intSum n (fun j => H i j * x j)) := by
            rw [← Int.mul_assoc, Int.mul_comm (x i) (m : Int), Int.mul_assoc]
          rw [ha, hb]
        unfold dot matVec addMat smulMat
        rw [intSum_congr hrow, intSum_add, intSum_mul_left, intSum_mul_left]
      have hexp_m : dot x (matVec (subMat (smulMat d (projBlock n m)) (smulMat (m : Int) H)) x) =
          d * S - (m : Int) * dot x (matVec H x) := by
        rw [← hdot_proj]
        have hs1 : ∀ k : Nat, (p q : Fin k → Int) →
            intSum k (fun r => p r - q r) = intSum k p - intSum k q := by
          intro k p q
          induction k with
          | zero => rfl
          | succ k ih =>
            simp only [intSum]
            rw [ih (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                   (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)]
            omega
        have hrow : ∀ i : Fin n,
            x i * intSum n (fun j => (d * projBlock n m i j - (m : Int) * H i j) * x j) =
            d * (x i * intSum n (fun j => projBlock n m i j * x j)) -
            (m : Int) * (x i * intSum n (fun j => H i j * x j)) := by
          intro i
          have h1 : intSum n (fun j => (d * projBlock n m i j - (m : Int) * H i j) * x j) =
              d * intSum n (fun j => projBlock n m i j * x j) -
              (m : Int) * intSum n (fun j => H i j * x j) := by
            rw [← intSum_mul_left, ← intSum_mul_left, ← hs1]
            apply intSum_congr; intro j
            rw [Int.sub_mul, Int.mul_assoc d (projBlock n m i j) (x j), Int.mul_assoc (m : Int) (H i j) (x j)]
          rw [h1, Int.mul_sub]
          have ha : x i * (d * intSum n (fun j => projBlock n m i j * x j)) =
              d * (x i * intSum n (fun j => projBlock n m i j * x j)) := by
            rw [← Int.mul_assoc, Int.mul_comm (x i) d, Int.mul_assoc]
          have hb : x i * ((m : Int) * intSum n (fun j => H i j * x j)) =
              (m : Int) * (x i * intSum n (fun j => H i j * x j)) := by
            rw [← Int.mul_assoc, Int.mul_comm (x i) (m : Int), Int.mul_assoc]
          rw [ha, hb]
        unfold dot matVec subMat smulMat
        rw [intSum_congr hrow, hs1, intSum_mul_left, intSum_mul_left]
      rw [hexp_p, hexp_m]
      have hm_nn : 0 ≤ (m : Int) := by omega
      have hb1 := Int.mul_nonneg hm_nn hbound.1
      have hb2 := Int.mul_nonneg hm_nn hbound.2
      have hdS : 2 * (d * S) = (m : Int) * (2 * B * S) + 2 * (m : Int) * S := by
        dsimp only [d]
        calc 2 * ((m : Int) * (B + 1) * S)
            = 2 * ((m : Int) * B * S + (m : Int) * S) := by
                rw [Int.mul_add (m : Int) B 1, Int.mul_one, Int.add_mul]
          _ = 2 * ((m : Int) * B * S) + 2 * ((m : Int) * S) := Int.mul_add 2 _ _
          _ = (m : Int) * (2 * B * S) + 2 * (m : Int) * S := by
                have h1 : 2 * ((m : Int) * B * S) = (m : Int) * (2 * B * S) := by
                  rw [← Int.mul_assoc 2 ((m : Int) * B) S, ← Int.mul_assoc 2 (m : Int) B,
                      Int.mul_comm 2 (m : Int), Int.mul_assoc (m : Int) 2 B,
                      Int.mul_assoc (m : Int) (2 * B) S]
                have h2 : 2 * ((m : Int) * S) = 2 * (m : Int) * S := (Int.mul_assoc 2 (m : Int) S).symm
                rw [h1, h2]
      rw [Int.mul_add] at hb1
      rw [Int.mul_sub] at hb2
      have hmH : (m : Int) * (2 * dot x (matVec H x)) = 2 * ((m : Int) * dot x (matVec H x)) := by
        rw [← Int.mul_assoc (m : Int) 2 _, Int.mul_comm (m : Int) 2, Int.mul_assoc 2 (m : Int) _]
      rw [hmH] at hb1 hb2
      have h2mS : 0 ≤ 2 * (m : Int) * S := Int.mul_nonneg (by omega) hS_nn
      constructor <;> omega
    refine ⟨d, hd_pos, ?_, ?_⟩
    · refine ⟨⟨Int.mul_pos (by omega) hd_pos, ?_, ?_, fun x => (hpsd_both x).1⟩, ?_⟩
      · intro i j; simp only [addMat, smulMat, projBlock, hsym i j]
        by_cases h : i = j
        · subst h; simp
        · have h' : j ≠ i := fun hc => h hc.symm
          simp [h, h']
      · unfold trMat addMat smulMat
        rw [intSum_add, intSum_mul_left, intSum_mul_left]
        change d * trMat (projBlock n m) + (m : Int) * trMat H = (m : Int) * d
        rw [htr_proj, htr0]; simp [Int.mul_comm]
      · rw [trProd_diagMat]
        have hcong : intSum n (fun i => eigs i *
            (addMat (smulMat d (projBlock n m)) (smulMat (m : Int) H) i i)) =
            lamMax * (d * trMat (projBlock n m) + (m : Int) * trMat H) := by
          unfold trMat addMat smulMat
          have hc2 : lamMax * (d * intSum n (fun i => projBlock n m i i) +
              (m : Int) * intSum n (fun i => H i i)) =
              intSum n (fun i => lamMax * (d * projBlock n m i i + (m : Int) * H i i)) := by
            rw [Int.mul_add, ← intSum_mul_left, ← intSum_mul_left, ← intSum_mul_left,
                ← intSum_mul_left, ← intSum_add]
            apply intSum_congr; intro i; rw [Int.mul_add]
          rw [hc2]
          apply intSum_congr; intro i
          by_cases him : i.val < m
          · rw [hspec.2.2.1 i him]
          · have hge : m ≤ i.val := by omega
            have hH0 : H i i = 0 := hsup i i (Or.inl hge)
            have hP0 : projBlock n m i i = 0 := by simp [projBlock, him]
            rw [hH0, hP0]; simp
        rw [hcong, htr_proj, htr0]; simp [Int.mul_assoc, Int.mul_comm]
    · refine ⟨⟨Int.mul_pos (by omega) hd_pos, ?_, ?_, fun x => (hpsd_both x).2⟩, ?_⟩
      · intro i j; simp only [subMat, smulMat, projBlock, hsym i j]
        by_cases h : i = j
        · subst h; simp
        · have h' : j ≠ i := fun hc => h hc.symm
          simp [h, h']
      · have hs1 : ∀ k : Nat, (p q : Fin k → Int) →
            intSum k p - intSum k q = intSum k (fun r => p r - q r) := by
          intro k p q
          induction k with
          | zero => rfl
          | succ k ih =>
            simp only [intSum]
            have := ih (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                       (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
            omega
        unfold trMat subMat smulMat
        rw [← hs1, intSum_mul_left, intSum_mul_left]
        change d * trMat (projBlock n m) - (m : Int) * trMat H = (m : Int) * d
        rw [htr_proj, htr0]; simp [Int.mul_comm]
      · rw [trProd_diagMat]
        have hs1 : ∀ k : Nat, (p q : Fin k → Int) →
            intSum k p - intSum k q = intSum k (fun r => p r - q r) := by
          intro k p q
          induction k with
          | zero => rfl
          | succ k ih =>
            simp only [intSum]
            have := ih (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                       (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
            omega
        have hcong : intSum n (fun i => eigs i *
            (subMat (smulMat d (projBlock n m)) (smulMat (m : Int) H) i i)) =
            lamMax * (d * trMat (projBlock n m) - (m : Int) * trMat H) := by
          unfold trMat subMat smulMat
          rw [Int.mul_sub, ← intSum_mul_left, ← intSum_mul_left, ← intSum_mul_left,
              ← intSum_mul_left, hs1]
          apply intSum_congr; intro i
          by_cases him : i.val < m
          · rw [hspec.2.2.1 i him, Int.mul_sub]
          · have hge : m ≤ i.val := by omega
            have hH0 : H i i = 0 := hsup i i (Or.inl hge)
            have hP0 : projBlock n m i i = 0 := by simp [projBlock, him]
            rw [hH0, hP0]; simp
        rw [hcong, htr_proj, htr0]; simp [Int.mul_assoc, Int.mul_comm]

/-! ## 2. Exact Border-Splitting Dimension Induction for `TracelessSymBlock` and `TracelessHermBlock` -/

def symPairMat (n : Nat) (i j : Fin n) : Mat n :=
  fun r s => (if r = i ∧ s = j then 1 else 0) + (if r = j ∧ s = i then 1 else 0)

def diagDiffMat (n : Nat) (k₀ k : Fin n) : Mat n :=
  fun r s => (if r = k ∧ s = k then 1 else 0) - (if r = k₀ ∧ s = k₀ then 1 else 0)

/-- Border space bridging `TracelessSymBlock n m` to `TracelessSymBlock n (m + 1)`. -/
def SymBorder (n m : Nat) (_hm : m + 1 ≤ n) (B : Mat n) : Prop :=
  IsSym B ∧ trMat B = 0 ∧
  (∀ i j : Fin n, (m + 1 ≤ i.val ∨ m + 1 ≤ j.val) → B i j = 0) ∧
  (∀ i j : Fin n, i.val < m → j.val < m → (i.val ≠ 0 ∨ j.val ≠ 0) → B i j = 0)

theorem symBorder_hasDim {n m : Nat} (hm1 : 1 ≤ m) (hm : m + 1 ≤ n) :
    ZMod.HasDim (matZMod n) (SymBorder n m hm) (m + 1) := by
  let idx₀ : Fin n := ⟨0, by omega⟩
  let idx_m : Fin n := ⟨m, hm⟩
  let b : Fin (m + 1) → Mat n := fun k =>
    if hk : k.val < m then symPairMat n ⟨k.val, by omega⟩ idx_m
    else diagDiffMat n idx₀ idx_m
  let coord : Mat n → Fin (m + 1) → Int := fun B k =>
    if hk : k.val < m then B ⟨k.val, by omega⟩ idx_m
    else B idx_m idx_m
  apply ZMod.hasDim_of_coords (matZMod n) b coord
  · intro k
    unfold SymBorder
    by_cases hk : k.val < m
    · simp only [b, hk, ↓reduceDIte]
      have hkm_ne : (⟨k.val, by omega⟩ : Fin n) ≠ idx_m := by
        intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m] at hv; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r s; unfold symPairMat
        by_cases hrj : r = ⟨k.val, by omega⟩ <;> by_cases hsm : s = idx_m <;>
        by_cases hrm : r = idx_m <;> by_cases hsj : s = ⟨k.val, by omega⟩
        all_goals (simp_all <;> omega)
      · unfold trMat symPairMat
        rw [intSum_congr (g := fun _ => 0)]
        · exact intSum_zero_fn n
        · intro r
          by_cases hr1 : r = ⟨k.val, by omega⟩
          · subst hr1; simp [hkm_ne]
          · simp [hr1]
      · intro r s hrs
        unfold symPairMat
        have h1 : ¬ (r = ⟨k.val, by omega⟩ ∧ s = idx_m) := by
          rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
        have h2 : ¬ (r = idx_m ∧ s = ⟨k.val, by omega⟩) := by
          rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
        simp [h1, h2]
      · intro r s hr hs _h0
        unfold symPairMat
        have h1 : ¬ (r = ⟨k.val, by omega⟩ ∧ s = idx_m) := by
          rintro ⟨_, rfl⟩; dsimp only [idx_m] at hs; omega
        have h2 : ¬ (r = idx_m ∧ s = ⟨k.val, by omega⟩) := by
          rintro ⟨rfl, _⟩; dsimp only [idx_m] at hr; omega
        simp [h1, h2]
    · simp only [b, hk, ↓reduceDIte]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r s; unfold diagDiffMat
        by_cases hr_m : r = idx_m <;> by_cases hs_m : s = idx_m <;>
        by_cases hr_0 : r = idx₀ <;> by_cases hs_0 : s = idx₀
        all_goals (simp_all <;> omega)
      · unfold trMat diagDiffMat
        have hsub : ∀ d : Nat, (f g : Fin d → Int) →
            intSum d (fun r => f r - g r) = intSum d f - intSum d g := by
          intro d f g
          induction d with
          | zero => rfl
          | succ d ih =>
            simp only [intSum]
            rw [ih (fun r => f ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                   (fun r => g ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)]
            omega
        rw [hsub]
        have hc1 : intSum n (fun r => if r = idx_m ∧ r = idx_m then (1 : Int) else 0) =
            intSum n (fun r => if r = idx_m then (1 : Int) else 0) := by
          apply intSum_congr; intro r; simp
        have hc2 : intSum n (fun r => if r = idx₀ ∧ r = idx₀ then (1 : Int) else 0) =
            intSum n (fun r => if r = idx₀ then (1 : Int) else 0) := by
          apply intSum_congr; intro r; simp
        rw [hc1, hc2, intSum_ite_eq, intSum_ite_eq]; omega
      · intro r s hrs
        unfold diagDiffMat
        have h1 : ¬ (r = idx_m ∧ s = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
        have h2 : ¬ (r = idx₀ ∧ s = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hrs; omega
        simp [h1, h2]
      · intro r s hr _hs h0
        unfold diagDiffMat
        have h1 : ¬ (r = idx_m ∧ s = idx_m) := by rintro ⟨rfl, _⟩; dsimp only [idx_m] at hr; omega
        have h2 : ¬ (r = idx₀ ∧ s = idx₀) := by
          rintro ⟨rfl, rfl⟩; simp [idx₀] at h0
        simp [h1, h2]
  · intro c k
    dsimp only [coord]
    unfold ZMod.linComb
    by_cases hk : k.val < m
    · simp only [hk, ↓reduceDIte]
      rw [matFinSum_apply]
      have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (c r) (b r)) ⟨k.val, by omega⟩ idx_m) =
          intSum (m + 1) (fun r => if r = k then c r else 0) := by
        apply intSum_congr; intro r
        simp only [matZMod, smulMat, b]
        by_cases hr : r.val < m
        · simp only [hr, ↓reduceDIte, symPairMat]
          have hkm : (⟨k.val, by omega⟩ : Fin n) ≠ idx_m := by
            intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m] at hv; omega
          by_cases hrk : r = k
          · subst hrk; simp [hkm]
          · have hk_ne : k.val ≠ r.val := fun hv => hrk (Fin.ext hv.symm)
            simp [hrk, hk_ne, hkm]
        · simp only [hr, ↓reduceDIte, diagDiffMat]
          have hrk : r ≠ k := by intro heq; subst heq; exact hr hk
          have hkm : (⟨k.val, by omega⟩ : Fin n) ≠ idx_m := by
            intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m] at hv; omega
          have hm0 : idx_m ≠ idx₀ := by
            intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m, idx₀] at hv; omega
          simp [hrk, hkm, hm0]
      rw [hcong, intSum_ite_eq]
    · simp only [hk, ↓reduceDIte]
      let k_last : Fin (m + 1) := ⟨m, by omega⟩
      have hk_eq : k = k_last := by ext; dsimp only [k_last]; omega
      rw [matFinSum_apply]
      have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (c r) (b r)) idx_m idx_m) =
          intSum (m + 1) (fun r => if r = k_last then c r else 0) := by
        apply intSum_congr; intro r
        simp only [matZMod, smulMat, b]
        by_cases hr : r.val < m
        · simp only [hr, ↓reduceDIte, symPairMat]
          have hrk : r ≠ k_last := by intro heq; have hv := congrArg Fin.val heq; dsimp only [k_last] at hv; omega
          have hne : idx_m ≠ ⟨r.val, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m] at hv; omega
          simp [hrk, hne, hne.symm]
        · simp only [hr, ↓reduceDIte, diagDiffMat]
          have hrk : r = k_last := by ext; dsimp only [k_last]; omega
          have hne : idx_m ≠ idx₀ := by
            intro heq; have hv := congrArg Fin.val heq; dsimp only [idx_m, idx₀] at hv; omega
          simp [hrk, hne]
      rw [hcong, intSum_ite_eq, hk_eq]
  · intro k
    simp only [coord, matZMod, zeroMat]
    by_cases hk : k.val < m <;> simp [hk]
  · intro B ⟨hsym, htr0, hsup, hinner⟩
    have hB00 : B idx₀ idx₀ = - B idx_m idx_m := by
      have htr_calc : trMat B = intSum n (fun r =>
          (if r = idx₀ then B idx₀ idx₀ else 0) + (if r = idx_m then B idx_m idx_m else 0)) := by
        unfold trMat
        apply intSum_congr; intro r
        by_cases hr0 : r = idx₀
        · subst hr0
          have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
          simp [hne]
        · by_cases hrm : r = idx_m
          · subst hrm; simp [hr0]
          · simp only [hr0, hrm, ↓reduceIte, Int.add_zero]
            by_cases hlt : r.val < m
            · exact hinner r r hlt hlt (Or.inl (fun hv => hr0 (Fin.ext hv)))
            · have hge : m + 1 ≤ r.val := by
                have hne_v : r.val ≠ m := fun hv => hrm (Fin.ext hv)
                omega
              exact hsup r r (Or.inl hge)
      rw [htr_calc, intSum_add, intSum_ite_eq, intSum_ite_eq] at htr0
      omega
    funext i j
    unfold ZMod.linComb
    rw [matFinSum_apply]
    by_cases hhigh : m + 1 ≤ i.val ∨ m + 1 ≤ j.val
    · rw [hsup i j hhigh]
      rw [intSum_congr (g := fun _ => 0)]
      · exact (intSum_zero_fn (m + 1)).symm
      · intro r
        simp only [matZMod, smulMat, b]
        by_cases hr : r.val < m
        · simp only [hr, ↓reduceDIte, symPairMat]
          have h1 : ¬ (i = ⟨r.val, by omega⟩ ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx_m ∧ j = ⟨r.val, by omega⟩) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          simp [h1, h2]
        · simp only [hr, ↓reduceDIte, diagDiffMat]
          have h1 : ¬ (i = idx_m ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hhigh; omega
          simp [h1, h2]
    · by_cases him : i = idx_m
      · subst him
        by_cases hjm : j = idx_m
        · subst hjm
          let k_last : Fin (m + 1) := ⟨m, by omega⟩
          have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (coord B r) (b r)) idx_m idx_m) =
              intSum (m + 1) (fun r => if r = k_last then B idx_m idx_m else 0) := by
            apply intSum_congr; intro r
            simp only [matZMod, smulMat, b, coord]
            by_cases hr : r.val < m
            · have hrk : r ≠ k_last := by intro hc; have hv := congrArg Fin.val hc; dsimp only [k_last] at hv; omega
              have hne : idx_m ≠ ⟨r.val, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
              simp [hr, hrk, symPairMat, hne]
            · have hrk : r = k_last := by ext; dsimp only [k_last]; omega
              have hne : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
              simp [k_last, hr, hrk, diagDiffMat, hne]
          rw [hcong, intSum_ite_eq]
        · have hj_lt : j.val < m := by
            have hj_ne : j.val ≠ m := fun hv => hjm (Fin.ext hv)
            omega
          let k_j : Fin (m + 1) := ⟨j.val, by omega⟩
          have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (coord B r) (b r)) idx_m j) =
              intSum (m + 1) (fun r => if r = k_j then B idx_m j else 0) := by
            apply intSum_congr; intro r
            simp only [matZMod, smulMat, b, coord]
            by_cases hr : r.val < m
            · simp only [hr, ↓reduceDIte, symPairMat]
              have h1 : idx_m ≠ ⟨r.val, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
              by_cases hrk : r = k_j
              · subst hrk
                have hj_eq : (⟨k_j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
                simp [k_j, hj_lt, h1, hjm, Ne.symm hjm, hj_eq, hsym j idx_m]
              · have hj_ne : j ≠ ⟨r.val, by omega⟩ := by
                  intro hc; apply hrk; ext; exact (congrArg Fin.val hc).symm
                simp [hrk, h1, hj_ne]
            · simp only [hr, ↓reduceDIte, diagDiffMat]
              have hrk : r ≠ k_j := by intro hc; subst hc; exact hr hj_lt
              have hne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
              simp [hrk, hjm, Ne.symm hjm, hne0]
          rw [hcong, intSum_ite_eq]
      · have hi_lt : i.val < m := by
          have hi_ne : i.val ≠ m := fun hv => him (Fin.ext hv)
          omega
        by_cases hjm : j = idx_m
        · subst hjm
          let k_i : Fin (m + 1) := ⟨i.val, by omega⟩
          have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (coord B r) (b r)) i idx_m) =
              intSum (m + 1) (fun r => if r = k_i then B i idx_m else 0) := by
            apply intSum_congr; intro r
            simp only [matZMod, smulMat, b, coord]
            by_cases hr : r.val < m
            · simp only [hr, ↓reduceDIte, symPairMat]
              have h2 : i ≠ idx_m := him
              by_cases hrk : r = k_i
              · subst hrk
                have hi_eq : (⟨k_i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
                simp [k_i, hi_lt, h2, h2.symm, hi_eq]
              · have hi_ne : i ≠ ⟨r.val, by omega⟩ := by
                  intro hc; apply hrk; ext; exact (congrArg Fin.val hc).symm
                simp [hrk, hi_ne, h2]
            · simp only [hr, ↓reduceDIte, diagDiffMat]
              have hrk : r ≠ k_i := by intro hc; subst hc; exact hr hi_lt
              have hne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
              simp [hrk, him, Ne.symm him, hne0]
          rw [hcong, intSum_ite_eq]
        · have hj_lt : j.val < m := by
            have hj_ne : j.val ≠ m := fun hv => hjm (Fin.ext hv)
            omega
          by_cases hij0 : i = idx₀ ∧ j = idx₀
          · rcases hij0 with ⟨rfl, rfl⟩
            rw [hB00]
            let k_last : Fin (m + 1) := ⟨m, by omega⟩
            have hcong : intSum (m + 1) (fun r => ((matZMod n).smul (coord B r) (b r)) idx₀ idx₀) =
                intSum (m + 1) (fun r => if r = k_last then - B idx_m idx_m else 0) := by
              apply intSum_congr; intro r
              simp only [matZMod, smulMat, b, coord]
              by_cases hr : r.val < m
              · have hrk : r ≠ k_last := by intro hc; have hv := congrArg Fin.val hc; dsimp only [k_last] at hv; omega
                have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                simp [hr, hrk, symPairMat, hne]
              · have hrk : r = k_last := by ext; dsimp only [k_last]; omega
                have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                simp [k_last, hr, hrk, diagDiffMat, hne]
            rw [hcong, intSum_ite_eq]
          · have hnz0 : i.val ≠ 0 ∨ j.val ≠ 0 := by
              by_cases hi0 : i.val = 0
              · right; intro hj0; exact hij0 ⟨Fin.ext hi0, Fin.ext hj0⟩
              · left; exact hi0
            rw [hinner i j hi_lt hj_lt hnz0]
            rw [intSum_congr (g := fun _ => 0)]
            · exact (intSum_zero_fn (m + 1)).symm
            · intro r
              simp only [matZMod, smulMat, b]
              by_cases hr : r.val < m
              · simp [hr, symPairMat, him, hjm]
              · simp [hr, diagDiffMat, him, hij0]

/-- Exact real dimension of `TracelessSymBlock n m`: `m * (m + 1) / 2 - 1` for all `1 ≤ m ≤ n`. -/
theorem tracelessSymBlock_hasDim {n m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ZMod.HasDim (matZMod n) (TracelessSymBlock n m) (m * (m + 1) / 2 - 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.zero_add, Nat.mul_div_cancel]
      -- `m = 1`: `TracelessSymBlock n 1 = {0}` has dimension `0`
      let b : Fin 0 → Mat n := Fin.elim0
      refine ⟨b, fun i => Fin.elim0 i, fun c _ i => Fin.elim0 i, ?_⟩
      intro H ⟨_hsym, htr0, hsup⟩
      let z0 : Fin n := ⟨0, by omega⟩
      refine ⟨Fin.elim0, ?_⟩
      funext i j
      simp only [ZMod.linComb, ZMod.finSum, matZMod, zeroMat]
      by_cases hi0 : i.val = 0
      · by_cases hj0 : j.val = 0
        · have hi_eq : i = z0 := Fin.ext hi0
          have hj_eq : j = z0 := Fin.ext hj0
          have htr_calc : trMat H = intSum n (fun r => if r = z0 then H z0 z0 else 0) := by
            unfold trMat; apply intSum_congr; intro r
            by_cases hr : r = z0
            · subst hr; simp
            · have hge : 1 ≤ r.val := by
                by_cases hrz : r.val = 0
                · exact absurd (Fin.ext hrz) hr
                · omega
              rw [hsup r r (Or.inl hge)]; simp [hr]
          rw [htr_calc, intSum_ite_eq] at htr0
          exact hi_eq ▸ hj_eq ▸ htr0
        · exact hsup i j (Or.inr (by omega))
      · exact hsup i j (Or.inl (by omega))
    · have hk1 : 1 ≤ k := by omega
      have hkn : k ≤ n := by omega
      have hd_ih := ih hk1 hkn
      have hd_b := symBorder_hasDim hk1 hmn
      have harith : (k * (k + 1) / 2 - 1) + (k + 1) = (k + 1) * (k + 2) / 2 - 1 := by
        have hdiv : (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by
          calc (k + 1) * (k + 2)
              = (k + 1) * k + (k + 1) * 2 := Nat.mul_add (k + 1) k 2
            _ = k * (k + 1) + 2 * (k + 1) := by rw [Nat.mul_comm (k + 1) k, Nat.mul_comm (k + 1) 2]
        have hpos_div : 1 ≤ k * (k + 1) / 2 := by
          have h2 : 2 ≤ k * (k + 1) := by
            calc 2 = 1 * 2 := rfl
              _ ≤ k * (k + 1) := Nat.mul_le_mul hk1 (by omega)
          omega
        rw [hdiv, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
        omega
      rw [← harith]
      apply ZMod.hasDim_directSum (matZMod n) hd_ih hd_b
      · intro v ⟨hs, ht, hsp⟩ c
        refine ⟨fun i j => by simp [matZMod, smulMat, hs i j], ?_, fun i j hij => by simp [matZMod, smulMat, hsp i j hij]⟩
        unfold trMat; simp only [matZMod, smulMat]; rw [intSum_mul_left]; change c * trMat v = 0; rw [ht]; simp
      · intro v ⟨hs, ht, hsp, hin⟩ c
        refine ⟨fun i j => by simp [matZMod, smulMat, hs i j], ?_,
                fun i j hij => by simp [matZMod, smulMat, hsp i j hij],
                fun i j hi hj h0 => by simp [matZMod, smulMat, hin i j hi hj h0]⟩
        unfold trMat; simp only [matZMod, smulMat]; rw [intSum_mul_left]; change c * trMat v = 0; rw [ht]; simp
      · intro u v ⟨hsu, htu, hspu⟩ ⟨hsv, htv, hspv⟩
        refine ⟨fun i j => by simp [matZMod, addMat, hsu i j, hsv i j], ?_,
                fun i j hij => by simp [matZMod, addMat, hspu i j hij, hspv i j hij]⟩
        unfold trMat; simp only [matZMod, addMat]; rw [intSum_add]; change trMat u + trMat v = 0; omega
      · intro u v ⟨hsu, htu, hspu, hinu⟩ ⟨hsv, htv, hspv, hinv⟩
        refine ⟨fun i j => by simp [matZMod, addMat, hsu i j, hsv i j], ?_,
                fun i j hij => by simp [matZMod, addMat, hspu i j hij, hspv i j hij],
                fun i j hi hj h0 => by simp [matZMod, addMat, hinu i j hi hj h0, hinv i j hi hj h0]⟩
        unfold trMat; simp only [matZMod, addMat]; rw [intSum_add]; change trMat u + trMat v = 0; omega
      · refine ⟨fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
        unfold trMat; simp [matZMod, zeroMat, intSum_zero_fn]
      · refine ⟨fun _ _ => rfl, ?_, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
        unfold trMat; simp [matZMod, zeroMat, intSum_zero_fn]
      · intro v ⟨hs, ht, hsp⟩
        exact ⟨hs, ht, fun i j hij => hsp i j (by omega)⟩
      · intro v ⟨hs, ht, hsp, _⟩
        exact ⟨hs, ht, hsp⟩
      · intro u v ⟨hsu, htu, hspu⟩ ⟨hsv, htv, hspv⟩
        refine ⟨fun i j => by simp [matZMod, addMat, hsu i j, hsv i j], ?_,
                fun i j hij => by simp [matZMod, addMat, hspu i j hij, hspv i j hij]⟩
        unfold trMat; simp only [matZMod, addMat]; rw [intSum_add]; change trMat u + trMat v = 0; omega
      · intro H ⟨hsH, htH, hspH⟩
        let idx₀ : Fin n := ⟨0, by omega⟩
        let idx_k : Fin n := ⟨k, hmn⟩
        let B : Mat n := fun i j =>
          if i = idx₀ ∧ j = idx₀ then - H idx_k idx_k
          else if i.val = k ∨ j.val = k then H i j
          else 0
        let P : Mat n := subMat H B
        have hB_mem : SymBorder n k hmn B := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i j
            simp only [B]
            by_cases h0 : i = idx₀ ∧ j = idx₀
            · rcases h0 with ⟨rfl, rfl⟩; simp
            · have h0' : ¬ (j = idx₀ ∧ i = idx₀) := fun ⟨hj, hi⟩ => h0 ⟨hi, hj⟩
              simp only [h0, h0', ↓reduceIte]
              by_cases hk_ij : i.val = k ∨ j.val = k
              · have hk_ji : j.val = k ∨ i.val = k := hk_ij.symm
                simp [hk_ij, hk_ji, hsH i j]
              · have hk_ji : ¬ (j.val = k ∨ i.val = k) := fun h => hk_ij h.symm
                simp [hk_ij, hk_ji]
          · have htrB : trMat B = intSum n (fun r =>
                (if r = idx₀ then - H idx_k idx_k else 0) +
                (if r = idx_k then H idx_k idx_k else 0)) := by
              unfold trMat; apply intSum_congr; intro r
              simp only [B]
              by_cases hr0 : r = idx₀
              · subst hr0
                have hne : idx₀ ≠ idx_k := by intro hc; have hv := congrArg Fin.val hc; simp [idx₀, idx_k] at hv; omega
                simp [hne]
              · by_cases hrk : r = idx_k
                · subst hrk; simp [hr0, idx_k]
                · have hrkv : r.val ≠ k := fun hv => hrk (Fin.ext hv)
                  simp [hr0, hrk, hrkv]
            rw [htrB, intSum_add, intSum_ite_eq, intSum_ite_eq]; omega
          · intro i j hij
            simp only [B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hij; omega
            simp only [h0, ↓reduceIte]
            by_cases hkv : i.val = k ∨ j.val = k
            · simp [hkv, hspH i j hij]
            · simp [hkv]
          · intro i j _hi _hj hnz
            simp only [B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; simp [idx₀] at hnz
            have hkv : ¬ (i.val = k ∨ j.val = k) := by omega
            simp [h0, hkv]
        have hP_mem : TracelessSymBlock n k P := by
          refine ⟨?_, ?_, ?_⟩
          · intro i j; simp [P, subMat, hsH i j, hB_mem.1 i j]
          · have hs1 : ∀ d : Nat, (p q : Fin d → Int) →
                intSum d (fun r => p r - q r) = intSum d p - intSum d q := by
              intro d p q
              induction d with
              | zero => rfl
              | succ d ih2 =>
                simp only [intSum]
                rw [ih2 (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                        (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)]
                omega
            unfold trMat P subMat
            rw [hs1]
            change trMat H - trMat B = 0
            rw [htH, hB_mem.2.1]; rfl
          · intro i j hij
            simp only [P, subMat, B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hij; omega
            simp only [h0, ↓reduceIte]
            by_cases hkv : i.val = k ∨ j.val = k
            · simp [hkv]
            · have hge1 : k + 1 ≤ i.val ∨ k + 1 ≤ j.val := by omega
              simp [hkv, hspH i j hge1]
        refine ⟨P, B, hP_mem, hB_mem, ?_⟩
        funext i j; simp [matZMod, addMat, P, subMat]
      · intro P B ⟨_hsP, htP, hspP⟩ ⟨_hsB, _htB, hspB, hinB⟩ hsum0
        let z0 : Fin n := ⟨0, by omega⟩
        have hPB : ∀ i j, P i j + B i j = 0 := fun i j => congrFun (congrFun hsum0 i) j
        have hB_zero : ∀ i j, B i j = 0 := by
          intro i j
          by_cases hhigh : k + 1 ≤ i.val ∨ k + 1 ≤ j.val
          · exact hspB i j hhigh
          · by_cases hbord : k ≤ i.val ∨ k ≤ j.val
            · have hP0 := hspP i j hbord
              have := hPB i j; omega
            · by_cases hij0 : i.val = 0 ∧ j.val = 0
              · have hP_other : ∀ r : Fin n, r.val ≠ 0 → P r r = 0 := by
                  intro r hr0
                  by_cases hrk : r.val < k
                  · have hBr := hinB r r hrk hrk (Or.inl hr0)
                    have := hPB r r; omega
                  · exact hspP r r (Or.inl (by omega))
                have htrP_calc : trMat P = intSum n (fun r => if r = z0 then P z0 z0 else 0) := by
                  unfold trMat; apply intSum_congr; intro r
                  by_cases hr : r = z0
                  · subst hr; simp
                  · have hrv : r.val ≠ 0 := fun hv => hr (Fin.ext hv)
                    rw [hP_other r hrv]; simp [hr]
                rw [htrP_calc, intSum_ite_eq] at htP
                have hB00 : B z0 z0 = 0 := by have := hPB z0 z0; omega
                have hi_eq : i = z0 := Fin.ext hij0.1
                have hj_eq : j = z0 := Fin.ext hij0.2
                exact hi_eq ▸ hj_eq ▸ hB00
              · exact hinB i j (by omega) (by omega) (by omega)
        have hB_eq : B = zeroMat n := by funext i j; exact hB_zero i j
        have hP_eq : P = zeroMat n := by
          funext i j
          have := hPB i j
          rw [hB_zero i j] at this
          simp [zeroMat]; omega
        exact ⟨hP_eq, hB_eq⟩

/-- Refutation for real density matrices: `m * (m + 1) / 2 - 1 ≠ m` for `m = 1` and ALL `m ≥ 3`! -/
theorem real_density_dim_ne_m {m : Nat} (hm1 : 1 ≤ m) (hm_ne2 : m ≠ 2) :
    m * (m + 1) / 2 - 1 ≠ m := by
  by_cases hm_eq1 : m = 1
  · subst hm_eq1; decide
  · have hm3 : 3 ≤ m := by omega
    have hprod : 2 * (m + 2) ≤ m * (m + 1) := by
      calc 2 * (m + 2)
          ≤ 3 * (m + 1) := by omega
        _ ≤ m * (m + 1) := Nat.mul_le_mul_right (m + 1) hm3
    omega

theorem tracelessSymBlock_not_hasDim_m {n m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ n) (hm_ne2 : m ≠ 2) :
    ¬ ZMod.HasDim (matZMod n) (TracelessSymBlock n m) m :=
  ZMod.not_hasDim_of_ne (matZMod n) (tracelessSymBlock_hasDim hm1 hmn) (real_density_dim_ne_m hm1 hm_ne2)

/-! ## 3. Domain 5B: Complex Hermitian Density-Matrix Extremal Faces `𝒟_n(ℂ)` -/

def subCMat {n : Nat} (A B : CMat n) : CMat n := fun i j => GaussInt.sub (A i j) (B i j)

def cTrRe {n : Nat} (A : CMat n) : Int := intSum n (fun i => (A i i).re)

def cTrProdRe {n : Nat} (A B : CMat n) : Int :=
  intSum n (fun i => intSum n (fun j => (GaussInt.mul (A i j) (B j i)).re))

def IsComplexDensity {n : Nat} (R : CMat n) (d : Int) : Prop :=
  0 < d ∧ IsHermitian R ∧ cTrRe R = d ∧ ∀ z : CVec n, 0 ≤ (hermInner z (cMatVec R z)).re

def InComplexExtremalFace {n : Nat} (A : CMat n) (lamMax : Int) (R : CMat n) (d : Int) : Prop :=
  IsComplexDensity R d ∧ cTrProdRe A R = lamMax * d

def cProjBlock (n m : Nat) : CMat n :=
  fun i j => if i = j ∧ i.val < m then GaussInt.one else GaussInt.zero

def TracelessHermBlock (n m : Nat) (H : CMat n) : Prop :=
  IsHermitian H ∧ cTrRe H = 0 ∧ ∀ i j : Fin n, (m ≤ i.val ∨ m ≤ j.val) → H i j = GaussInt.zero

def IsComplexFaceTangent {n : Nat} (A : CMat n) (lamMax : Int) (m : Nat) (H : CMat n) : Prop :=
  ∃ d : Int, 0 < d ∧
    InComplexExtremalFace A lamMax
      (addCMat (rSmulCMat d (cProjBlock n m)) (rSmulCMat (m : Int) H)) ((m : Int) * d) ∧
    InComplexExtremalFace A lamMax
      (subCMat (rSmulCMat d (cProjBlock n m)) (rSmulCMat (m : Int) H)) ((m : Int) * d)

theorem cMatFinSum_apply (n d : Nat) (f : Fin d → CMat n) (i j : Fin n) :
    ZMod.finSum (cMatRMod n) d f i j = gaussSum d (fun k => f k i j) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [ZMod.finSum, gaussSum]
    change addCMat (ZMod.finSum (cMatRMod n) d (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
      (f ⟨d, Nat.lt_succ_self d⟩) i j = _
    simp only [addCMat, ih]

def hermRealPair (n : Nat) (i j : Fin n) : CMat n :=
  fun r s => GaussInt.add (if r = i ∧ s = j then GaussInt.one else GaussInt.zero)
                          (if r = j ∧ s = i then GaussInt.one else GaussInt.zero)

def hermImagPair (n : Nat) (i j : Fin n) : CMat n :=
  fun r s => GaussInt.sub (if r = i ∧ s = j then GaussInt.I else GaussInt.zero)
                          (if r = j ∧ s = i then GaussInt.I else GaussInt.zero)

def cDiagDiffMat (n : Nat) (k₀ k : Fin n) : CMat n :=
  fun r s => GaussInt.sub (if r = k ∧ s = k then GaussInt.one else GaussInt.zero)
                          (if r = k₀ ∧ s = k₀ then GaussInt.one else GaussInt.zero)

def HermBorder (n m : Nat) (_hm : m + 1 ≤ n) (B : CMat n) : Prop :=
  IsHermitian B ∧ cTrRe B = 0 ∧
  (∀ i j : Fin n, (m + 1 ≤ i.val ∨ m + 1 ≤ j.val) → B i j = GaussInt.zero) ∧
  (∀ i j : Fin n, i.val < m → j.val < m → (i.val ≠ 0 ∨ j.val ≠ 0) → B i j = GaussInt.zero)

theorem hermBorder_hasDim {n m : Nat} (hm1 : 1 ≤ m) (hm : m + 1 ≤ n) :
    ZMod.HasDim (cMatRMod n) (HermBorder n m hm) (2 * m + 1) := by
  let idx₀ : Fin n := ⟨0, by omega⟩
  let idx_m : Fin n := ⟨m, hm⟩
  let b : Fin (2 * m + 1) → CMat n := fun k =>
    if hk : k.val < 2 * m then
      let j : Fin n := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then hermRealPair n j idx_m else hermImagPair n j idx_m
    else cDiagDiffMat n idx₀ idx_m
  let coord : CMat n → Fin (2 * m + 1) → Int := fun B k =>
    if hk : k.val < 2 * m then
      let j : Fin n := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then (B j idx_m).re else (B j idx_m).im
    else (B idx_m idx_m).re
  apply ZMod.hasDim_of_coords (cMatRMod n) b coord
  · intro k
    unfold HermBorder
    by_cases hk : k.val < 2 * m
    · simp only [b, hk, ↓reduceDIte]
      have hj_ne : (⟨k.val / 2, by omega⟩ : Fin n) ≠ idx_m := by
        intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
      by_cases hmod : k.val % 2 = 0
      · simp only [hmod, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r s; unfold hermRealPair
          by_cases hrj : r = ⟨k.val / 2, by omega⟩ <;> by_cases hsm : s = idx_m <;>
          by_cases hrm : r = idx_m <;> by_cases hsj : s = ⟨k.val / 2, by omega⟩
          all_goals (ext <;> simp_all [GaussInt.add, GaussInt.conj, GaussInt.one, GaussInt.zero] <;> omega)
        · unfold cTrRe hermRealPair
          rw [intSum_congr (g := fun _ => 0)]
          · exact intSum_zero_fn n
          · intro r
            by_cases hr : r = ⟨k.val / 2, by omega⟩
            · subst hr; simp [hj_ne, GaussInt.add, GaussInt.zero]
            · simp [hr, GaussInt.add, GaussInt.zero]
        · intro r s hrs; unfold hermRealPair
          have h1 : ¬ (r = ⟨k.val / 2, by omega⟩ ∧ s = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
          have h2 : ¬ (r = idx_m ∧ s = ⟨k.val / 2, by omega⟩) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
          simp [h1, h2, GaussInt.add, GaussInt.zero]
        · intro r s hr hs _h0; unfold hermRealPair
          have h1 : ¬ (r = ⟨k.val / 2, by omega⟩ ∧ s = idx_m) := by rintro ⟨_, rfl⟩; dsimp only [idx_m] at hs; omega
          have h2 : ¬ (r = idx_m ∧ s = ⟨k.val / 2, by omega⟩) := by rintro ⟨rfl, _⟩; dsimp only [idx_m] at hr; omega
          simp [h1, h2, GaussInt.add, GaussInt.zero]
      · simp only [hmod, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r s; unfold hermImagPair
          by_cases hrj : r = ⟨k.val / 2, by omega⟩ <;> by_cases hsm : s = idx_m <;>
          by_cases hrm : r = idx_m <;> by_cases hsj : s = ⟨k.val / 2, by omega⟩
          all_goals (ext <;> simp_all [GaussInt.sub, GaussInt.conj, GaussInt.I, GaussInt.zero] <;> omega)
        · unfold cTrRe hermImagPair
          rw [intSum_congr (g := fun _ => 0)]
          · exact intSum_zero_fn n
          · intro r
            by_cases hr : r = ⟨k.val / 2, by omega⟩
            · subst hr; simp [hj_ne, GaussInt.sub, GaussInt.zero]
            · simp [hr, GaussInt.sub, GaussInt.zero]
        · intro r s hrs; unfold hermImagPair
          have h1 : ¬ (r = ⟨k.val / 2, by omega⟩ ∧ s = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
          have h2 : ¬ (r = idx_m ∧ s = ⟨k.val / 2, by omega⟩) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
          simp [h1, h2, GaussInt.sub, GaussInt.zero]
        · intro r s hr hs _h0; unfold hermImagPair
          have h1 : ¬ (r = ⟨k.val / 2, by omega⟩ ∧ s = idx_m) := by rintro ⟨_, rfl⟩; dsimp only [idx_m] at hs; omega
          have h2 : ¬ (r = idx_m ∧ s = ⟨k.val / 2, by omega⟩) := by rintro ⟨rfl, _⟩; dsimp only [idx_m] at hr; omega
          simp [h1, h2, GaussInt.sub, GaussInt.zero]
    · simp only [b, hk, ↓reduceDIte]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r s; unfold cDiagDiffMat
        by_cases h1 : r = idx_m <;> by_cases h2 : s = idx_m <;>
        by_cases h3 : r = idx₀ <;> by_cases h4 : s = idx₀
        all_goals (ext <;> simp_all [GaussInt.sub, GaussInt.conj, GaussInt.one, GaussInt.zero] <;> omega)
      · unfold cTrRe cDiagDiffMat
        have hs1 : ∀ d : Nat, (p q : Fin d → Int) →
            intSum d (fun r => p r - q r) = intSum d p - intSum d q := by
          intro d p q
          induction d with
          | zero => rfl
          | succ d ih =>
            simp only [intSum]
            rw [ih (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                   (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)]
            omega
        have hc : intSum n (fun r => (GaussInt.sub
            (if r = idx_m ∧ r = idx_m then GaussInt.one else GaussInt.zero)
            (if r = idx₀ ∧ r = idx₀ then GaussInt.one else GaussInt.zero)).re) =
            intSum n (fun r => (if r = idx_m then (1 : Int) else 0) - (if r = idx₀ then 1 else 0)) := by
          have hne : idx_m ≠ idx₀ := by
            intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
          apply intSum_congr; intro r
          by_cases hrm : r = idx_m <;> by_cases hr0 : r = idx₀ <;>
            simp [hrm, hr0, hne, hne.symm, GaussInt.sub, GaussInt.one, GaussInt.zero]
        rw [hc, hs1, intSum_ite_eq, intSum_ite_eq]; omega
      · intro r s hrs; unfold cDiagDiffMat
        have h1 : ¬ (r = idx_m ∧ s = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hrs; omega
        have h2 : ¬ (r = idx₀ ∧ s = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hrs; omega
        simp [h1, h2, GaussInt.sub, GaussInt.zero]
      · intro r s hr _hs h0; unfold cDiagDiffMat
        have h1 : ¬ (r = idx_m ∧ s = idx_m) := by rintro ⟨rfl, _⟩; dsimp only [idx_m] at hr; omega
        have h2 : ¬ (r = idx₀ ∧ s = idx₀) := by rintro ⟨rfl, rfl⟩; simp [idx₀] at h0
        simp [h1, h2, GaussInt.sub, GaussInt.zero]
  · intro c k
    dsimp only [coord]
    unfold ZMod.linComb
    by_cases hk : k.val < 2 * m
    · simp only [hk, ↓reduceDIte]
      let j_k : Fin n := ⟨k.val / 2, by omega⟩
      have hj_ne_m : j_k ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [j_k, idx_m] at hv; omega
      by_cases hmod : k.val % 2 = 0
      · simp only [hmod, ↓reduceIte]
        rw [cMatFinSum_apply, gaussSum_re]
        have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (c r) (b r) j_k idx_m).re) =
            intSum (2 * m + 1) (fun r => if r = k then c r else 0) := by
          apply intSum_congr; intro r
          simp only [cMatRMod, rSmulCMat, b]
          by_cases hr : r.val < 2 * m
          · simp only [hr, ↓reduceDIte]
            have hr_ne_m : (⟨r.val / 2, by omega⟩ : Fin n) ≠ idx_m := by
              intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
            by_cases hrmod : r.val % 2 = 0
            · simp only [hrmod, ↓reduceIte, hermRealPair]
              by_cases hrk : r = k
              · subst hrk; simp [j_k, hj_ne_m, hr_ne_m, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
              · have hne_j : j_k ≠ ⟨r.val / 2, by omega⟩ := by
                  intro hc; have hv := congrArg Fin.val hc; dsimp only [j_k] at hv; apply hrk; ext; omega
                simp [hrk, hne_j, hj_ne_m, hr_ne_m, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, hermImagPair]
              have hrk : r ≠ k := by intro hc; subst hc; exact hrmod hmod
              by_cases hj_eq : j_k = ⟨r.val / 2, by omega⟩ <;>
                simp [hrk, hj_eq, hj_ne_m, hj_ne_m.symm, hr_ne_m, hr_ne_m.symm,
                      GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
          · simp only [hr, ↓reduceDIte, cDiagDiffMat]
            have hrk : r ≠ k := by intro hc; subst hc; exact hr hk
            have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
            simp [hrk, hj_ne_m, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
      · simp only [hmod, ↓reduceIte]
        rw [cMatFinSum_apply, gaussSum_im]
        have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (c r) (b r) j_k idx_m).im) =
            intSum (2 * m + 1) (fun r => if r = k then c r else 0) := by
          apply intSum_congr; intro r
          simp only [cMatRMod, rSmulCMat, b]
          by_cases hr : r.val < 2 * m
          · simp only [hr, ↓reduceDIte]
            have hr_ne_m : (⟨r.val / 2, by omega⟩ : Fin n) ≠ idx_m := by
              intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
            by_cases hrmod : r.val % 2 = 0
            · simp only [hrmod, ↓reduceIte, hermRealPair]
              have hrk : r ≠ k := by intro hc; subst hc; exact hmod hrmod
              by_cases hj_eq : j_k = ⟨r.val / 2, by omega⟩ <;>
                simp [hrk, hj_eq, hj_ne_m, hj_ne_m.symm, hr_ne_m, hr_ne_m.symm,
                      GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, hermImagPair]
              by_cases hrk : r = k
              · subst hrk; simp [j_k, hj_ne_m, hr_ne_m, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
              · have hne_j : j_k ≠ ⟨r.val / 2, by omega⟩ := by
                  intro hc; have hv := congrArg Fin.val hc; dsimp only [j_k] at hv; apply hrk; ext; omega
                simp [hrk, hne_j, hj_ne_m, hr_ne_m, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          · simp only [hr, ↓reduceDIte, cDiagDiffMat]
            have hrk : r ≠ k := by intro hc; subst hc; exact hr hk
            have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
            simp [hrk, hj_ne_m, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
    · simp only [hk, ↓reduceDIte]
      let k_last : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
      have hk_eq : k = k_last := by ext; dsimp only [k_last]; omega
      rw [cMatFinSum_apply, gaussSum_re]
      have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (c r) (b r) idx_m idx_m).re) =
          intSum (2 * m + 1) (fun r => if r = k_last then c r else 0) := by
        apply intSum_congr; intro r
        simp only [cMatRMod, rSmulCMat, b]
        by_cases hr : r.val < 2 * m
        · simp only [hr, ↓reduceDIte]
          have hrk : r ≠ k_last := by intro hc; have hv := congrArg Fin.val hc; dsimp only [k_last] at hv; omega
          have hne : idx_m ≠ ⟨r.val / 2, by omega⟩ := by
            intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
          by_cases hrmod : r.val % 2 = 0 <;>
            simp [hrk, hrmod, hermRealPair, hermImagPair, hne, hne.symm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hr, ↓reduceDIte, cDiagDiffMat]
          have hrk : r = k_last := by ext; dsimp only [k_last]; omega
          have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
          simp [hrk, hm_ne0, hm_ne0.symm, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
      rw [hcong, intSum_ite_eq, hk_eq]
  · intro k
    simp only [coord, cMatRMod, zeroCMat, GaussInt.zero]
    by_cases hk : k.val < 2 * m
    · by_cases hmod : k.val % 2 = 0 <;> simp [hk, hmod]
    · simp [hk]
  · intro B ⟨hherm, htr0, hsup, hinner⟩
    have hdiag_im : ∀ r : Fin n, (B r r).im = 0 := by
      intro r
      have h := congrArg GaussInt.im (hherm r r)
      simp [GaussInt.conj] at h; omega
    have hB00_re : (B idx₀ idx₀).re = - (B idx_m idx_m).re := by
      have htr_calc : cTrRe B = intSum n (fun r =>
          (if r = idx₀ then (B idx₀ idx₀).re else 0) + (if r = idx_m then (B idx_m idx_m).re else 0)) := by
        unfold cTrRe; apply intSum_congr; intro r
        by_cases hr0 : r = idx₀
        · subst hr0
          have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
          simp [hne]
        · by_cases hrm : r = idx_m
          · subst hrm; simp [hr0]
          · simp only [hr0, hrm, ↓reduceIte, Int.add_zero]
            by_cases hlt : r.val < m
            · rw [hinner r r hlt hlt (Or.inl (fun hv => hr0 (Fin.ext hv)))]; rfl
            · have hge : m + 1 ≤ r.val := by
                have hne_v : r.val ≠ m := fun hv => hrm (Fin.ext hv)
                omega
              rw [hsup r r (Or.inl hge)]; rfl
      rw [htr_calc, intSum_add, intSum_ite_eq, intSum_ite_eq] at htr0
      omega
    funext i j
    unfold ZMod.linComb
    rw [cMatFinSum_apply]
    by_cases hhigh : m + 1 ≤ i.val ∨ m + 1 ≤ j.val
    · rw [hsup i j hhigh]
      ext
      · rw [gaussSum_re, intSum_congr (g := fun _ => 0), intSum_zero_fn]; rfl
        intro r; simp only [cMatRMod, rSmulCMat, b]
        by_cases hr : r.val < 2 * m
        · simp only [hr, ↓reduceDIte]
          have h1 : ¬ (i = ⟨r.val / 2, by omega⟩ ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx_m ∧ j = ⟨r.val / 2, by omega⟩) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          by_cases hrmod : r.val % 2 = 0 <;>
            simp [hrmod, hermRealPair, hermImagPair, h1, h2, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hr, ↓reduceDIte, cDiagDiffMat]
          have h1 : ¬ (i = idx_m ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hhigh; omega
          simp [h1, h2, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
      · rw [gaussSum_im, intSum_congr (g := fun _ => 0), intSum_zero_fn]; rfl
        intro r; simp only [cMatRMod, rSmulCMat, b]
        by_cases hr : r.val < 2 * m
        · simp only [hr, ↓reduceDIte]
          have h1 : ¬ (i = ⟨r.val / 2, by omega⟩ ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx_m ∧ j = ⟨r.val / 2, by omega⟩) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          by_cases hrmod : r.val % 2 = 0 <;>
            simp [hrmod, hermRealPair, hermImagPair, h1, h2, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hr, ↓reduceDIte, cDiagDiffMat]
          have h1 : ¬ (i = idx_m ∧ j = idx_m) := by rintro ⟨rfl, rfl⟩; dsimp only [idx_m] at hhigh; omega
          have h2 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hhigh; omega
          simp [h1, h2, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
    · by_cases him : i = idx_m
      · subst him
        by_cases hjm : j = idx_m
        · subst hjm
          let k_last : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
          ext
          · rw [gaussSum_re]
            have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) idx_m idx_m).re) =
                intSum (2 * m + 1) (fun r => if r = k_last then (B idx_m idx_m).re else 0) := by
              apply intSum_congr; intro r
              simp only [cMatRMod, rSmulCMat, b, coord]
              by_cases hr : r.val < 2 * m
              · have hrk : r ≠ k_last := by intro hc; have hv := congrArg Fin.val hc; dsimp only [k_last] at hv; omega
                have hne : idx_m ≠ ⟨r.val / 2, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0 <;>
                  simp [hr, hrk, hrmod, hermRealPair, hermImagPair, hne, hne.symm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · have hrk : r = k_last := by ext; dsimp only [k_last]; omega
                have hne : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
                simp [k_last, hr, hrk, cDiagDiffMat, hne, hne.symm, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
            rw [hcong, intSum_ite_eq]
          · rw [hdiag_im idx_m, gaussSum_im, intSum_congr (g := fun _ => 0), intSum_zero_fn]
            intro r; simp only [cMatRMod, rSmulCMat, b]
            by_cases hr : r.val < 2 * m
            · have hne : idx_m ≠ ⟨r.val / 2, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
              by_cases hrmod : r.val % 2 = 0 <;>
                simp [hr, hrmod, hermRealPair, hermImagPair, hne, hne.symm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · have hne : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
              simp [hr, cDiagDiffMat, hne, hne.symm, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
        · have hj_lt : j.val < m := by
            have hj_ne : j.val ≠ m := fun hv => hjm (Fin.ext hv)
            omega
          let k_re : Fin (2 * m + 1) := ⟨2 * j.val, by omega⟩
          let k_im : Fin (2 * m + 1) := ⟨2 * j.val + 1, by omega⟩
          have hconj_mj := hherm j idx_m
          ext
          · rw [hconj_mj, gaussSum_re]
            simp only [GaussInt.conj]
            have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) idx_m j).re) =
                intSum (2 * m + 1) (fun r => if r = k_re then (B j idx_m).re else 0) := by
              apply intSum_congr; intro r
              simp only [cMatRMod, rSmulCMat, b, coord]
              by_cases hr : r.val < 2 * m
              · simp only [hr, ↓reduceDIte]
                have hm_ner : idx_m ≠ ⟨r.val / 2, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0
                · simp only [hrmod, ↓reduceIte, hermRealPair]
                  by_cases hrk : r = k_re
                  · subst hrk
                    have hj_eq : (⟨(2 * j.val) / 2, by omega⟩ : Fin n) = j := by ext; simp
                    simp [k_re, hm_ner, hm_ner.symm, hjm, Ne.symm hjm, hj_eq, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
                  · have hj_ne : j ≠ ⟨r.val / 2, by omega⟩ := by
                      intro hc; have hv := congrArg Fin.val hc; simp at hv; apply hrk; ext; dsimp only [k_re]; omega
                    simp [hrk, hm_ner, hm_ner.symm, hj_ne, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
                · simp only [hrmod, ↓reduceIte, hermImagPair]
                  have hrk : r ≠ k_re := by intro hc; subst hc; simp [k_re] at hrmod
                  by_cases hj_eq : j = ⟨r.val / 2, by omega⟩ <;>
                    simp [hrk, hm_ner, hm_ner.symm, hjm, Ne.symm hjm, hj_eq, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
              · have hrk : r ≠ k_re := by intro hc; subst hc; dsimp only [k_re] at hr; omega
                have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
                simp [hr, hrk, cDiagDiffMat, hjm, Ne.symm hjm, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            rw [hcong, intSum_ite_eq]
          · rw [hconj_mj, gaussSum_im]
            simp only [GaussInt.conj]
            have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) idx_m j).im) =
                intSum (2 * m + 1) (fun r => if r = k_im then - (B j idx_m).im else 0) := by
              apply intSum_congr; intro r
              simp only [cMatRMod, rSmulCMat, b, coord]
              by_cases hr : r.val < 2 * m
              · simp only [hr, ↓reduceDIte]
                have hm_ner : idx_m ≠ ⟨r.val / 2, by omega⟩ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0
                · simp only [hrmod, ↓reduceIte, hermRealPair]
                  have hrk : r ≠ k_im := by intro hc; subst hc; simp [k_im] at hrmod
                  by_cases hj_eq : j = ⟨r.val / 2, by omega⟩ <;>
                    simp [hrk, hm_ner, hm_ner.symm, hjm, Ne.symm hjm, hj_eq, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
                · simp only [hrmod, ↓reduceIte, hermImagPair]
                  by_cases hrk : r = k_im
                  · subst hrk
                    have hj_eq : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := by ext; simp; omega
                    simp [k_im, hm_ner, hm_ner.symm, hjm, Ne.symm hjm, hj_eq, Int.mul_neg, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
                  · have hj_ne : j ≠ ⟨r.val / 2, by omega⟩ := by
                      intro hc; have hv := congrArg Fin.val hc; simp at hv; apply hrk; ext; dsimp only [k_im]; omega
                    simp [hrk, hm_ner, hm_ner.symm, hj_ne, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · have hrk : r ≠ k_im := by intro hc; subst hc; dsimp only [k_im] at hr; omega
                have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
                simp [hr, hrk, cDiagDiffMat, hjm, Ne.symm hjm, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            rw [hcong, intSum_ite_eq]
      · have hi_lt : i.val < m := by
          have hi_ne : i.val ≠ m := fun hv => him (Fin.ext hv)
          omega
        by_cases hjm : j = idx_m
        · subst hjm
          let k_re : Fin (2 * m + 1) := ⟨2 * i.val, by omega⟩
          let k_im : Fin (2 * m + 1) := ⟨2 * i.val + 1, by omega⟩
          ext
          · rw [gaussSum_re]
            have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) i idx_m).re) =
                intSum (2 * m + 1) (fun r => if r = k_re then (B i idx_m).re else 0) := by
              apply intSum_congr; intro r
              simp only [cMatRMod, rSmulCMat, b, coord]
              by_cases hr : r.val < 2 * m
              · simp only [hr, ↓reduceDIte]
                have hr_ne_m : (⟨r.val / 2, by omega⟩ : Fin n) ≠ idx_m := by
                  intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0
                · simp only [hrmod, ↓reduceIte, hermRealPair]
                  by_cases hrk : r = k_re
                  · subst hrk
                    have hi_eq : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i := by ext; simp
                    simp [k_re, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_eq, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
                  · have hi_ne : i ≠ ⟨r.val / 2, by omega⟩ := by
                      intro hc; have hv := congrArg Fin.val hc; simp at hv; apply hrk; ext; dsimp only [k_re]; omega
                    simp [hrk, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_ne, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
                · simp only [hrmod, ↓reduceIte, hermImagPair]
                  have hrk : r ≠ k_re := by intro hc; subst hc; simp [k_re] at hrmod
                  by_cases hi_eq : i = ⟨r.val / 2, by omega⟩ <;>
                    simp [hrk, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_eq, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
              · have hrk : r ≠ k_re := by intro hc; subst hc; dsimp only [k_re] at hr; omega
                have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
                simp [hr, hrk, cDiagDiffMat, him, Ne.symm him, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            rw [hcong, intSum_ite_eq]
          · rw [gaussSum_im]
            have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) i idx_m).im) =
                intSum (2 * m + 1) (fun r => if r = k_im then (B i idx_m).im else 0) := by
              apply intSum_congr; intro r
              simp only [cMatRMod, rSmulCMat, b, coord]
              by_cases hr : r.val < 2 * m
              · simp only [hr, ↓reduceDIte]
                have hr_ne_m : (⟨r.val / 2, by omega⟩ : Fin n) ≠ idx_m := by
                  intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0
                · simp only [hrmod, ↓reduceIte, hermRealPair]
                  have hrk : r ≠ k_im := by intro hc; subst hc; simp [k_im] at hrmod
                  by_cases hi_eq : i = ⟨r.val / 2, by omega⟩ <;>
                    simp [hrk, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_eq, GaussInt.add, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
                · simp only [hrmod, ↓reduceIte, hermImagPair]
                  by_cases hrk : r = k_im
                  · subst hrk
                    have hi_eq : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := by ext; simp; omega
                    simp [k_im, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_eq, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
                  · have hi_ne : i ≠ ⟨r.val / 2, by omega⟩ := by
                      intro hc; have hv := congrArg Fin.val hc; simp at hv; apply hrk; ext; dsimp only [k_im]; omega
                    simp [hrk, him, Ne.symm him, hr_ne_m, hr_ne_m.symm, hi_ne, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · have hrk : r ≠ k_im := by intro hc; subst hc; dsimp only [k_im] at hr; omega
                have hm_ne0 : idx_m ≠ idx₀ := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx_m, idx₀] at hv; omega
                simp [hr, hrk, cDiagDiffMat, him, Ne.symm him, hm_ne0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            rw [hcong, intSum_ite_eq]
        · have hj_lt : j.val < m := by
            have hj_ne : j.val ≠ m := fun hv => hjm (Fin.ext hv)
            omega
          by_cases hij0 : i = idx₀ ∧ j = idx₀
          · rcases hij0 with ⟨rfl, rfl⟩
            let k_last : Fin (2 * m + 1) := ⟨2 * m, by omega⟩
            ext
            · rw [hB00_re, gaussSum_re]
              have hcong : intSum (2 * m + 1) (fun r => ((cMatRMod n).smul (coord B r) (b r) idx₀ idx₀).re) =
                  intSum (2 * m + 1) (fun r => if r = k_last then - (B idx_m idx_m).re else 0) := by
                apply intSum_congr; intro r
                simp only [cMatRMod, rSmulCMat, b, coord]
                by_cases hr : r.val < 2 * m
                · have hrk : r ≠ k_last := by intro hc; have hv := congrArg Fin.val hc; dsimp only [k_last] at hv; omega
                  have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                  by_cases hrmod : r.val % 2 = 0 <;>
                    simp [hr, hrk, hrmod, hermRealPair, hermImagPair, hne, hne.symm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
                · have hrk : r = k_last := by ext; dsimp only [k_last]; omega
                  have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                  simp [k_last, hr, hrk, cDiagDiffMat, hne, hne.symm, Int.mul_neg, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
              rw [hcong, intSum_ite_eq]
            · rw [hdiag_im idx₀, gaussSum_im, intSum_congr (g := fun _ => 0), intSum_zero_fn]
              intro r; simp only [cMatRMod, rSmulCMat, b]
              by_cases hr : r.val < 2 * m
              · have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                by_cases hrmod : r.val % 2 = 0 <;>
                  simp [hr, hrmod, hermRealPair, hermImagPair, hne, hne.symm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · have hne : idx₀ ≠ idx_m := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_m] at hv; omega
                simp [hr, cDiagDiffMat, hne, hne.symm, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
          · have hnz0 : i.val ≠ 0 ∨ j.val ≠ 0 := by
              by_cases hi0 : i.val = 0
              · right; intro hj0; exact hij0 ⟨Fin.ext hi0, Fin.ext hj0⟩
              · left; exact hi0
            rw [hinner i j hi_lt hj_lt hnz0]
            ext
            · rw [gaussSum_re, intSum_congr (g := fun _ => 0), intSum_zero_fn]; rfl
              intro r; simp only [cMatRMod, rSmulCMat, b]
              by_cases hr : r.val < 2 * m
              · by_cases hrmod : r.val % 2 = 0 <;>
                  simp [hr, hrmod, hermRealPair, hermImagPair, him, hjm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · simp [hr, cDiagDiffMat, him, hij0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · rw [gaussSum_im, intSum_congr (g := fun _ => 0), intSum_zero_fn]; rfl
              intro r; simp only [cMatRMod, rSmulCMat, b]
              by_cases hr : r.val < 2 * m
              · by_cases hrmod : r.val % 2 = 0 <;>
                  simp [hr, hrmod, hermRealPair, hermImagPair, him, hjm, GaussInt.add, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · simp [hr, cDiagDiffMat, him, hij0, GaussInt.sub, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]

/-- Exact real dimension of `TracelessHermBlock n m`: `m² - 1` for ALL `1 ≤ m ≤ n`. -/
theorem tracelessHermBlock_hasDim {n m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ZMod.HasDim (cMatRMod n) (TracelessHermBlock n m) (m * m - 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.zero_add]
      let b : Fin 0 → CMat n := Fin.elim0
      refine ⟨b, fun i => Fin.elim0 i, fun c _ i => Fin.elim0 i, ?_⟩
      intro H ⟨hherm, htr0, hsup⟩
      let z0 : Fin n := ⟨0, by omega⟩
      refine ⟨Fin.elim0, ?_⟩
      funext i j
      simp only [ZMod.linComb, ZMod.finSum, cMatRMod, zeroCMat]
      by_cases hi0 : i.val = 0
      · by_cases hj0 : j.val = 0
        · have hi_eq : i = z0 := Fin.ext hi0
          have hj_eq : j = z0 := Fin.ext hj0
          have htr_calc : cTrRe H = intSum n (fun r => if r = z0 then (H z0 z0).re else 0) := by
            unfold cTrRe; apply intSum_congr; intro r
            by_cases hr : r = z0
            · subst hr; simp
            · have hge : 1 ≤ r.val := by
                by_cases hrz : r.val = 0
                · exact absurd (Fin.ext hrz) hr
                · omega
              rw [hsup r r (Or.inl hge)]; simp [hr, GaussInt.zero]
          rw [htr_calc, intSum_ite_eq] at htr0
          have him0 := congrArg GaussInt.im (hherm z0 z0)
          simp [GaussInt.conj] at him0
          have hH00 : H z0 z0 = GaussInt.zero := by
            ext <;> simp [GaussInt.zero] <;> omega
          exact hi_eq ▸ hj_eq ▸ hH00
        · exact hsup i j (Or.inr (by omega))
      · exact hsup i j (Or.inl (by omega))
    · have hk1 : 1 ≤ k := by omega
      have hkn : k ≤ n := by omega
      have hd_ih := ih hk1 hkn
      have hd_b := hermBorder_hasDim hk1 hmn
      have harith : (k * k - 1) + (2 * k + 1) = (k + 1) * (k + 1) - 1 := by
        have hpos : 1 ≤ k * k := Nat.mul_le_mul hk1 hk1
        have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
          calc (k + 1) * (k + 1)
              = k * (k + 1) + 1 * (k + 1) := Nat.add_mul k 1 (k + 1)
            _ = k * k + k * 1 + (k + 1) := by rw [Nat.mul_add k k 1, Nat.one_mul]
            _ = k * k + 2 * k + 1 := by omega
        omega
      rw [← harith]
      apply ZMod.hasDim_directSum (cMatRMod n) hd_ih hd_b
      · intro v ⟨hh, ht, hsp⟩ c
        refine ⟨fun i j => by ext <;> (have hij := hh i j; simp [cMatRMod, rSmulCMat, hij, GaussInt.conj, GaussInt.mul, GaussInt.ofInt, Int.mul_neg]),
                ?_,
                fun i j hij => by simp [cMatRMod, rSmulCMat, hsp i j hij, GaussInt.mul_zero]⟩
        unfold cTrRe; simp only [cMatRMod, rSmulCMat, GaussInt.mul, GaussInt.ofInt]
        have hc : intSum n (fun i => c * (v i i).re - 0 * (v i i).im) = c * cTrRe v := by
          unfold cTrRe; rw [← intSum_mul_left]; apply intSum_congr; intro i; omega
        rw [hc, ht]; simp
      · intro v ⟨hh, ht, hsp, hin⟩ c
        refine ⟨fun i j => by ext <;> (have hij := hh i j; simp [cMatRMod, rSmulCMat, hij, GaussInt.conj, GaussInt.mul, GaussInt.ofInt, Int.mul_neg]),
                ?_,
                fun i j hij => by simp [cMatRMod, rSmulCMat, hsp i j hij, GaussInt.mul_zero],
                fun i j hi hj h0 => by simp [cMatRMod, rSmulCMat, hin i j hi hj h0, GaussInt.mul_zero]⟩
        unfold cTrRe; simp only [cMatRMod, rSmulCMat, GaussInt.mul, GaussInt.ofInt]
        have hc : intSum n (fun i => c * (v i i).re - 0 * (v i i).im) = c * cTrRe v := by
          unfold cTrRe; rw [← intSum_mul_left]; apply intSum_congr; intro i; omega
        rw [hc, ht]; simp
      · intro u v ⟨hhu, htu, hspu⟩ ⟨hhv, htv, hspv⟩
        refine ⟨fun i j => by simp [cMatRMod, addCMat, hhu i j, hhv i j, GaussInt.conj_add],
                ?_,
                fun i j hij => by simp [cMatRMod, addCMat, hspu i j hij, hspv i j hij, GaussInt.add_zero]⟩
        unfold cTrRe; simp only [cMatRMod, addCMat, GaussInt.add]
        rw [intSum_add]; change cTrRe u + cTrRe v = 0; omega
      · intro u v ⟨hhu, htu, hspu, hinu⟩ ⟨hhv, htv, hspv, hinv⟩
        refine ⟨fun i j => by simp [cMatRMod, addCMat, hhu i j, hhv i j, GaussInt.conj_add],
                ?_,
                fun i j hij => by simp [cMatRMod, addCMat, hspu i j hij, hspv i j hij, GaussInt.add_zero],
                fun i j hi hj h0 => by simp [cMatRMod, addCMat, hinu i j hi hj h0, hinv i j hi hj h0, GaussInt.add_zero]⟩
        unfold cTrRe; simp only [cMatRMod, addCMat, GaussInt.add]
        rw [intSum_add]; change cTrRe u + cTrRe v = 0; omega
      · refine ⟨fun _ _ => by rfl, ?_, fun _ _ _ => rfl⟩
        unfold cTrRe; simp [cMatRMod, zeroCMat, GaussInt.zero, intSum_zero_fn]
      · refine ⟨fun _ _ => by rfl, ?_, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
        unfold cTrRe; simp [cMatRMod, zeroCMat, GaussInt.zero, intSum_zero_fn]
      · intro v ⟨hh, ht, hsp⟩
        exact ⟨hh, ht, fun i j hij => hsp i j (by omega)⟩
      · intro v ⟨hh, ht, hsp, _⟩
        exact ⟨hh, ht, hsp⟩
      · intro u v ⟨hhu, htu, hspu⟩ ⟨hhv, htv, hspv⟩
        refine ⟨fun i j => by simp [cMatRMod, addCMat, hhu i j, hhv i j, GaussInt.conj_add],
                ?_,
                fun i j hij => by simp [cMatRMod, addCMat, hspu i j hij, hspv i j hij, GaussInt.add_zero]⟩
        unfold cTrRe; simp only [cMatRMod, addCMat, GaussInt.add]
        rw [intSum_add]; change cTrRe u + cTrRe v = 0; omega
      · intro H ⟨hhH, htH, hspH⟩
        let idx₀ : Fin n := ⟨0, by omega⟩
        let idx_k : Fin n := ⟨k, hmn⟩
        let B : CMat n := fun i j =>
          if i = idx₀ ∧ j = idx₀ then GaussInt.neg (H idx_k idx_k)
          else if i.val = k ∨ j.val = k then H i j
          else GaussInt.zero
        let P : CMat n := subCMat H B
        have hkk_im : (H idx_k idx_k).im = 0 := by
          have h := congrArg GaussInt.im (hhH idx_k idx_k); simp [GaussInt.conj] at h; omega
        have hB_mem : HermBorder n k hmn B := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i j; simp only [B]
            by_cases h0 : i = idx₀ ∧ j = idx₀
            · rcases h0 with ⟨rfl, rfl⟩; ext <;> simp [GaussInt.neg, GaussInt.conj, hkk_im]
            · have h0' : ¬ (j = idx₀ ∧ i = idx₀) := fun ⟨hj, hi⟩ => h0 ⟨hi, hj⟩
              simp only [h0, h0', ↓reduceIte]
              by_cases hkv : i.val = k ∨ j.val = k
              · have hkv' : j.val = k ∨ i.val = k := hkv.symm
                simp [hkv, hkv', hhH i j]
              · have hkv' : ¬ (j.val = k ∨ i.val = k) := fun h => hkv h.symm
                simp [hkv, hkv', GaussInt.conj, GaussInt.zero]
          · have htrB : cTrRe B = intSum n (fun r =>
                (if r = idx₀ then - (H idx_k idx_k).re else 0) +
                (if r = idx_k then (H idx_k idx_k).re else 0)) := by
              unfold cTrRe; apply intSum_congr; intro r; simp only [B]
              by_cases hr0 : r = idx₀
              · subst hr0
                have hne : idx₀ ≠ idx_k := by intro hc; have hv := congrArg Fin.val hc; dsimp only [idx₀, idx_k] at hv; omega
                simp [hne, GaussInt.neg]
              · by_cases hrk : r = idx_k
                · subst hrk; simp [hr0, idx_k]
                · have hrkv : r.val ≠ k := fun hv => hrk (Fin.ext hv)
                  simp [hr0, hrk, hrkv, GaussInt.zero]
            rw [htrB, intSum_add, intSum_ite_eq, intSum_ite_eq]; omega
          · intro i j hij; simp only [B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hij; omega
            simp only [h0, ↓reduceIte]
            by_cases hkv : i.val = k ∨ j.val = k
            · simp [hkv, hspH i j hij]
            · simp [hkv]
          · intro i j _hi _hj hnz; simp only [B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; simp [idx₀] at hnz
            have hkv : ¬ (i.val = k ∨ j.val = k) := by omega
            simp [h0, hkv]
        have hP_mem : TracelessHermBlock n k P := by
          refine ⟨?_, ?_, ?_⟩
          · intro i j
            ext <;> (have h1 := hhH i j; have h2 := hB_mem.1 i j;
                     simp [P, subCMat, h1, h2, GaussInt.sub, GaussInt.conj] <;> omega)
          · have hs1 : ∀ d : Nat, (p q : Fin d → Int) →
                intSum d (fun r => p r - q r) = intSum d p - intSum d q := by
              intro d p q
              induction d with
              | zero => rfl
              | succ d ih2 =>
                simp only [intSum]
                rw [ih2 (fun r => p ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)
                        (fun r => q ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩)]
                omega
            unfold cTrRe P subCMat
            simp only [GaussInt.sub]
            rw [hs1]; change cTrRe H - cTrRe B = 0; rw [htH, hB_mem.2.1]; rfl
          · intro i j hij; simp only [P, subCMat, B]
            have h0 : ¬ (i = idx₀ ∧ j = idx₀) := by rintro ⟨rfl, rfl⟩; dsimp only [idx₀] at hij; omega
            simp only [h0, ↓reduceIte]
            by_cases hkv : i.val = k ∨ j.val = k
            · ext <;> simp [hkv, GaussInt.sub, GaussInt.zero]
            · have hge1 : k + 1 ≤ i.val ∨ k + 1 ≤ j.val := by omega
              ext <;> simp [hkv, hspH i j hge1, GaussInt.sub, GaussInt.zero]
        refine ⟨P, B, hP_mem, hB_mem, ?_⟩
        funext i j; ext <;> simp [cMatRMod, addCMat, P, subCMat, GaussInt.add, GaussInt.sub] <;> omega
      · intro P B ⟨hhP, htP, hspP⟩ ⟨_hhB, _htB, hspB, hinB⟩ hsum0
        let z0 : Fin n := ⟨0, by omega⟩
        have hPB : ∀ i j, GaussInt.add (P i j) (B i j) = GaussInt.zero :=
          fun i j => congrFun (congrFun hsum0 i) j
        have hB_zero : ∀ i j, B i j = GaussInt.zero := by
          intro i j
          by_cases hhigh : k + 1 ≤ i.val ∨ k + 1 ≤ j.val
          · exact hspB i j hhigh
          · by_cases hbord : k ≤ i.val ∨ k ≤ j.val
            · have hP0 := hspP i j hbord
              have h := hPB i j; rw [hP0, GaussInt.zero_add] at h; exact h
            · by_cases hij0 : i.val = 0 ∧ j.val = 0
              · have hP_other : ∀ r : Fin n, r.val ≠ 0 → (P r r).re = 0 := by
                  intro r hr0
                  by_cases hrk : r.val < k
                  · have hBr := hinB r r hrk hrk (Or.inl hr0)
                    have h := congrArg GaussInt.re (hPB r r)
                    rw [hBr] at h; simp [GaussInt.add, GaussInt.zero] at h; exact h
                  · rw [hspP r r (Or.inl (by omega))]; rfl
                have htrP_calc : cTrRe P = intSum n (fun r => if r = z0 then (P z0 z0).re else 0) := by
                  unfold cTrRe; apply intSum_congr; intro r
                  by_cases hr : r = z0
                  · subst hr; simp
                  · rw [hP_other r (fun hv => hr (Fin.ext hv))]; simp [hr]
                rw [htrP_calc, intSum_ite_eq] at htP
                have himP0 := congrArg GaussInt.im (hhP z0 z0)
                simp [GaussInt.conj] at himP0
                have hP00 : P z0 z0 = GaussInt.zero := by
                  ext <;> simp [GaussInt.zero] <;> omega
                have hB00 : B z0 z0 = GaussInt.zero := by
                  have h := hPB z0 z0; rw [hP00, GaussInt.zero_add] at h; exact h
                have hi_eq : i = z0 := Fin.ext hij0.1
                have hj_eq : j = z0 := Fin.ext hij0.2
                exact hi_eq ▸ hj_eq ▸ hB00
              · exact hinB i j (by omega) (by omega) (by omega)
        have hB_eq : B = zeroCMat n := by funext i j; exact hB_zero i j
        have hP_eq : P = zeroCMat n := by
          funext i j
          have h := hPB i j
          rw [hB_zero i j, GaussInt.add_zero] at h
          exact h
        exact ⟨hP_eq, hB_eq⟩

/-- Universal arithmetic refutation for complex density matrices: `m² - 1 ≠ m` for EVERY `m ≥ 1`! -/
theorem complex_density_dim_ne_m {m : Nat} (hm1 : 1 ≤ m) : m * m - 1 ≠ m := by
  by_cases hm_eq1 : m = 1
  · subst hm_eq1; decide
  · have hm2 : 2 ≤ m := by omega
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m hm2
    omega

theorem tracelessHermBlock_not_hasDim_m {n m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ¬ ZMod.HasDim (cMatRMod n) (TracelessHermBlock n m) m :=
  ZMod.not_hasDim_of_ne (cMatRMod n) (tracelessHermBlock_hasDim hm1 hmn) (complex_density_dim_ne_m hm1)

/-! ## 4. Structural Obstructions Beyond Extremal Hermitian Eigenvalues -/

/-- Obstruction 6A: Non-normal matrix `A = [[0, 2], [0, 0]]`. -/
def nonNormalA : Mat 2 := fun i j => if i.val = 0 ∧ j.val = 1 then 2 else 0

def charPoly2 (A : Mat 2) (mu : Int) : Int :=
  (mu - A ⟨0, by omega⟩ ⟨0, by omega⟩) * (mu - A ⟨1, by omega⟩ ⟨1, by omega⟩) -
    A ⟨0, by omega⟩ ⟨1, by omega⟩ * A ⟨1, by omega⟩ ⟨0, by omega⟩

def diagVec11 : Vec 2 := fun _ => 1

theorem diagVec11_ne_zero : diagVec11 ≠ zeroVec 2 := by
  intro h; have h0 := congrFun h ⟨0, by omega⟩; simp [diagVec11, zeroVec] at h0

/-- For `nonNormalA = [[0, 2], [0, 0]]`:
    1. `χ_A(μ) = μ²` (unique eigenvalue `0` of algebraic multiplicity `2`);
    2. `max R_A = 1 ≠ 0` is attained at `(1, 1)ᵀ`;
    3. `R_A(x) = 1 ↔ ProjEquiv x (1, 1)ᵀ` (singleton ray of projective dimension `0 ≠ 2` and `0 ≠ 1`). -/
theorem nonNormal_counterexample :
    (∀ mu : Int, charPoly2 nonNormalA mu = mu * mu) ∧
    RatVal.Eq (rayleigh nonNormalA diagVec11 diagVec11_ne_zero) (RatVal.ofInt 1) ∧
    (∀ (x : Vec 2) (hx : x ≠ zeroVec 2),
      RatVal.Le (rayleigh nonNormalA x hx) (RatVal.ofInt 1) ∧
      (RatVal.Eq (rayleigh nonNormalA x hx) (RatVal.ofInt 1) ↔ ProjEquiv x diagVec11)) := by
  have hquad_nn : ∀ x : Vec 2,
      dot x (matVec nonNormalA x) = 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := by
    intro x
    change (0 + x ⟨0, by omega⟩ * ((0 + 0 * x ⟨0, by omega⟩) + 2 * x ⟨1, by omega⟩)) +
        x ⟨1, by omega⟩ * ((0 + 0 * x ⟨0, by omega⟩) + 0 * x ⟨1, by omega⟩) =
        2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩
    simp only [Int.zero_mul, Int.zero_add, Int.add_zero, Int.mul_zero]
    rw [← Int.mul_assoc (x ⟨0, by omega⟩) 2 (x ⟨1, by omega⟩), Int.mul_comm (x ⟨0, by omega⟩) 2]
  have hnorm2 : ∀ x : Vec 2,
      normSq x = x ⟨0, by omega⟩ * x ⟨0, by omega⟩ + x ⟨1, by omega⟩ * x ⟨1, by omega⟩ := by
    intro x
    change (0 + x ⟨0, by omega⟩ * x ⟨0, by omega⟩) + x ⟨1, by omega⟩ * x ⟨1, by omega⟩ = _
    rw [Int.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · intro mu
    change (mu - 0) * (mu - 0) - 2 * 0 = mu * mu
    simp only [Int.sub_zero, Int.mul_zero]
  · dsimp only [RatVal.Eq, rayleigh, RatVal.ofInt]
    rw [hquad_nn, hnorm2]
    rfl
  · intro x hx
    dsimp only [RatVal.Le, RatVal.Eq, rayleigh, RatVal.ofInt]
    simp only [Int.mul_one, Int.one_mul]
    rw [hquad_nn, hnorm2]
    have hdiff : x ⟨0, by omega⟩ * x ⟨0, by omega⟩ + x ⟨1, by omega⟩ * x ⟨1, by omega⟩ -
        2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ =
        (x ⟨0, by omega⟩ - x ⟨1, by omega⟩) * (x ⟨0, by omega⟩ - x ⟨1, by omega⟩) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (x ⟨1, by omega⟩) (x ⟨0, by omega⟩)]
      have h2 : 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ =
          x ⟨0, by omega⟩ * x ⟨1, by omega⟩ + x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := by
        have h2a : (2 : Int) * x ⟨0, by omega⟩ = x ⟨0, by omega⟩ + x ⟨0, by omega⟩ := by omega
        rw [h2a, Int.add_mul]
      omega
    have hsq_nn := int_sq_nonneg (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)
    refine ⟨by omega, ?_⟩
    constructor
    · intro heq
      have hsq0 : (x ⟨0, by omega⟩ - x ⟨1, by omega⟩) * (x ⟨0, by omega⟩ - x ⟨1, by omega⟩) = 0 := by omega
      have hab : x ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by
        have := (int_sq_eq_zero_iff (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)).mp hsq0
        omega
      have ha_ne : x ⟨0, by omega⟩ ≠ 0 := by
        intro ha0
        apply hx
        funext i
        match i with
        | ⟨0, _⟩ => exact ha0
        | ⟨1, _⟩ => change x ⟨1, by omega⟩ = 0; omega
      refine ⟨1, x ⟨0, by omega⟩, by omega, ha_ne, ?_⟩
      funext i
      match i with
      | ⟨0, _⟩ => change 1 * x ⟨0, by omega⟩ = x ⟨0, by omega⟩ * 1; omega
      | ⟨1, _⟩ => change 1 * x ⟨1, by omega⟩ = x ⟨0, by omega⟩ * 1; omega
    · rintro ⟨c₁, c₂, hc₁, _hc₂, hsc⟩
      have h0 : c₁ * x ⟨0, by omega⟩ = c₂ * 1 := congrFun hsc ⟨0, by omega⟩
      have h1 : c₁ * x ⟨1, by omega⟩ = c₂ * 1 := congrFun hsc ⟨1, by omega⟩
      have hc_eq : c₁ * x ⟨0, by omega⟩ = c₁ * x ⟨1, by omega⟩ := by omega
      have hab : x ⟨0, by omega⟩ = x ⟨1, by omega⟩ := Int.eq_of_mul_eq_mul_left hc₁ hc_eq
      rw [hab]
      have h2 : (2 : Int) * x ⟨1, by omega⟩ = x ⟨1, by omega⟩ + x ⟨1, by omega⟩ := by omega
      rw [h2, Int.add_mul]

/-- Obstruction 6B: Joint Rayleigh quotient `A₁ = diag(1,1,0,0)`, `A₂ = diag(0,0,1,0)` with 1D extremal face. -/
def jointEigs1 : Fin 4 → Int := fun i => if i.val < 2 then 1 else 0
def jointEigs2 : Fin 4 → Int := fun i => if i.val = 2 then 1 else 0
def jointSupportEigs : Fin 4 → Int := fun i => if i.val < 3 then 1 else 0

theorem joint_extremal_face_obstruction :
    HasMaxMult jointSupportEigs 1 3 ∧
    HasMaxMult jointEigs1 1 2 ∧
    ¬ ZMod.HasDim (vecZMod 4) (TangentRealSphere (diagMat jointSupportEigs) 1 (stdBasis 4 ⟨0, by omega⟩)) 3 ∧
    ¬ ZMod.HasDim (cVecRMod 4) (TangentComplexSphere (cDiagMat jointSupportEigs) 1 (cStdBasis 4 ⟨0, by omega⟩)) 3 ∧
    ¬ CMod.HasCDim (cVecCMod 4) (TangentComplexProj (cDiagMat jointSupportEigs) 1 (cStdBasis 4 ⟨0, by omega⟩)) 3 ∧
    ¬ ZMod.HasDim (cVecRMod 4) (TangentComplexProj (cDiagMat jointSupportEigs) 1 (cStdBasis 4 ⟨0, by omega⟩)) 3 ∧
    ¬ ZMod.HasDim (cMatRMod 4) (TracelessHermBlock 4 3) 3 ∧
    ¬ ZMod.HasDim (matZMod 4) (TracelessSymBlock 4 3) 3 := by
  have hsup3 : HasMaxMult jointSupportEigs 1 3 := by
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro i hi; simp [jointSupportEigs, hi]
    · intro i hi; have : ¬ (i.val < 3) := by omega
      simp [jointSupportEigs, this]
  have heig1 : HasMaxMult jointEigs1 1 2 := by
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro i hi; simp [jointEigs1, hi]
    · intro i hi; have : ¬ (i.val < 2) := by omega
      simp [jointEigs1, this]
  exact ⟨hsup3, heig1,
         tangentRealSphere_not_hasDim_m hsup3,
         tangentComplexSphere_not_hasDim_m hsup3 (by omega),
         tangentComplexProj_not_hasCDim_m hsup3,
         tangentComplexProj_not_hasRDim_m hsup3 (by omega),
         tracelessHermBlock_not_hasDim_m (by omega) (by omega),
         tracelessSymBlock_not_hasDim_m (by omega) (by omega) (by omega)⟩

/-- Obstruction 6C: Interior eigenvalue singularity for `A = diag(1, 0, -1)` on `S²`. -/
def interiorEigs3 : Fin 3 → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => -1

def interiorA3 : Mat 3 := diagMat interiorEigs3

def pSing3 : Vec 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

def qReg3 : Vec 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2

/-- Zariski tangent space to `{x ∈ S² : R_{interiorA3}(x) = 0}` at `x`:
    `⟨x, v⟩ = 0` and `⟨A x, v⟩ = 0`. -/
def InteriorLevelZariski (p v : Vec 3) : Prop :=
  dot p v = 0 ∧ dot (matVec interiorA3 p) v = 0

/-- At interior eigenvalue `λ₂ = 0` (multiplicity `m = 1`), the Zariski tangent space of
    `S² ∩ R_A⁻¹(0)` has dimension `2` at `pSing3 = (0, 1, 0)` and dimension `1` at the
    rational unit point `(1/3) qReg3 = (2/3, 1/3, 2/3)`, proving `S² ∩ R_A⁻¹(0)` is singular! -/
theorem interior_eigenvalue_level_set_singular :
    ZMod.HasDim (vecZMod 3) (RealEigenspace interiorA3 0) 1 ∧
    dot pSing3 (matVec interiorA3 pSing3) = 0 ∧
    dot qReg3 (matVec interiorA3 qReg3) = 0 ∧
    ZMod.HasDim (vecZMod 3) (InteriorLevelZariski pSing3) 2 ∧
    ZMod.HasDim (vecZMod 3) (InteriorLevelZariski qReg3) 1 ∧
    ¬ ZMod.HasDim (vecZMod 3) (InteriorLevelZariski pSing3) 1 := by
  have heig_dim : ZMod.HasDim (vecZMod 3) (RealEigenspace interiorA3 0) 1 := by
    let b : Fin 1 → Vec 3 := fun _ => stdBasis 3 ⟨1, by omega⟩
    let coord : Vec 3 → Fin 1 → Int := fun v _ => v ⟨1, by omega⟩
    apply ZMod.hasDim_of_coords (vecZMod 3) b coord
    · intro _; funext i
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    · intro c k
      match k with
      | ⟨0, _⟩ =>
        change 0 + c ⟨0, by omega⟩ * 1 = c ⟨0, by omega⟩
        omega
    · intro _; rfl
    · intro v hv
      have h0 := congrFun hv ⟨0, by omega⟩
      have h2 := congrFun hv ⟨2, by omega⟩
      unfold interiorA3 at h0 h2
      rw [matVec_diagMat] at h0 h2
      change 1 * v ⟨0, by omega⟩ = 0 * v ⟨0, by omega⟩ at h0
      change (-1) * v ⟨2, by omega⟩ = 0 * v ⟨2, by omega⟩ at h2
      funext i
      match i with
      | ⟨0, _⟩ =>
        change v ⟨0, by omega⟩ = 0 + v ⟨1, by omega⟩ * 0
        omega
      | ⟨1, _⟩ =>
        change v ⟨1, by omega⟩ = 0 + v ⟨1, by omega⟩ * 1
        omega
      | ⟨2, _⟩ =>
        change v ⟨2, by omega⟩ = 0 + v ⟨1, by omega⟩ * 0
        omega
  have hsing_dim : ZMod.HasDim (vecZMod 3) (InteriorLevelZariski pSing3) 2 := by
    let b : Fin 2 → Vec 3
      | ⟨0, _⟩ => stdBasis 3 ⟨0, by omega⟩
      | ⟨1, _⟩ => stdBasis 3 ⟨2, by omega⟩
    let coord : Vec 3 → Fin 2 → Int := fun v k =>
      match k with
      | ⟨0, _⟩ => v ⟨0, by omega⟩
      | ⟨1, _⟩ => v ⟨2, by omega⟩
    apply ZMod.hasDim_of_coords (vecZMod 3) b coord
    · intro k
      match k with
      | ⟨0, _⟩ => constructor <;> rfl
      | ⟨1, _⟩ => constructor <;> rfl
    · intro c k
      match k with
      | ⟨0, _⟩ =>
        change (0 + c ⟨0, by omega⟩ * 1) + c ⟨1, by omega⟩ * 0 = c ⟨0, by omega⟩
        omega
      | ⟨1, _⟩ =>
        change (0 + c ⟨0, by omega⟩ * 0) + c ⟨1, by omega⟩ * 1 = c ⟨1, by omega⟩
        omega
    · intro k
      match k with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    · intro v ⟨hv1, _⟩
      change ((0 + 0 * v ⟨0, by omega⟩) + 1 * v ⟨1, by omega⟩) + 0 * v ⟨2, by omega⟩ = 0 at hv1
      funext i
      match i with
      | ⟨0, _⟩ =>
        change v ⟨0, by omega⟩ = (0 + v ⟨0, by omega⟩ * 1) + v ⟨2, by omega⟩ * 0
        omega
      | ⟨1, _⟩ =>
        change v ⟨1, by omega⟩ = (0 + v ⟨0, by omega⟩ * 0) + v ⟨2, by omega⟩ * 0
        omega
      | ⟨2, _⟩ =>
        change v ⟨2, by omega⟩ = (0 + v ⟨0, by omega⟩ * 0) + v ⟨2, by omega⟩ * 1
        omega
  have hreg_dim : ZMod.HasDim (vecZMod 3) (InteriorLevelZariski qReg3) 1 := by
    let w : Vec 3
      | ⟨0, _⟩ => 1
      | ⟨1, _⟩ => -4
      | ⟨2, _⟩ => 1
    let b : Fin 1 → Vec 3 := fun _ => w
    let coord : Vec 3 → Fin 1 → Int := fun v _ => v ⟨0, by omega⟩
    apply ZMod.hasDim_of_coords (vecZMod 3) b coord
    · intro _; constructor <;> rfl
    · intro c k
      match k with
      | ⟨0, _⟩ =>
        change 0 + c ⟨0, by omega⟩ * 1 = c ⟨0, by omega⟩
        omega
    · intro _; rfl
    · intro v ⟨hv1, hv2⟩
      have hAq : matVec interiorA3 qReg3 = fun i => interiorEigs3 i * qReg3 i := by
        funext i; exact matVec_diagMat interiorEigs3 qReg3 i
      rw [hAq] at hv2
      change ((0 + 2 * v ⟨0, by omega⟩) + 1 * v ⟨1, by omega⟩) + 2 * v ⟨2, by omega⟩ = 0 at hv1
      change ((0 + (1 * 2) * v ⟨0, by omega⟩) + (0 * 1) * v ⟨1, by omega⟩) + ((-1) * 2) * v ⟨2, by omega⟩ = 0 at hv2
      funext i
      match i with
      | ⟨0, _⟩ =>
        change v ⟨0, by omega⟩ = 0 + v ⟨0, by omega⟩ * 1
        omega
      | ⟨1, _⟩ =>
        change v ⟨1, by omega⟩ = 0 + v ⟨0, by omega⟩ * (-4)
        omega
      | ⟨2, _⟩ =>
        change v ⟨2, by omega⟩ = 0 + v ⟨0, by omega⟩ * 1
        omega
  exact ⟨heig_dim, rfl, rfl, hsing_dim, hreg_dim,
         ZMod.not_hasDim_of_ne (vecZMod 3) hsing_dim (by omega)⟩

end Conjecture00000007165
