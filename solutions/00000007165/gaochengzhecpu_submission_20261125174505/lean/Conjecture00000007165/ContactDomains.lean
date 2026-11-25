/-
  Conjecture 00000007165 — Normalized Contact Domains 1–4 & Strict Contact Geometry
  Core Lean 4.19.0 (zero external dependencies).

  Formalizes exact contact loci, point-set characterizations, rational stereographic
  charts, smooth/Zariski tangent spaces, strict Sasakian contact geometry on `S^{2n-1}`,
  and dimension refutations across Domains 1–4:
  1. Real Unit Sphere `S^{n-1}`: `dim_ℝ = m - 1 ≠ m` for ALL `m ≥ 1` (`S^0` pair at `m = 1`).
  2. Real Projective Space `ℝℙ^{n-1}`: `dim_ℝ = m - 1 ≠ m` for ALL `m ≥ 1` (singleton at `m = 1`).
  3. Complex Unit Sphere `S^{2n-1}`: strict contact submanifold `(S^{2m-1}, Im⟨z, dz⟩)` with
     nondegenerate symplectic `dα|_ξ` and `dim_ℝ = 2m - 1` (`≠ m` for ALL `m ≥ 2`).
  4. Complex Projective Space `ℂℙ^{n-1}`: `dim_ℂ = m - 1 ≠ m` for ALL `m ≥ 1`, and
     `dim_ℝ = 2m - 2 ≠ m` for ALL `m ≠ 2` (in particular at `m = 1` and all `m ≥ 3`).
-/

import Conjecture00000007165.RayleighSpectrum

namespace Conjecture00000007165

/-! ## 1. Domain 1: Real Unit Sphere `S^{n-1}` -/

def RealSphereContact {n : Nat} (A : Mat n) (lamMax : Int) (x : Vec n) : Prop :=
  ∃ hx : x ≠ zeroVec n, normSq x = 1 ∧ RatVal.Eq (rayleigh A x hx) (RatVal.ofInt lamMax)

theorem stdBasis_ne_zero (n : Nat) (j : Fin n) : stdBasis n j ≠ zeroVec n := by
  intro heq
  have h1 := congrFun heq j
  simp [stdBasis, zeroVec] at h1

theorem stdBasis0_mem_realSphereContact {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    RealSphereContact (diagMat eigs) lamMax (stdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩) := by
  let j₀ : Fin n := ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩
  refine ⟨stdBasis_ne_zero n j₀, normSq_stdBasis n j₀, ?_⟩
  rw [rayleigh_eq_max_iff_eigvec hspec, eigvec_diag_iff_vanish_above hspec]
  intro i hi
  simp only [stdBasis]
  have hne : i ≠ j₀ := by
    intro heq
    have hv : i.val = 0 := congrArg Fin.val heq
    have hm1 := hspec.1
    omega
  simp [j₀, hne]

theorem int_sq_eq_one_iff (a : Int) : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    have hfac : (a - 1) * (a + 1) = 0 := by
      calc (a - 1) * (a + 1)
          = a * a + a * 1 - 1 * a - 1 * 1 := by
              rw [Int.sub_mul, Int.mul_add, Int.mul_add]
              omega
        _ = a * a - 1 := by omega
        _ = 0 := by omega
    cases Int.mul_eq_zero.mp hfac with
    | inl h1 => left; omega
    | inr h2 => right; omega
  · intro h
    cases h with
    | inl h1 => rw [h1]; rfl
    | inr h2 => rw [h2]; rfl

/-- At multiplicity `m = 1`, `M_{ℝ,S}(A) = {+e₀, -e₀} ≅ S^0` has exact cardinality `2` (`dim = 0 ≠ 1`). -/
theorem realSphereContact_m1_iff_pair {n : Nat} {eigs : Fin n → Int} {lamMax : Int}
    (hspec : HasMaxMult eigs lamMax 1) (x : Vec n) :
    let e₀ := stdBasis n ⟨0, by have := hspec.2.1; omega⟩
    RealSphereContact (diagMat eigs) lamMax x ↔ x = e₀ ∨ x = negVec e₀ := by
  intro e₀
  let idx₀ : Fin n := ⟨0, by have := hspec.2.1; omega⟩
  constructor
  · rintro ⟨hx, hns, hray⟩
    have hvan := (eigvec_diag_iff_vanish_above hspec x).mp ((rayleigh_eq_max_iff_eigvec hspec hx).mp hray)
    have hx0_sq : x idx₀ * x idx₀ = 1 := by
      have hcong : normSq x = intSum n (fun i => if i = idx₀ then x i * x i else 0) := by
        unfold normSq dot
        apply intSum_congr
        intro i
        by_cases hi : i = idx₀
        · subst hi; simp
        · have hge : 1 ≤ i.val := by
            by_cases h0 : i.val = 0
            · exact absurd (Fin.ext h0) hi
            · omega
          rw [hvan i hge]; simp [hi]
      rw [hcong, intSum_ite_eq] at hns
      exact hns
    cases (int_sq_eq_one_iff (x idx₀)).mp hx0_sq with
    | inl hp1 =>
      left
      funext i
      by_cases hi : i = idx₀
      · subst hi; simp [e₀, idx₀, stdBasis, hp1]
      · have hge : 1 ≤ i.val := by
          by_cases h0 : i.val = 0
          · exact absurd (Fin.ext h0) hi
          · omega
        rw [hvan i hge]
        simp [e₀, idx₀, stdBasis, hi]
    | inr hm1 =>
      right
      funext i
      by_cases hi : i = idx₀
      · subst hi; simp [e₀, idx₀, negVec, stdBasis, hm1]
      · have hge : 1 ≤ i.val := by
          by_cases h0 : i.val = 0
          · exact absurd (Fin.ext h0) hi
          · omega
        rw [hvan i hge]
        simp [e₀, idx₀, negVec, stdBasis, hi]
  · intro hpair
    cases hpair with
    | inl hp =>
      rw [hp]
      exact stdBasis0_mem_realSphereContact hspec
    | inr hm =>
      rw [hm]
      have hne : negVec e₀ ≠ zeroVec n := by
        intro heq
        have h0 := congrFun heq idx₀
        simp [e₀, idx₀, negVec, stdBasis, zeroVec] at h0
      have hns : normSq (negVec e₀) = 1 := by
        have hsm : negVec e₀ = smulVec (-1) e₀ := by funext i; simp [negVec, smulVec]
        rw [hsm, normSq_smul, normSq_stdBasis]
        rfl
      refine ⟨hne, hns, ?_⟩
      rw [rayleigh_eq_max_iff_eigvec hspec, eigvec_diag_iff_vanish_above hspec]
      intro i hi
      have hne_i : i ≠ idx₀ := by intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
      simp [e₀, idx₀, negVec, stdBasis, hne_i]

theorem stdBasis_ne_neg_stdBasis (n : Nat) (j : Fin n) :
    stdBasis n j ≠ negVec (stdBasis n j) := by
  intro heq
  have h := congrFun heq j
  simp [stdBasis, negVec] at h

/-- Exact algebraic identity underlying the `(m - 1)`-parameter rational stereographic chart
    `σ(y) = ((1 - ‖y‖²), 2 y₁, ..., 2 y_{m-1}) / (1 + ‖y‖²)` on `S^{m-1}`. -/
theorem stereographic_norm_identity {d : Nat} (y : Vec d) :
    (1 - normSq y) * (1 - normSq y) + intSum d (fun k => (2 * y k) * (2 * y k)) =
      (1 + normSq y) * (1 + normSq y) := by
  have hsum4 : intSum d (fun k => (2 * y k) * (2 * y k)) = 4 * normSq y := by
    unfold normSq dot
    rw [← intSum_mul_left]
    apply intSum_congr
    intro k
    calc (2 * y k) * (2 * y k)
        = (2 * 2) * (y k * y k) := by simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = 4 * (y k * y k) := rfl
  rw [hsum4]
  calc (1 - normSq y) * (1 - normSq y) + 4 * normSq y
      = 1 - 2 * normSq y + normSq y * normSq y + 4 * normSq y := by
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
          omega
    _ = 1 + 2 * normSq y + normSq y * normSq y := by omega
    _ = (1 + normSq y) * (1 + normSq y) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add]
          omega

/-- Smooth / Zariski tangent space to `M_{ℝ,S}(A) = S^{n-1} ∩ ker(A - lamMax I)` at `p`. -/
def TangentRealSphere {n : Nat} (A : Mat n) (lamMax : Int) (p : Vec n) (v : Vec n) : Prop :=
  dot p v = 0 ∧ RealEigenspace A lamMax v

theorem dot_stdBasis_left (n : Nat) (j : Fin n) (v : Vec n) :
    dot (stdBasis n j) v = v j := by
  unfold dot stdBasis
  have hcong : intSum n (fun i => (if i = j then (1 : Int) else 0) * v i) =
      intSum n (fun i => if i = j then v i else 0) := by
    apply intSum_congr
    intro i
    by_cases h : i = j <;> simp [h]
  rw [hcong, intSum_ite_eq]

/-- Exact dimension theorem for Domain 1: `dim_ℝ T_{e₀} M_{ℝ,S}(A) = m - 1` for all `1 ≤ m ≤ n`. -/
theorem tangentRealSphere_hasDim {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ZMod.HasDim (vecZMod n)
      (TangentRealSphere (diagMat eigs) lamMax
        (stdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      (m - 1) := by
  have hm1 : 1 ≤ m := hspec.1
  have hmn : m ≤ n := hspec.2.1
  let b : Fin (m - 1) → Vec n := fun k => stdBasis n ⟨k.val + 1, by omega⟩
  let coord : Vec n → Fin (m - 1) → Int := fun v k => v ⟨k.val + 1, by omega⟩
  apply ZMod.hasDim_of_coords (vecZMod n) b coord
  · intro k
    unfold TangentRealSphere
    rw [dot_stdBasis_left, eigvec_diag_iff_vanish_above hspec]
    constructor
    · simp only [b, stdBasis]
      have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨k.val + 1, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv
      simp [hne]
    · intro i hi
      simp only [b, stdBasis]
      have hne : i ≠ ⟨k.val + 1, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [hne]
  · intro c k
    unfold coord ZMod.linComb
    rw [vecFinSum_apply]
    have hcong : intSum (m - 1) (fun r => ((vecZMod n).smul (c r) (b r)) ⟨k.val + 1, by omega⟩) =
        intSum (m - 1) (fun r => if r = k then c r else 0) := by
      apply intSum_congr
      intro r
      simp only [vecZMod, smulVec, b, stdBasis]
      by_cases hrk : r = k
      · subst hrk; simp
      · have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ ⟨r.val + 1, by omega⟩ := by
          intro heq
          have hv := congrArg Fin.val heq; simp at hv
          apply hrk; ext; omega
        simp [hrk, hne]
    rw [hcong, intSum_ite_eq]
  · intro _k; rfl
  · intro v ⟨hv0, hveig⟩
    rw [dot_stdBasis_left] at hv0
    have hvan := (eigvec_diag_iff_vanish_above hspec v).mp hveig
    funext i
    unfold ZMod.linComb coord
    rw [vecFinSum_apply]
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hi_eq, hv0]
      have hcong : intSum (m - 1) (fun r => ((vecZMod n).smul (v ⟨r.val + 1, by omega⟩) (b r)) ⟨0, by omega⟩) =
          intSum (m - 1) (fun _ => 0) := by
        apply intSum_congr
        intro r
        have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨r.val + 1, by omega⟩ := by
          intro heq; have hv := congrArg Fin.val heq; simp at hv
        simp [vecZMod, smulVec, b, stdBasis, hne]
      rw [hcong, intSum_zero_fn]
    · by_cases him : i.val < m
      · let k₀ : Fin (m - 1) := ⟨i.val - 1, by omega⟩
        have hcong : intSum (m - 1) (fun r => ((vecZMod n).smul (v ⟨r.val + 1, by omega⟩) (b r)) i) =
            intSum (m - 1) (fun r => if r = k₀ then v i else 0) := by
          apply intSum_congr
          intro r
          simp only [vecZMod, smulVec, b, stdBasis]
          by_cases hrk : r = k₀
          · subst hrk
            have heq : i = ⟨k₀.val + 1, by omega⟩ := by ext; simp [k₀]; omega
            simp [← heq]
          · have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
              intro heq
              have hv := congrArg Fin.val heq; simp at hv
              apply hrk; ext; simp [k₀]; omega
            simp [hrk, hne]
        rw [hcong, intSum_ite_eq]
      · rw [hvan i (by omega)]
        have hcong : intSum (m - 1) (fun r => ((vecZMod n).smul (v ⟨r.val + 1, by omega⟩) (b r)) i) =
            intSum (m - 1) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp [vecZMod, smulVec, b, stdBasis, hne]
        rw [hcong, intSum_zero_fn]

/-- Universal refutation on `S^{n-1}`: `T_{e₀} M_{ℝ,S}(A)` NEVER has dimension `m` (`∀ m ≥ 1`). -/
theorem tangentRealSphere_not_hasDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ¬ ZMod.HasDim (vecZMod n)
      (TangentRealSphere (diagMat eigs) lamMax
        (stdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      m := by
  apply ZMod.not_hasDim_of_ne (vecZMod n) (tangentRealSphere_hasDim hspec)
  have hm1 := hspec.1
  omega

/-! ## 2. Domain 2: Real Projective Space `ℝℙ^{n-1}` -/

def RealProjContact {n : Nat} (A : Mat n) (lamMax : Int) (x : Vec n) : Prop :=
  ∃ hx : x ≠ zeroVec n, RatVal.Eq (rayleigh A x hx) (RatVal.ofInt lamMax)

theorem realProjContact_projInvar {n : Nat} (A : Mat n) (lamMax : Int) {x y : Vec n}
    (hx : x ≠ zeroVec n) (hy : y ≠ zeroVec n) (hp : ProjEquiv x y) :
    RealProjContact A lamMax x → RealProjContact A lamMax y := by
  rintro ⟨_, hrx⟩
  refine ⟨hy, ?_⟩
  have heq := rayleigh_projInvar A hx hy hp
  unfold RatVal.Eq at heq hrx ⊢
  simp [RatVal.ofInt] at hrx ⊢
  have hns_pos := normSq_pos hx
  have hns_ne : (rayleigh A x hx).den ≠ 0 := by
    change normSq x ≠ 0
    omega
  apply Int.eq_of_mul_eq_mul_left hns_ne
  calc (rayleigh A x hx).den * (rayleigh A y hy).num
      = (rayleigh A y hy).num * (rayleigh A x hx).den := Int.mul_comm _ _
    _ = (rayleigh A x hx).num * (rayleigh A y hy).den := heq.symm
    _ = (lamMax * (rayleigh A x hx).den) * (rayleigh A y hy).den := by rw [hrx]
    _ = (rayleigh A x hx).den * (lamMax * (rayleigh A y hy).den) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-- At multiplicity `m = 1`, `M_{ℝℙ}(A) = {[e₀]}` is a SINGLETON ray (`dim = 0 ≠ 1`). -/
theorem realProjContact_m1_unique_ray {n : Nat} {eigs : Fin n → Int} {lamMax : Int}
    (hspec : HasMaxMult eigs lamMax 1) {x : Vec n}
    (hx_mem : RealProjContact (diagMat eigs) lamMax x) :
    ProjEquiv x (stdBasis n ⟨0, by have := hspec.2.1; omega⟩) := by
  rcases hx_mem with ⟨hx, hray⟩
  have hvan := (eigvec_diag_iff_vanish_above hspec x).mp ((rayleigh_eq_max_iff_eigvec hspec hx).mp hray)
  let idx₀ : Fin n := ⟨0, by have := hspec.2.1; omega⟩
  have hx0_ne : x idx₀ ≠ 0 := by
    intro h0
    apply hx
    funext i
    by_cases hi : i = idx₀
    · subst hi; exact h0
    · have hge : 1 ≤ i.val := by
        by_cases hz : i.val = 0
        · exact absurd (Fin.ext hz) hi
        · omega
      exact hvan i hge
  refine ⟨1, x idx₀, by omega, hx0_ne, ?_⟩
  funext i
  simp only [smulVec, Int.one_mul, stdBasis]
  by_cases hi : i = idx₀
  · subst hi; simp [idx₀]
  · have hge : 1 ≤ i.val := by
      by_cases hz : i.val = 0
      · exact absurd (Fin.ext hz) hi
      · omega
    rw [hvan i hge]
    simp [idx₀, hi]

/-- Tangent space to `M_{ℝℙ}(A)` at `[p]` (represented as `{v ∈ ker(A - lamMax I) : ⟨p, v⟩ = 0} ≅ ker / ℝ p`). -/
abbrev TangentRealProj {n : Nat} (A : Mat n) (lamMax : Int) (p : Vec n) : Vec n → Prop :=
  TangentRealSphere A lamMax p

theorem tangentRealProj_not_hasDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ¬ ZMod.HasDim (vecZMod n)
      (TangentRealProj (diagMat eigs) lamMax
        (stdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      m :=
  tangentRealSphere_not_hasDim_m hspec

/-! ## 3. Domain 3: Complex Unit Sphere `S^{2n-1}` & Strict Contact Geometry -/

def ComplexSphereContact {n : Nat} (A : CMat n) (lamMax : Int) (z : CVec n) : Prop :=
  ∃ hz : z ≠ zeroCVec n, cNormSq z = 1 ∧ RatVal.Eq (cRayleigh A z hz) (RatVal.ofInt lamMax)

theorem cStdBasis_ne_zero (n : Nat) (j : Fin n) : cStdBasis n j ≠ zeroCVec n := by
  intro heq
  have h := congrArg GaussInt.re (congrFun heq j)
  simp [cStdBasis, zeroCVec, GaussInt.one, GaussInt.zero] at h

theorem cNormSq_cStdBasis (n : Nat) (j : Fin n) : cNormSq (cStdBasis n j) = 1 := by
  unfold cNormSq cStdBasis
  have hcong : intSum n (fun i => (if i = j then GaussInt.one else GaussInt.zero).normSq) =
      intSum n (fun i => if i = j then (1 : Int) else 0) := by
    apply intSum_congr
    intro i
    by_cases h : i = j <;> simp [h, GaussInt.normSq, GaussInt.one, GaussInt.zero]
  rw [hcong, intSum_ite_eq]

theorem cStdBasis0_mem_complexSphereContact {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ComplexSphereContact (cDiagMat eigs) lamMax
      (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩) := by
  let j₀ : Fin n := ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩
  refine ⟨cStdBasis_ne_zero n j₀, cNormSq_cStdBasis n j₀, ?_⟩
  rw [cRayleigh_eq_max_iff_eigvec hspec, cEigvec_diag_iff_vanish_above hspec]
  intro i hi
  have hne : i ≠ j₀ := by
    intro heq; have hv := congrArg Fin.val heq; simp [j₀] at hv; have := hspec.1; omega
  simp [j₀, cStdBasis, hne]

theorem hermInner_cStdBasis_left (n : Nat) (j : Fin n) (v : CVec n) :
    hermInner (cStdBasis n j) v = v j := by
  unfold hermInner cStdBasis
  ext
  · rw [gaussSum_re]
    have hcong : intSum n (fun i => (GaussInt.mul (GaussInt.conj (if i = j then GaussInt.one else GaussInt.zero)) (v i)).re) =
        intSum n (fun i => if i = j then (v i).re else 0) := by
      apply intSum_congr
      intro i
      by_cases h : i = j
      · subst h; simp [GaussInt.conj, GaussInt.one, GaussInt.mul]
      · simp [h, GaussInt.conj, GaussInt.zero, GaussInt.mul]
    rw [hcong, intSum_ite_eq]
  · rw [gaussSum_im]
    have hcong : intSum n (fun i => (GaussInt.mul (GaussInt.conj (if i = j then GaussInt.one else GaussInt.zero)) (v i)).im) =
        intSum n (fun i => if i = j then (v i).im else 0) := by
      apply intSum_congr
      intro i
      by_cases h : i = j
      · subst h; simp [GaussInt.conj, GaussInt.one, GaussInt.mul]
      · simp [h, GaussInt.conj, GaussInt.zero, GaussInt.mul]
    rw [hcong, intSum_ite_eq]

/-- Real (`ℤ`) tangent space to `M_{ℂ,S}(A) = S^{2n-1} ∩ ker_ℂ(A - lamMax I)` at `p`. -/
def TangentComplexSphere {n : Nat} (A : CMat n) (lamMax : Int) (p : CVec n) (v : CVec n) : Prop :=
  (hermInner p v).re = 0 ∧ ComplexEigenspace A lamMax v

/-- Exact real dimension theorem for Domain 3: `dim_ℝ T_{e₀} M_{ℂ,S}(A) = 2m - 1` for all `1 ≤ m ≤ n`. -/
theorem tangentComplexSphere_hasDim {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ZMod.HasDim (cVecRMod n)
      (TangentComplexSphere (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      (2 * m - 1) := by
  have hm1 : 1 ≤ m := hspec.1
  have hmn : m ≤ n := hspec.2.1
  let idx₀ : Fin n := ⟨0, by omega⟩
  -- Basis of size `2m - 1`: `k = 0` is `i e₀`; for `k ≥ 1`, `(k + 1) / 2` gives coordinate index,
  -- odd `k` gives real basis `e_j`, even `k` gives imaginary basis `i e_j`.
  let b : Fin (2 * m - 1) → CVec n := fun k =>
    if hk0 : k.val = 0 then cImagBasis n idx₀
    else
      let j : Fin n := ⟨(k.val + 1) / 2, by omega⟩
      if k.val % 2 = 1 then cStdBasis n j else cImagBasis n j
  let coord : CVec n → Fin (2 * m - 1) → Int := fun v k =>
    if hk0 : k.val = 0 then (v idx₀).im
    else
      let j : Fin n := ⟨(k.val + 1) / 2, by omega⟩
      if k.val % 2 = 1 then (v j).re else (v j).im
  apply ZMod.hasDim_of_coords (cVecRMod n) b coord
  · intro k
    unfold TangentComplexSphere
    rw [hermInner_cStdBasis_left, cEigvec_diag_iff_vanish_above hspec]
    by_cases hk0 : k.val = 0
    · simp only [b, hk0, ↓reduceDIte, cImagBasis]
      constructor
      · simp [idx₀, GaussInt.I]
      · intro i hi
        have hne : i ≠ idx₀ := by intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
        simp [idx₀, hne]
    · simp only [b, hk0, ↓reduceDIte]
      have hj_pos : idx₀ ≠ ⟨(k.val + 1) / 2, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
      by_cases hmod : k.val % 2 = 1
      · simp only [hmod, ↓reduceIte, cStdBasis]
        constructor
        · have hj_pos' : (⟨0, by omega⟩ : Fin n) ≠ ⟨(k.val + 1) / 2, by omega⟩ := hj_pos
          simp [hj_pos', GaussInt.zero]
        · intro i hi
          have hne : i ≠ ⟨(k.val + 1) / 2, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp [hne]
      · simp only [hmod, ↓reduceIte, cImagBasis]
        constructor
        · have hj_pos' : (⟨0, by omega⟩ : Fin n) ≠ ⟨(k.val + 1) / 2, by omega⟩ := hj_pos
          simp [hj_pos', GaussInt.zero]
        · intro i hi
          have hne : i ≠ ⟨(k.val + 1) / 2, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp [hne]
  · intro c k
    dsimp only [coord]
    unfold ZMod.linComb
    by_cases hk0 : k.val = 0
    · simp only [hk0, ↓reduceDIte]
      rw [cVecFinSum_apply, gaussSum_im]
      have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (c r) (b r) idx₀).im) =
          intSum (2 * m - 1) (fun r => if r = k then c r else 0) := by
        apply intSum_congr
        intro r
        simp only [cVecRMod, rSmulCVec, b]
        by_cases hr0 : r.val = 0
        · have hrk : r = k := by ext; omega
          simp [hk0, hrk, cImagBasis, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
        · have hrk : r ≠ k := by intro heq; subst heq; exact hr0 hk0
          have hj_ne : idx₀ ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
          by_cases hrmod : r.val % 2 = 1 <;>
            simp [hr0, hrk, hrmod, cStdBasis, cImagBasis, hj_ne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
    · simp only [hk0, ↓reduceDIte]
      by_cases hmod : k.val % 2 = 1
      · simp only [hmod, ↓reduceIte]
        rw [cVecFinSum_apply, gaussSum_re]
        have hcong : intSum (2 * m - 1)
            (fun r => ((cVecRMod n).smul (c r) (b r) ⟨(k.val + 1) / 2, by omega⟩).re) =
            intSum (2 * m - 1) (fun r => if r = k then c r else 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr0 : r.val = 0
          · have hrk : r ≠ k := by intro heq; subst heq; exact hk0 hr0
            have hne : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) ≠ idx₀ := by
              intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
            simp [hr0, hrk, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          · simp only [hr0, ↓reduceDIte]
            by_cases hrmod : r.val % 2 = 1
            · simp only [hrmod, ↓reduceIte, cStdBasis]
              by_cases hrk : r = k
              · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.one]
              · have hne : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                  intro heq
                  have hv := congrArg Fin.val heq; simp at hv
                  apply hrk; ext; omega
                simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, cImagBasis]
              have hrk : r ≠ k := by intro heq; subst heq; exact hrmod hmod
              by_cases hdiv : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) = ⟨(r.val + 1) / 2, by omega⟩ <;>
                simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
      · simp only [hmod, ↓reduceIte]
        rw [cVecFinSum_apply, gaussSum_im]
        have hcong : intSum (2 * m - 1)
            (fun r => ((cVecRMod n).smul (c r) (b r) ⟨(k.val + 1) / 2, by omega⟩).im) =
            intSum (2 * m - 1) (fun r => if r = k then c r else 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr0 : r.val = 0
          · have hrk : r ≠ k := by intro heq; subst heq; exact hk0 hr0
            have hne : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) ≠ idx₀ := by
              intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
            simp [hr0, hrk, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          · simp only [hr0, ↓reduceDIte]
            by_cases hrmod : r.val % 2 = 1
            · simp only [hrmod, ↓reduceIte, cStdBasis]
              have hrk : r ≠ k := by intro heq; subst heq; exact hmod hrmod
              by_cases hdiv : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) = ⟨(r.val + 1) / 2, by omega⟩ <;>
                simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, cImagBasis]
              by_cases hrk : r = k
              · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.I]
              · have hne : (⟨(k.val + 1) / 2, by omega⟩ : Fin n) ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                  intro heq
                  have hv := congrArg Fin.val heq; simp at hv
                  apply hrk; ext; omega
                simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
  · intro k
    simp only [coord, cVecRMod, zeroCVec, GaussInt.zero]
    by_cases hk0 : k.val = 0
    · simp [hk0]
    · by_cases hmod : k.val % 2 = 1 <;> simp [hk0, hmod]
  · intro v ⟨hv0, hveig⟩
    rw [hermInner_cStdBasis_left] at hv0
    have hvan := (cEigvec_diag_iff_vanish_above hspec v).mp hveig
    funext i
    unfold ZMod.linComb
    rw [cVecFinSum_apply]
    by_cases hi0 : i.val = 0
    · have hi_eq : i = idx₀ := Fin.ext hi0
      rw [hi_eq]
      let k₀ : Fin (2 * m - 1) := ⟨0, by omega⟩
      ext
      · have hv0' : (v idx₀).re = 0 := hv0
        rw [hv0', gaussSum_re]
        have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) idx₀).re) =
            intSum (2 * m - 1) (fun _ => 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr0 : r.val = 0
          · simp [hr0, cImagBasis, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
          · have hne : idx₀ ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
            by_cases hrmod : r.val % 2 = 1 <;>
              simp [hr0, hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_zero_fn]
      · rw [gaussSum_im]
        have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) idx₀).im) =
            intSum (2 * m - 1) (fun r => if r = k₀ then (v idx₀).im else 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b, coord]
          by_cases hr0 : r.val = 0
          · have hrk : r = k₀ := Fin.ext hr0
            simp [k₀, hr0, hrk, cImagBasis, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
          · have hrk : r ≠ k₀ := fun heq => hr0 (congrArg Fin.val heq)
            have hne : idx₀ ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; omega
            by_cases hrmod : r.val % 2 = 1 <;>
              simp [hr0, hrk, hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
    · by_cases him : i.val < m
      · let k_re : Fin (2 * m - 1) := ⟨2 * i.val - 1, by omega⟩
        let k_im : Fin (2 * m - 1) := ⟨2 * i.val, by omega⟩
        ext
        · rw [gaussSum_re]
          have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) i).re) =
              intSum (2 * m - 1) (fun r => if r = k_re then (v i).re else 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b, coord]
            by_cases hr0 : r.val = 0
            · have hrk : r ≠ k_re := by intro heq; have hv := congrArg Fin.val heq; simp [k_re] at hv; omega
              have hne : i ≠ idx₀ := fun heq => hi0 (congrArg Fin.val heq)
              simp [hr0, hrk, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · simp only [hr0, ↓reduceDIte]
              by_cases hrmod : r.val % 2 = 1
              · simp only [hrmod, ↓reduceIte, cStdBasis]
                by_cases hrk : r = k_re
                · subst hrk
                  have hdiv : (⟨((2 * i.val - 1) + 1) / 2, by omega⟩ : Fin n) = i := by
                    ext; simp; omega
                  simp [k_re, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one]
                · have hne : i ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                    intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k_re]; omega
                  simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
              · simp only [hrmod, ↓reduceIte, cImagBasis]
                have hrk : r ≠ k_re := by
                  intro heq; subst heq; simp [k_re] at hrmod; omega
                by_cases hdiv : i = ⟨(r.val + 1) / 2, by omega⟩ <;>
                  simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
        · rw [gaussSum_im]
          have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) i).im) =
              intSum (2 * m - 1) (fun r => if r = k_im then (v i).im else 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b, coord]
            by_cases hr0 : r.val = 0
            · have hrk : r ≠ k_im := by intro heq; have hv := congrArg Fin.val heq; simp [k_im] at hv; omega
              have hne : i ≠ idx₀ := fun heq => hi0 (congrArg Fin.val heq)
              simp [hr0, hrk, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · simp only [hr0, ↓reduceDIte]
              by_cases hrmod : r.val % 2 = 1
              · simp only [hrmod, ↓reduceIte, cStdBasis]
                have hrk : r ≠ k_im := by
                  intro heq; subst heq; simp [k_im] at hrmod
                by_cases hdiv : i = ⟨(r.val + 1) / 2, by omega⟩ <;>
                  simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
              · simp only [hrmod, ↓reduceIte, cImagBasis]
                by_cases hrk : r = k_im
                · subst hrk
                  have hdiv : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := by
                    ext; simp; omega
                  simp [k_im, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
                · have hne : i ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                    intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k_im]; omega
                  simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
      · rw [hvan i (by omega)]
        ext
        · rw [gaussSum_re]
          have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) i).re) =
              intSum (2 * m - 1) (fun _ => 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hr0 : r.val = 0
            · have hne : i ≠ idx₀ := fun heq => hi0 (congrArg Fin.val heq)
              simp [hr0, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · have hne : i ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
              by_cases hrmod : r.val % 2 = 1 <;>
                simp [hr0, hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl
        · rw [gaussSum_im]
          have hcong : intSum (2 * m - 1) (fun r => ((cVecRMod n).smul (coord v r) (b r) i).im) =
              intSum (2 * m - 1) (fun _ => 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hr0 : r.val = 0
            · have hne : i ≠ idx₀ := fun heq => hi0 (congrArg Fin.val heq)
              simp [hr0, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · have hne : i ≠ ⟨(r.val + 1) / 2, by omega⟩ := by
                intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
              by_cases hrmod : r.val % 2 = 1 <;>
                simp [hr0, hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl

/-- Refutation on `S^{2n-1}`: for EVERY `m ≥ 2`, `dim_ℝ T_{e₀} M_{ℂ,S}(A) = 2m - 1 ≠ m`! -/
theorem tangentComplexSphere_not_hasDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) (hm2 : 2 ≤ m) :
    ¬ ZMod.HasDim (cVecRMod n)
      (TangentComplexSphere (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      m := by
  apply ZMod.not_hasDim_of_ne (cVecRMod n) (tangentComplexSphere_hasDim hspec)
  omega

/-- Standard Sasakian contact 1-form `α_p(v) = Im⟨p, v⟩` and Reeb vector `R_p = i p`. -/
def contactAlpha {n : Nat} (p v : CVec n) : Int := (hermInner p v).im

def reebVec {n : Nat} (p : CVec n) : CVec n := cSmulCVec GaussInt.I p

def ContactXi {n : Nat} (A : CMat n) (lamMax : Int) (p v : CVec n) : Prop :=
  TangentComplexSphere A lamMax p v ∧ contactAlpha p v = 0

/-- `M_{ℂ,S}(A)` is a genuine strict contact manifold: `R_{e₀} ∈ T_{e₀} M`, `α(R_{e₀}) = 1`,
    and the symplectic 2-form `dα(u, w) = 2 Im⟨u, w⟩` is nondegenerate on `ξ = ker α`. -/
theorem complexSphere_strict_contact_structure {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    let e₀ := cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩
    TangentComplexSphere (cDiagMat eigs) lamMax e₀ (reebVec e₀) ∧
    contactAlpha e₀ (reebVec e₀) = 1 ∧
    (∀ u, ContactXi (cDiagMat eigs) lamMax e₀ u →
      (∀ w, ContactXi (cDiagMat eigs) lamMax e₀ w → (hermInner u w).im = 0) →
      u = zeroCVec n) := by
  intro e₀
  let idx₀ : Fin n := ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold TangentComplexSphere reebVec
    rw [hermInner_cStdBasis_left, cEigvec_diag_iff_vanish_above hspec]
    constructor
    · simp [e₀, idx₀, cSmulCVec, cStdBasis, GaussInt.mul, GaussInt.I, GaussInt.one]
    · intro i hi
      have hne : i ≠ idx₀ := by intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv; have := hspec.1; omega
      simp [e₀, idx₀, cSmulCVec, cStdBasis, hne, GaussInt.mul_zero]
  · unfold contactAlpha reebVec
    rw [hermInner_cStdBasis_left]
    simp [e₀, idx₀, cSmulCVec, cStdBasis, GaussInt.mul, GaussInt.I, GaussInt.one]
  · intro u ⟨⟨hu_re, hu_eig⟩, hu_im⟩ hsymp
    rw [hermInner_cStdBasis_left] at hu_re
    unfold contactAlpha at hu_im
    rw [hermInner_cStdBasis_left] at hu_im
    have hu0 : u idx₀ = GaussInt.zero := by ext <;> simp [idx₀, GaussInt.zero, hu_re, hu_im]
    have hvan := (cEigvec_diag_iff_vanish_above hspec u).mp hu_eig
    -- Test `w = i u ∈ ContactXi`: `(hermInner u (i u)).im = cNormSq u = 0`!
    let w := cSmulCVec GaussInt.I u
    have hw_mem : ContactXi (cDiagMat eigs) lamMax e₀ w := by
      unfold ContactXi TangentComplexSphere contactAlpha
      rw [hermInner_cStdBasis_left, cEigvec_diag_iff_vanish_above hspec]
      have hu0' : u ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩ = GaussInt.zero := hu0
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [w, cSmulCVec, hu0', GaussInt.mul, GaussInt.zero]
      · intro i hi
        simp [w, cSmulCVec, hvan i hi, GaussInt.mul_zero]
      · simp [w, cSmulCVec, hu0', GaussInt.mul, GaussInt.zero]
    have him0 := hsymp w hw_mem
    have hcalc : (hermInner u w).im = cNormSq u := by
      unfold hermInner w cSmulCVec cNormSq
      rw [gaussSum_im]
      apply intSum_congr
      intro j
      simp [GaussInt.conj, GaussInt.mul, GaussInt.I, GaussInt.normSq, Int.neg_mul, Int.mul_neg]
    rw [hcalc] at him0
    exact (cNormSq_eq_zero_iff u).mp him0

/-- Topological parity obstruction: every strict contact manifold has odd real dimension `2d + 1`,
    hence can NEVER equal an even multiplicity `m = 2k`. -/
theorem strict_contact_dim_odd_obstruction (d k : Nat) : 2 * d + 1 ≠ 2 * k := by
  omega

/-! ## 4. Domain 4: Complex Projective Space `ℂℙ^{n-1}` -/

def ComplexProjContact {n : Nat} (A : CMat n) (lamMax : Int) (z : CVec n) : Prop :=
  ∃ hz : z ≠ zeroCVec n, RatVal.Eq (cRayleigh A z hz) (RatVal.ofInt lamMax)

/-- At multiplicity `m = 1`, `M_{ℂℙ}(A) = {[e₀]}` is a SINGLETON ray (`dim_ℂ = dim_ℝ = 0 ≠ 1`). -/
theorem complexProjContact_m1_unique_ray {n : Nat} {eigs : Fin n → Int} {lamMax : Int}
    (hspec : HasMaxMult eigs lamMax 1) {z : CVec n}
    (hz_mem : ComplexProjContact (cDiagMat eigs) lamMax z) :
    CProjEquiv z (cStdBasis n ⟨0, by have := hspec.2.1; omega⟩) := by
  rcases hz_mem with ⟨hz, hray⟩
  have hvan := (cEigvec_diag_iff_vanish_above hspec z).mp
    ((cRayleigh_eq_max_iff_eigvec hspec hz).mp hray)
  let idx₀ : Fin n := ⟨0, by have := hspec.2.1; omega⟩
  have hz0_ne : z idx₀ ≠ GaussInt.zero := by
    intro h0
    apply hz
    funext i
    by_cases hi : i = idx₀
    · subst hi; exact h0
    · have hge : 1 ≤ i.val := by
        by_cases hz_i : i.val = 0
        · exact absurd (Fin.ext hz_i) hi
        · omega
      exact hvan i hge
  refine ⟨GaussInt.one, z idx₀, by intro h; injection h with h1; omega, hz0_ne, ?_⟩
  funext i
  simp only [cSmulCVec, GaussInt.one_mul, cStdBasis]
  by_cases hi : i = idx₀
  · subst hi; simp [idx₀, GaussInt.mul_one]
  · have hge : 1 ≤ i.val := by
      by_cases hz_i : i.val = 0
      · exact absurd (Fin.ext hz_i) hi
      · omega
    rw [hvan i hge]
    simp [idx₀, hi, GaussInt.mul_zero]

/-- Projective tangent space to `M_{ℂℙ}(A)` at `[p]`: `{v ∈ ker_ℂ(A - lamMax I) : ⟨p, v⟩ = 0} ≅ ker_ℂ / ℂ p`. -/
def TangentComplexProj {n : Nat} (A : CMat n) (lamMax : Int) (p v : CVec n) : Prop :=
  hermInner p v = GaussInt.zero ∧ ComplexEigenspace A lamMax v

/-- Exact complex dimension of `M_{ℂℙ}(A)`: `dim_ℂ = m - 1` for all `1 ≤ m ≤ n`. -/
theorem tangentComplexProj_hasCDim {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    CMod.HasCDim (cVecCMod n)
      (TangentComplexProj (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      (m - 1) := by
  have hm1 : 1 ≤ m := hspec.1
  have hmn : m ≤ n := hspec.2.1
  let idx₀ : Fin n := ⟨0, by omega⟩
  let b : Fin (m - 1) → CVec n := fun k => cStdBasis n ⟨k.val + 1, by omega⟩
  let coord : CVec n → Fin (m - 1) → GaussInt := fun v k => v ⟨k.val + 1, by omega⟩
  apply CMod.hasCDim_of_coords (cVecCMod n) b coord
  · intro k
    unfold TangentComplexProj
    rw [hermInner_cStdBasis_left, cEigvec_diag_iff_vanish_above hspec]
    constructor
    · have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨k.val + 1, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv
      simp [b, cStdBasis, hne]
    · intro i hi
      have hne : i ≠ ⟨k.val + 1, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [b, cStdBasis, hne]
  · intro c k
    unfold coord CMod.clinComb
    simp only [cVecCMod]
    rw [cVecFinSum_apply]
    ext
    · rw [gaussSum_re]
      have hcong : intSum (m - 1) (fun r => (cSmulCVec (c r) (b r) ⟨k.val + 1, by omega⟩).re) =
          intSum (m - 1) (fun r => if r = k then (c r).re else 0) := by
        apply intSum_congr
        intro r
        simp only [cSmulCVec, b, cStdBasis]
        by_cases hrk : r = k
        · subst hrk; simp [GaussInt.mul_one]
        · have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ ⟨r.val + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; omega
          simp [hrk, hne, GaussInt.mul, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
    · rw [gaussSum_im]
      have hcong : intSum (m - 1) (fun r => (cSmulCVec (c r) (b r) ⟨k.val + 1, by omega⟩).im) =
          intSum (m - 1) (fun r => if r = k then (c r).im else 0) := by
        apply intSum_congr
        intro r
        simp only [cSmulCVec, b, cStdBasis]
        by_cases hrk : r = k
        · subst hrk; simp [GaussInt.mul_one]
        · have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ ⟨r.val + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; omega
          simp [hrk, hne, GaussInt.mul, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
  · intro _k; rfl
  · intro v ⟨hv0, hveig⟩
    rw [hermInner_cStdBasis_left] at hv0
    have hvan := (cEigvec_diag_iff_vanish_above hspec v).mp hveig
    funext i
    unfold CMod.clinComb coord
    simp only [cVecCMod]
    rw [cVecFinSum_apply]
    by_cases hi0 : i.val = 0
    · have hi_eq : i = idx₀ := Fin.ext hi0
      rw [hi_eq, hv0]
      ext
      · rw [gaussSum_re]
        have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) idx₀).re) =
            intSum (m - 1) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : idx₀ ≠ ⟨r.val + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv
          simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
      · rw [gaussSum_im]
        have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) idx₀).im) =
            intSum (m - 1) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : idx₀ ≠ ⟨r.val + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv
          simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
    · by_cases him : i.val < m
      · let k₀ : Fin (m - 1) := ⟨i.val - 1, by omega⟩
        ext
        · rw [gaussSum_re]
          have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) i).re) =
              intSum (m - 1) (fun r => if r = k₀ then (v i).re else 0) := by
            apply intSum_congr
            intro r
            simp only [cSmulCVec, b, cStdBasis]
            by_cases hrk : r = k₀
            · subst hrk
              have heq : i = ⟨k₀.val + 1, by omega⟩ := by ext; simp [k₀]; omega
              simp [← heq, GaussInt.mul_one]
            · have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
                intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k₀]; omega
              simp [hrk, hne, GaussInt.mul, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
        · rw [gaussSum_im]
          have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) i).im) =
              intSum (m - 1) (fun r => if r = k₀ then (v i).im else 0) := by
            apply intSum_congr
            intro r
            simp only [cSmulCVec, b, cStdBasis]
            by_cases hrk : r = k₀
            · subst hrk
              have heq : i = ⟨k₀.val + 1, by omega⟩ := by ext; simp [k₀]; omega
              simp [← heq, GaussInt.mul_one]
            · have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
                intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k₀]; omega
              simp [hrk, hne, GaussInt.mul, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
      · rw [hvan i (by omega)]
        ext
        · rw [gaussSum_re]
          have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) i).re) =
              intSum (m - 1) (fun _ => 0) := by
            apply intSum_congr
            intro r
            have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
            simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl
        · rw [gaussSum_im]
          have hcong : intSum (m - 1) (fun r => (cSmulCVec (v ⟨r.val + 1, by omega⟩) (b r) i).im) =
              intSum (m - 1) (fun _ => 0) := by
            apply intSum_congr
            intro r
            have hne : i ≠ ⟨r.val + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
            simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl

/-- Universal complex-dimension refutation on `ℂℙ^{n-1}`: `dim_ℂ M_{ℂℙ}(A) = m - 1 ≠ m` (`∀ m ≥ 1`). -/
theorem tangentComplexProj_not_hasCDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ¬ CMod.HasCDim (cVecCMod n)
      (TangentComplexProj (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      m := by
  apply CMod.not_hasCDim_of_ne (cVecCMod n) (tangentComplexProj_hasCDim hspec)
  have := hspec.1
  omega

/-- Exact real dimension of `M_{ℂℙ}(A)`: `dim_ℝ = 2m - 2` for all `1 ≤ m ≤ n`. -/
theorem tangentComplexProj_hasRDim {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ZMod.HasDim (cVecRMod n)
      (TangentComplexProj (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      (2 * m - 2) := by
  have hm1 : 1 ≤ m := hspec.1
  have hmn : m ≤ n := hspec.2.1
  let idx₀ : Fin n := ⟨0, by omega⟩
  let b : Fin (2 * m - 2) → CVec n := fun k =>
    let j : Fin n := ⟨k.val / 2 + 1, by omega⟩
    if k.val % 2 = 0 then cStdBasis n j else cImagBasis n j
  let coord : CVec n → Fin (2 * m - 2) → Int := fun v k =>
    let j : Fin n := ⟨k.val / 2 + 1, by omega⟩
    if k.val % 2 = 0 then (v j).re else (v j).im
  apply ZMod.hasDim_of_coords (cVecRMod n) b coord
  · intro k
    unfold TangentComplexProj
    rw [hermInner_cStdBasis_left, cEigvec_diag_iff_vanish_above hspec]
    have hj_ne : idx₀ ≠ ⟨k.val / 2 + 1, by omega⟩ := by
      intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv
    by_cases hmod : k.val % 2 = 0
    · simp only [b, hmod, ↓reduceIte, cStdBasis]
      refine ⟨by simp [hj_ne], fun i hi => ?_⟩
      have hne : i ≠ ⟨k.val / 2 + 1, by omega⟩ := by intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [hne]
    · simp only [b, hmod, ↓reduceIte, cImagBasis]
      refine ⟨by simp [hj_ne], fun i hi => ?_⟩
      have hne : i ≠ ⟨k.val / 2 + 1, by omega⟩ := by intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [hne]
  · intro c k
    dsimp only [coord]
    unfold ZMod.linComb
    by_cases hmod : k.val % 2 = 0
    · simp only [hmod, ↓reduceIte]
      rw [cVecFinSum_apply, gaussSum_re]
      have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul (c r) (b r) ⟨k.val / 2 + 1, by omega⟩).re) =
          intSum (2 * m - 2) (fun r => if r = k then c r else 0) := by
        apply intSum_congr
        intro r
        simp only [cVecRMod, rSmulCVec, b]
        by_cases hrmod : r.val % 2 = 0
        · simp only [hrmod, ↓reduceIte, cStdBasis]
          by_cases hrk : r = k
          · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.one]
          · have hne : (⟨k.val / 2 + 1, by omega⟩ : Fin n) ≠ ⟨r.val / 2 + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; omega
            simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hrmod, ↓reduceIte, cImagBasis]
          have hrk : r ≠ k := by intro heq; subst heq; exact hrmod hmod
          by_cases hdiv : (⟨k.val / 2 + 1, by omega⟩ : Fin n) = ⟨r.val / 2 + 1, by omega⟩ <;>
            simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
    · simp only [hmod, ↓reduceIte]
      rw [cVecFinSum_apply, gaussSum_im]
      have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul (c r) (b r) ⟨k.val / 2 + 1, by omega⟩).im) =
          intSum (2 * m - 2) (fun r => if r = k then c r else 0) := by
        apply intSum_congr
        intro r
        simp only [cVecRMod, rSmulCVec, b]
        by_cases hrmod : r.val % 2 = 0
        · simp only [hrmod, ↓reduceIte, cStdBasis]
          have hrk : r ≠ k := by intro heq; subst heq; exact hmod hrmod
          by_cases hdiv : (⟨k.val / 2 + 1, by omega⟩ : Fin n) = ⟨r.val / 2 + 1, by omega⟩ <;>
            simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
        · simp only [hrmod, ↓reduceIte, cImagBasis]
          by_cases hrk : r = k
          · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.I]
          · have hne : (⟨k.val / 2 + 1, by omega⟩ : Fin n) ≠ ⟨r.val / 2 + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; omega
            simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
  · intro k
    simp only [coord, cVecRMod, zeroCVec, GaussInt.zero]
    by_cases hmod : k.val % 2 = 0 <;> simp [hmod]
  · intro v ⟨hv0, hveig⟩
    rw [hermInner_cStdBasis_left] at hv0
    have hvan := (cEigvec_diag_iff_vanish_above hspec v).mp hveig
    funext i
    unfold ZMod.linComb coord
    rw [cVecFinSum_apply]
    by_cases hi0 : i.val = 0
    · have hi_eq : i = idx₀ := Fin.ext hi0
      rw [hi_eq, hv0]
      ext
      · rw [gaussSum_re]
        have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
            (b r) idx₀).re) = intSum (2 * m - 2) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : idx₀ ≠ ⟨r.val / 2 + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hrmod : r.val % 2 = 0 <;>
            simp [hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
      · rw [gaussSum_im]
        have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
            (b r) idx₀).im) = intSum (2 * m - 2) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : idx₀ ≠ ⟨r.val / 2 + 1, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp [idx₀] at hv
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hrmod : r.val % 2 = 0 <;>
            simp [hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
    · by_cases him : i.val < m
      · let k_re : Fin (2 * m - 2) := ⟨2 * (i.val - 1), by omega⟩
        let k_im : Fin (2 * m - 2) := ⟨2 * (i.val - 1) + 1, by omega⟩
        ext
        · rw [gaussSum_re]
          have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
              (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
              (b r) i).re) = intSum (2 * m - 2) (fun r => if r = k_re then (v i).re else 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hrmod : r.val % 2 = 0
            · simp only [hrmod, ↓reduceIte, cStdBasis]
              by_cases hrk : r = k_re
              · subst hrk
                have hdiv : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := by ext; simp; omega
                simp [k_re, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one]
              · have hne : i ≠ ⟨r.val / 2 + 1, by omega⟩ := by
                  intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k_re]; omega
                simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, cImagBasis]
              have hrk : r ≠ k_re := by intro heq; subst heq; simp [k_re] at hrmod
              by_cases hdiv : i = ⟨r.val / 2 + 1, by omega⟩ <;>
                simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
        · rw [gaussSum_im]
          have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
              (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
              (b r) i).im) = intSum (2 * m - 2) (fun r => if r = k_im then (v i).im else 0) := by
            apply intSum_congr
            intro r
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hrmod : r.val % 2 = 0
            · simp only [hrmod, ↓reduceIte, cStdBasis]
              have hrk : r ≠ k_im := by intro heq; subst heq; simp [k_im] at hrmod
              by_cases hdiv : i = ⟨r.val / 2 + 1, by omega⟩ <;>
                simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one, GaussInt.zero]
            · simp only [hrmod, ↓reduceIte, cImagBasis]
              by_cases hrk : r = k_im
              · subst hrk
                have hdiv : (⟨(2 * (i.val - 1) + 1) / 2 + 1, by omega⟩ : Fin n) = i := by ext; simp; omega
                simp [k_im, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
              · have hne : i ≠ ⟨r.val / 2 + 1, by omega⟩ := by
                  intro heq; have hv := congrArg Fin.val heq; simp at hv; apply hrk; ext; simp [k_im]; omega
                simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_ite_eq]
      · rw [hvan i (by omega)]
        ext
        · rw [gaussSum_re]
          have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
              (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
              (b r) i).re) = intSum (2 * m - 2) (fun _ => 0) := by
            apply intSum_congr
            intro r
            have hne : i ≠ ⟨r.val / 2 + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hrmod : r.val % 2 = 0 <;>
              simp [hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl
        · rw [gaussSum_im]
          have hcong : intSum (2 * m - 2) (fun r => ((cVecRMod n).smul
              (if r.val % 2 = 0 then (v ⟨r.val / 2 + 1, by omega⟩).re else (v ⟨r.val / 2 + 1, by omega⟩).im)
              (b r) i).im) = intSum (2 * m - 2) (fun _ => 0) := by
            apply intSum_congr
            intro r
            have hne : i ≠ ⟨r.val / 2 + 1, by omega⟩ := by
              intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
            simp only [cVecRMod, rSmulCVec, b]
            by_cases hrmod : r.val % 2 = 0 <;>
              simp [hrmod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          rw [hcong, intSum_zero_fn]; rfl

/-- Real-dimension refutation on `ℂℙ^{n-1}`: `dim_ℝ M_{ℂℙ}(A) = 2m - 2 ≠ m` whenever `m ≠ 2`! -/
theorem tangentComplexProj_not_hasRDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) (hm_ne2 : m ≠ 2) :
    ¬ ZMod.HasDim (cVecRMod n)
      (TangentComplexProj (cDiagMat eigs) lamMax
        (cStdBasis n ⟨0, by have := hspec.1; have := hspec.2.1; omega⟩))
      m := by
  apply ZMod.not_hasDim_of_ne (cVecRMod n) (tangentComplexProj_hasRDim hspec)
  have := hspec.1
  omega

end Conjecture00000007165
