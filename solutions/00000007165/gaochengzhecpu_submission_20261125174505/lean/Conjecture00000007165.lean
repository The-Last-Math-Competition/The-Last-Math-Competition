/-
  Conjecture 00000007165 — Top-Level Positive & Master Disproof Theorems
  Core Lean 4.19.0 (zero external dependencies, `-DwarningAsError=true`).

  Conjecture Statement (`SOURCE.md`):
    "Definition: The spectrum of the Rayleigh quotient with the extremal faces of the quotient.
     Conjecture: The contact manifolds of extremal faces hold, and the dimension of the
     manifolds is the multiplicity of the index. (index-multiplicity Rayleigh contact manifolds)"

  Resolution Summary:
  1. `positive_linear_cone_characterization` (Non-Vacuity):
     For any symmetric / Hermitian matrix with maximum eigenvalue `lamMax` of multiplicity `m ≥ 1`,
     `R_A(x) ≤ lamMax` and `R_A(x) = lamMax ↔ A x = lamMax • x`. Adjoining `0 ∉ dom(R_A)`, the
     unnormalized linear cone `ker(A - lamMax I)` has exact `𝔽`-dimension `m` (though real
     dimension `2m ≠ m` over `ℂ`).
  2. `conjecture_00000007165_disproved` (Master Refutation Across All Normalized State Domains
     and Matrix Classes):
     - Domain 1 (`S^{n-1}`): `dim_ℝ M_{ℝ,S}(A) = m - 1 ≠ m` for ALL `m ≥ 1` (`S^0` pair at `m = 1`).
     - Domain 2 (`ℝℙ^{n-1}`): `dim_ℝ M_{ℝℙ}(A) = m - 1 ≠ m` for ALL `m ≥ 1` (singleton at `m = 1`).
     - Domain 3 (`S^{2n-1}`): strict contact submanifold `(S^{2m-1}, Im⟨z, dz⟩)` of exact
       `dim_ℝ = 2m - 1 ≠ m` for ALL `m ≥ 2` (plus odd-dimension parity obstruction for all even `m`).
     - Domain 4 (`ℂℙ^{n-1}`): `dim_ℂ = m - 1 ≠ m` for ALL `m ≥ 1`, and `dim_ℝ = 2m - 2 ≠ m`
       for ALL `m ≠ 2` (singleton at `m = 1`, `4 ≠ 3` at `m = 3`).
     - Domain 5 (`𝒟_n(ℂ)` & `𝒟_n(ℝ)`): exact bilateral tangent face dimension `m² - 1 ≠ m` for
       ALL `m ≥ 1` over `ℂ`, and `m(m+1)/2 - 1 ≠ m` for `m = 1` and ALL `m ≥ 3` over `ℝ`.
     - Non-normal, joint numerical-range extremal face, and interior-eigenvalue singularity
       obstructions all hold unconditionally.
-/

import Conjecture00000007165.ModuleDim
import Conjecture00000007165.RayleighSpectrum
import Conjecture00000007165.ContactDomains
import Conjecture00000007165.DensityAndObstructions

namespace Conjecture00000007165

/-- **Positive Non-Vacuity Theorem (Unnormalized Linear Cone):**
    For every `1 ≤ m ≤ n` and every ordered spectrum `eigs` whose maximum `lamMax` has
    multiplicity `m`, `R_A(x) = lamMax ↔ A x = lamMax • x`, and the linear eigenspace
    has exact `𝔽`-dimension `m` (while over `ℂ` its real dimension is `2m ≠ m`). -/
theorem positive_linear_cone_characterization {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    (∀ (x : Vec n) (hx : x ≠ zeroVec n),
      RatVal.Le (rayleigh (diagMat eigs) x hx) (RatVal.ofInt lamMax) ∧
      (RatVal.Eq (rayleigh (diagMat eigs) x hx) (RatVal.ofInt lamMax) ↔
        RealEigenspace (diagMat eigs) lamMax x)) ∧
    ZMod.HasDim (vecZMod n) (RealEigenspace (diagMat eigs) lamMax) m ∧
    CMod.HasCDim (cVecCMod n) (ComplexEigenspace (cDiagMat eigs) lamMax) m ∧
    ZMod.HasDim (cVecRMod n) (ComplexEigenspace (cDiagMat eigs) lamMax) (2 * m) ∧
    ¬ ZMod.HasDim (cVecRMod n) (ComplexEigenspace (cDiagMat eigs) lamMax) m := by
  refine ⟨fun x hx => ⟨rayleigh_le_max hspec hx, rayleigh_eq_max_iff_eigvec hspec hx⟩,
          realEigenspace_hasDim_m hspec,
          complexEigenspace_hasCDim_m hspec,
          complexEigenspace_hasRDim_two_m hspec,
          ZMod.not_hasDim_of_ne (cVecRMod n) (complexEigenspace_hasRDim_two_m hspec) ?_⟩
  have := hspec.1
  omega

/-- Concrete spectrum `modelEigs n m`: maximum eigenvalue `2` with multiplicity `m`, remaining `1`. -/
def modelEigs (n m : Nat) : Fin n → Int :=
  fun i => if i.val < m then 2 else 1

theorem modelEigs_hasMaxMult {n m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    HasMaxMult (modelEigs n m) 2 m := by
  refine ⟨hm1, hmn, ?_, ?_⟩
  · intro i hi; simp [modelEigs, hi]
  · intro i hi; have hnot : ¬ (i.val < m) := by omega
    simp [modelEigs, hnot]

/-- **Master Universal Refutation of Conjecture 00000007165:**
    Across every normalized domain (`S^{n-1}`, `ℝℙ^{n-1}`, `S^{2n-1}`, `ℂℙ^{n-1}`, `𝒟_n(ℂ)`, `𝒟_n(ℝ)`)
    and across non-normal matrices, joint numerical range faces, and interior indices, the
    contact manifold dimension fails to equal the index multiplicity `m`. -/
theorem conjecture_00000007165_disproved :
    -- (1) Domain 1 (`S^{n-1}`) & Domain 2 (`ℝℙ^{n-1}`): fails for EVERY `1 ≤ m ≤ n` (`m - 1 ≠ m`)
    (∀ (n m : Nat) (_hm1 : 1 ≤ m) (_hmn : m ≤ n),
      ZMod.HasDim (vecZMod n)
        (TangentRealSphere (diagMat (modelEigs n m)) 2 (stdBasis n ⟨0, by omega⟩)) (m - 1) ∧
      ¬ ZMod.HasDim (vecZMod n)
        (TangentRealSphere (diagMat (modelEigs n m)) 2 (stdBasis n ⟨0, by omega⟩)) m ∧
      ¬ ZMod.HasDim (vecZMod n)
        (TangentRealProj (diagMat (modelEigs n m)) 2 (stdBasis n ⟨0, by omega⟩)) m) ∧
    -- (2) Domain 3 (`S^{2n-1}`): strict contact manifold of dim `2m - 1 ≠ m` for EVERY `2 ≤ m ≤ n`
    (∀ (n m : Nat) (_hm2 : 2 ≤ m) (_hmn : m ≤ n),
      ZMod.HasDim (cVecRMod n)
        (TangentComplexSphere (cDiagMat (modelEigs n m)) 2 (cStdBasis n ⟨0, by omega⟩)) (2 * m - 1) ∧
      ¬ ZMod.HasDim (cVecRMod n)
        (TangentComplexSphere (cDiagMat (modelEigs n m)) 2 (cStdBasis n ⟨0, by omega⟩)) m) ∧
    -- (3) Domain 4 (`ℂℙ^{n-1}`): complex dim `m - 1 ≠ m` for ALL `m ≥ 1`; real dim `2m - 2 ≠ m` for ALL `m ≠ 2`
    (∀ (n m : Nat) (_hm1 : 1 ≤ m) (_hmn : m ≤ n),
      ¬ CMod.HasCDim (cVecCMod n)
        (TangentComplexProj (cDiagMat (modelEigs n m)) 2 (cStdBasis n ⟨0, by omega⟩)) m ∧
      (m ≠ 2 → ¬ ZMod.HasDim (cVecRMod n)
        (TangentComplexProj (cDiagMat (modelEigs n m)) 2 (cStdBasis n ⟨0, by omega⟩)) m)) ∧
    -- (4) Domain 5 (`𝒟_n(ℂ)` and `𝒟_n(ℝ)`): `m² - 1 ≠ m` for ALL `m ≥ 1`; `m(m+1)/2 - 1 ≠ m` for `m ≠ 2`
    (∀ (n m : Nat) (_hm1 : 1 ≤ m) (_hmn : m ≤ n),
      (∀ H : Mat n, IsRealFaceTangent (diagMat (modelEigs n m)) 2 m H ↔ TracelessSymBlock n m H) ∧
      ZMod.HasDim (cMatRMod n) (TracelessHermBlock n m) (m * m - 1) ∧
      ¬ ZMod.HasDim (cMatRMod n) (TracelessHermBlock n m) m ∧
      (m ≠ 2 → ¬ ZMod.HasDim (matZMod n) (TracelessSymBlock n m) m)) ∧
    -- (5) Non-normal matrix, joint extremal face, and interior singular level set obstructions
    ((∀ mu : Int, charPoly2 nonNormalA mu = mu * mu) ∧
     (∀ (x : Vec 2) (hx : x ≠ zeroVec 2),
       RatVal.Eq (rayleigh nonNormalA x hx) (RatVal.ofInt 1) ↔ ProjEquiv x diagVec11)) ∧
    (HasMaxMult jointSupportEigs 1 3 ∧
     ¬ ZMod.HasDim (vecZMod 4) (TangentRealSphere (diagMat jointSupportEigs) 1 (stdBasis 4 ⟨0, by omega⟩)) 3) ∧
    (ZMod.HasDim (vecZMod 3) (RealEigenspace interiorA3 0) 1 ∧
     ZMod.HasDim (vecZMod 3) (InteriorLevelZariski pSing3) 2 ∧
     ZMod.HasDim (vecZMod 3) (InteriorLevelZariski qReg3) 1 ∧
     ¬ ZMod.HasDim (vecZMod 3) (InteriorLevelZariski pSing3) 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hm1 hmn
    have hspec := modelEigs_hasMaxMult hm1 hmn
    exact ⟨tangentRealSphere_hasDim hspec,
           tangentRealSphere_not_hasDim_m hspec,
           tangentRealProj_not_hasDim_m hspec⟩
  · intro n m hm2 hmn
    have hspec := modelEigs_hasMaxMult (by omega : 1 ≤ m) hmn
    exact ⟨tangentComplexSphere_hasDim hspec,
           tangentComplexSphere_not_hasDim_m hspec hm2⟩
  · intro n m hm1 hmn
    have hspec := modelEigs_hasMaxMult hm1 hmn
    exact ⟨tangentComplexProj_not_hasCDim_m hspec,
           fun hne2 => tangentComplexProj_not_hasRDim_m hspec hne2⟩
  · intro n m hm1 hmn
    have hspec := modelEigs_hasMaxMult hm1 hmn
    exact ⟨isRealFaceTangent_iff_tracelessSymBlock hspec,
           tracelessHermBlock_hasDim hm1 hmn,
           tracelessHermBlock_not_hasDim_m hm1 hmn,
           fun hne2 => tracelessSymBlock_not_hasDim_m hm1 hmn hne2⟩
  · exact ⟨nonNormal_counterexample.1, fun x hx => (nonNormal_counterexample.2.2 x hx).2⟩
  · exact ⟨joint_extremal_face_obstruction.1, joint_extremal_face_obstruction.2.2.1⟩
  · exact ⟨interior_eigenvalue_level_set_singular.1,
           interior_eigenvalue_level_set_singular.2.2.2.1,
           interior_eigenvalue_level_set_singular.2.2.2.2.1,
           interior_eigenvalue_level_set_singular.2.2.2.2.2⟩

end Conjecture00000007165
