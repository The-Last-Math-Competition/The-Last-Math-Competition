import Conjecture00000004759.FockModel

/-
  Conjecture 00000004759 — Universal No-Go Theorem Against Un-Nested Block-Product Weightings
  Core Lean 4.19.0 (zero external dependencies).

  Even when full `B`-insertions `(B₁, B₂, B₃) ∈ M₂(ℤ)³` and the full covariance map
  `η_swap(B) = diag(b₂₂, b₁₁)` are known:
  1. `opXswap` realizes `E(X_swap · ι(B) · X_swap) = η_swap(B)` exactly on `Mat2 FockOp`.
  2. At `(E₁₂, E₁₁, E₂₁)`, `E₁₂ E₁₁ E₂₁ = 0`, `η_swap(E₁₂) = η_swap(E₂₁) = 0`, and EVERY
     linear combination of all 13 order-preserving un-nested trilinear patterns has
     `(2, 2)`-entry `0`, whereas `E(X_swap E₁₂ X_swap E₁₁ X_swap E₂₁ X_swap) = E₂₂ ≠ 0`.
  3. Across ALL `6 × 13 = 78` un-nested trilinear operators (allowing arbitrary permutations
     of `(B₁, B₂, B₃)` and arbitrary single-layer `η_swap` placements), our explicit 12-term
     `±1` separating functional `phiAll` vanishes identically on their entire `ℤ`-linear span
     while evaluating to `1` on BOTH `(B₁, B₂, B₃) ↦ η_swap(B₁ η_swap(B₂) B₃)` and the full
     fourth moment map `(B₁, B₂, B₃) ↦ E(X_swap B₁ X_swap B₂ X_swap B₃ X_swap)`.
  4. Moreover, for `B`-free `X₁ = E₁₁ ⊗ s₀` and `Y₁ = E₂₂ ⊗ s₁` at `(E₂₁, E₁₁, E₁₂)`, BOTH
     pure fourth moments vanish (`0`), all flat pairings vanish (`0`), yet the convolution
     fourth moment equals `E₂₂ ≠ 0` (`pure_moments_vanish_yet_conv_nonzero`).
-/

namespace Conjecture00000004759

/-- Diagonal-swapping completely positive covariance map `η_swap(B) = diag(b₂₂, b₁₁)`. -/
def etaSwap (B : Mat2 Int) : Mat2 Int := ⟨B.a22, 0, 0, B.a11⟩

/-- Self-adjoint Fock realization `X_swap = (E₁₂ ⊗ ℓ₀ + E₂₁ ⊗ ℓ₀^*) + (E₂₁ ⊗ ℓ₁ + E₁₂ ⊗ ℓ₁^*)`. -/
def opXswap : Mat2 FockOp :=
  ⟨0, FockOp.annihilateOp false + FockOp.createOp true,
   FockOp.createOp false + FockOp.annihilateOp true, 0⟩

theorem opXswap_covariance (B : Mat2 Int) :
    mat2FockSpace.exp (opXswap * iotaMat2Fock B * opXswap) = etaSwap B := by
  have hL : FockOp.phi ((FockOp.annihilateOp false + FockOp.createOp true) * FockOp.constOp B.a22 *
      (FockOp.createOp false + FockOp.annihilateOp true)) = B.a22 := by
    let A := FockOp.annihilateOp false + FockOp.createOp true
    let C := FockOp.createOp false + FockOp.annihilateOp true
    have hAC : (A * FockOp.constOp B.a22 * C).fn vacVec [] = B.a22 * (A * C).fn vacVec [] := by
      have hm := congrFun (A.map_smul B.a22 (C.fn vacVec)) []
      exact hm
    have hval : (A * C).fn vacVec [] = 1 := rfl
    change (A * FockOp.constOp B.a22 * C).fn vacVec [] = B.a22
    rw [hAC, hval, Int.mul_one]
  have hR : FockOp.phi ((FockOp.createOp false + FockOp.annihilateOp true) * FockOp.constOp B.a11 *
      (FockOp.annihilateOp false + FockOp.createOp true)) = B.a11 := by
    let A := FockOp.annihilateOp false + FockOp.createOp true
    let C := FockOp.createOp false + FockOp.annihilateOp true
    have hCA : (C * FockOp.constOp B.a11 * A).fn vacVec [] = B.a11 * (C * A).fn vacVec [] :=
      congrFun (C.map_smul B.a11 (A.fn vacVec)) []
    have hval : (C * A).fn vacVec [] = 1 := rfl
    change (C * FockOp.constOp B.a11 * A).fn vacVec [] = B.a11
    rw [hCA, hval, Int.mul_one]
  have hOff1 : FockOp.phi ((FockOp.annihilateOp false + FockOp.createOp true) * FockOp.constOp B.a21 *
      (FockOp.annihilateOp false + FockOp.createOp true)) = 0 := by
    let A := FockOp.annihilateOp false + FockOp.createOp true
    have hAA : (A * FockOp.constOp B.a21 * A).fn vacVec [] = B.a21 * (A * A).fn vacVec [] :=
      congrFun (A.map_smul B.a21 (A.fn vacVec)) []
    have hval : (A * A).fn vacVec [] = 0 := rfl
    change (A * FockOp.constOp B.a21 * A).fn vacVec [] = 0
    rw [hAA, hval, Int.mul_zero]
  have hOff2 : FockOp.phi ((FockOp.createOp false + FockOp.annihilateOp true) * FockOp.constOp B.a12 *
      (FockOp.createOp false + FockOp.annihilateOp true)) = 0 := by
    let C := FockOp.createOp false + FockOp.annihilateOp true
    have hCC : (C * FockOp.constOp B.a12 * C).fn vacVec [] = B.a12 * (C * C).fn vacVec [] :=
      congrFun (C.map_smul B.a12 (C.fn vacVec)) []
    have hval : (C * C).fn vacVec [] = 0 := rfl
    change (C * FockOp.constOp B.a12 * C).fn vacVec [] = 0
    rw [hCC, hval, Int.mul_zero]
  have hexp : opXswap * iotaMat2Fock B * opXswap =
      ⟨(FockOp.annihilateOp false + FockOp.createOp true) * FockOp.constOp B.a22 *
          (FockOp.createOp false + FockOp.annihilateOp true),
       (FockOp.annihilateOp false + FockOp.createOp true) * FockOp.constOp B.a21 *
          (FockOp.annihilateOp false + FockOp.createOp true),
       (FockOp.createOp false + FockOp.annihilateOp true) * FockOp.constOp B.a12 *
          (FockOp.createOp false + FockOp.annihilateOp true),
       (FockOp.createOp false + FockOp.annihilateOp true) * FockOp.constOp B.a11 *
          (FockOp.annihilateOp false + FockOp.createOp true)⟩ := by
    have hm1 (X Y : Mat2 FockOp) : X * Y = Mat2.mulMat X Y := rfl
    rw [hm1 (opXswap * iotaMat2Fock B) opXswap, hm1 opXswap (iotaMat2Fock B)]
    apply Mat2.ext <;> simp [opXswap, iotaMat2Fock, Mat2.mulMat, mul_zero_ring, zero_mul_ring,
      add_zero_ring, zero_add_ring]
  rw [hexp]
  apply Mat2.ext
  · exact hL
  · exact hOff1
  · exact hOff2
  · exact hR

/-- Fourth-moment evaluation `μ₄^{X_swap}(B₁, B₂, B₃) = E(X_swap B₁ X_swap B₂ X_swap B₃ X_swap)`. -/
def mu4Xswap (B₁ B₂ B₃ : Mat2 Int) : Mat2 Int :=
  mat2FockSpace.exp
    (opXswap * iotaMat2Fock B₁ * opXswap * iotaMat2Fock B₂ * opXswap * iotaMat2Fock B₃ * opXswap)

/-- Nested rainbow block contribution `T_nest(B₁, B₂, B₃) = η_swap(B₁ η_swap(B₂) B₃)`. -/
def nestedRainbowSwap (B₁ B₂ B₃ : Mat2 Int) : Mat2 Int :=
  etaSwap (B₁ * etaSwap B₂ * B₃)

theorem mu4Xswap_at_E12_E11_E21 :
    mu4Xswap Mat2.E12 Mat2.E11 Mat2.E21 = Mat2.E22 ∧
    (Mat2.E12 : Mat2 Int) * Mat2.E11 * Mat2.E21 = 0 ∧
    etaSwap Mat2.E12 = 0 ∧
    etaSwap Mat2.E21 = 0 := by
  refine ⟨by ext <;> rfl, by ext <;> rfl, by ext <;> rfl, by ext <;> rfl⟩

/-! ### All `6 × 13 = 78` Un-Nested Trilinear Operators -/

/-- All 6 permutations of `(B₁, B₂, B₃)`. -/
inductive Perm3 where
  | p012 | p021 | p102 | p120 | p201 | p210
  deriving DecidableEq, Repr

def applyPerm3 : Perm3 → Mat2 Int → Mat2 Int → Mat2 Int → (Mat2 Int × Mat2 Int × Mat2 Int)
  | .p012, b₀, b₁, b₂ => (b₀, b₁, b₂)
  | .p021, b₀, b₁, b₂ => (b₀, b₂, b₁)
  | .p102, b₀, b₁, b₂ => (b₁, b₀, b₂)
  | .p120, b₀, b₁, b₂ => (b₁, b₂, b₀)
  | .p201, b₀, b₁, b₂ => (b₂, b₀, b₁)
  | .p210, b₀, b₁, b₂ => (b₂, b₁, b₀)

/-- All 13 non-nested `η`-placement templates on an ordered triple `(x, y, z)`.
    Every contiguous group wrapped in `η(...)` has depth 1 (no `η` sits inside another `η`). -/
inductive UnnestedPat where
  | bare           -- x * y * z
  | eta1           -- η(x) * y * z
  | eta2           -- x * η(y) * z
  | eta3           -- x * y * η(z)
  | eta12_sep      -- η(x) * η(y) * z
  | eta13_sep      -- η(x) * y * η(z)   [flat pairing {{1,2},{3,4}}!]
  | eta23_sep      -- x * η(y) * η(z)
  | eta123_sep     -- η(x) * η(y) * η(z)
  | eta12_join     -- η(x * y) * z
  | eta12_eta3     -- η(x * y) * η(z)
  | eta23_join     -- x * η(y * z)
  | eta1_eta23     -- η(x) * η(y * z)
  | eta123_join    -- η(x * y * z)
  deriving DecidableEq, Repr

def evalUnnested (σ : Perm3) (pat : UnnestedPat) (η : Mat2 Int → Mat2 Int)
    (b₀ b₁ b₂ : Mat2 Int) : Mat2 Int :=
  let (x, y, z) := applyPerm3 σ b₀ b₁ b₂
  match pat with
  | .bare        => x * y * z
  | .eta1        => η x * y * z
  | .eta2        => x * η y * z
  | .eta3        => x * y * η z
  | .eta12_sep   => η x * η y * z
  | .eta13_sep   => η x * y * η z
  | .eta23_sep   => x * η y * η z
  | .eta123_sep  => η x * η y * η z
  | .eta12_join  => η (x * y) * z
  | .eta12_eta3  => η (x * y) * η z
  | .eta23_join  => x * η (y * z)
  | .eta1_eta23  => η x * η (y * z)
  | .eta123_join => η (x * y * z)

def scaleMat2 (c : Int) (M : Mat2 Int) : Mat2 Int :=
  ⟨c * M.a11, c * M.a12, c * M.a21, c * M.a22⟩

/-- Arbitrary `ℤ`-linear combination of the 78 un-nested trilinear operators. -/
abbrev UnnestedComb := List (Int × Perm3 × UnnestedPat)

def evalUnnestedComb (cs : UnnestedComb) (η : Mat2 Int → Mat2 Int)
    (b₀ b₁ b₂ : Mat2 Int) : Mat2 Int :=
  match cs with
  | [] => 0
  | (c, σ, pat) :: rest =>
      scaleMat2 c (evalUnnested σ pat η b₀ b₁ b₂) + evalUnnestedComb rest η b₀ b₁ b₂

/-! ### 1-Term Separating Functional for All 13 Order-Preserving Un-Nested Operators -/

def phiOrd (F : Mat2 Int → Mat2 Int → Mat2 Int → Mat2 Int) : Int :=
  (F Mat2.E12 Mat2.E11 Mat2.E21).a22

theorem phiOrd_unnested_id_zero (pat : UnnestedPat) :
    phiOrd (evalUnnested Perm3.p012 pat etaSwap) = 0 := by
  cases pat <;> rfl

theorem phiOrd_comb_id_zero :
    ∀ cs : List (Int × UnnestedPat),
      phiOrd (evalUnnestedComb (cs.map fun (c, p) => (c, Perm3.p012, p)) etaSwap) = 0
  | [] => rfl
  | (c, p) :: rest => by
      have hp := phiOrd_unnested_id_zero p
      have ih := phiOrd_comb_id_zero rest
      change c * phiOrd (evalUnnested Perm3.p012 p etaSwap) +
        phiOrd (evalUnnestedComb (rest.map fun (c, p) => (c, Perm3.p012, p)) etaSwap) = 0
      rw [hp, ih]; omega

/-! ### 12-Term `±1` Separating Functional Across ALL 78 Permuted Un-Nested Operators -/

def phiAll (F : Mat2 Int → Mat2 Int → Mat2 Int → Mat2 Int) : Int :=
    (F Mat2.E11 Mat2.E11 Mat2.E12).a12
  + (F Mat2.E11 Mat2.E11 Mat2.E21).a21
  + (F Mat2.E11 Mat2.E11 Mat2.E22).a11
  - (F Mat2.E11 Mat2.E11 Mat2.E22).a22
  - (F Mat2.E11 Mat2.E12 Mat2.E11).a12
  - (F Mat2.E11 Mat2.E12 Mat2.E22).a12
  - (F Mat2.E11 Mat2.E21 Mat2.E11).a21
  - (F Mat2.E11 Mat2.E21 Mat2.E22).a21
  - (F Mat2.E11 Mat2.E22 Mat2.E11).a11
  + (F Mat2.E11 Mat2.E22 Mat2.E11).a22
  + (F Mat2.E11 Mat2.E22 Mat2.E12).a12
  + (F Mat2.E11 Mat2.E22 Mat2.E21).a21

theorem phiAll_zero_op : phiAll (fun _ _ _ => (0 : Mat2 Int)) = 0 := rfl

theorem phiAll_add_scale (c : Int) (F G : Mat2 Int → Mat2 Int → Mat2 Int → Mat2 Int) :
    phiAll (fun b₀ b₁ b₂ => scaleMat2 c (F b₀ b₁ b₂) + G b₀ b₁ b₂) =
      c * phiAll F + phiAll G := by
  have h11 (M N : Mat2 Int) : (scaleMat2 c M + N).a11 = c * M.a11 + N.a11 := rfl
  have h12 (M N : Mat2 Int) : (scaleMat2 c M + N).a12 = c * M.a12 + N.a12 := rfl
  have h21 (M N : Mat2 Int) : (scaleMat2 c M + N).a21 = c * M.a21 + N.a21 := rfl
  have h22 (M N : Mat2 Int) : (scaleMat2 c M + N).a22 = c * M.a22 + N.a22 := rfl
  unfold phiAll
  simp only [h11, h12, h21, h22, Int.mul_add, Int.mul_sub]
  omega

theorem phiAll_unnested_zero (σ : Perm3) (pat : UnnestedPat) :
    phiAll (evalUnnested σ pat etaSwap) = 0 := by
  cases σ <;> cases pat <;> rfl

theorem phiAll_comb_zero :
    ∀ cs : UnnestedComb, phiAll (evalUnnestedComb cs etaSwap) = 0
  | [] => rfl
  | (c, σ, pat) :: rest => by
      change phiAll (fun b₀ b₁ b₂ =>
        scaleMat2 c (evalUnnested σ pat etaSwap b₀ b₁ b₂) +
          evalUnnestedComb rest etaSwap b₀ b₁ b₂) = 0
      rw [phiAll_add_scale, phiAll_unnested_zero σ pat, phiAll_comb_zero rest]
      omega

theorem phiAll_nestedRainbowSwap : phiAll nestedRainbowSwap = 1 := rfl

theorem phiAll_mu4Xswap : phiAll mu4Xswap = 1 := rfl

/-- Universal Impossibility Theorem: NO `ℤ`-linear combination of ALL 78 un-nested trilinear
    operators (across all 6 input permutations and all 13 depth-1 `η`-patterns) can equal
    either the nested rainbow block operator `η_swap(B₁ η_swap(B₂) B₃)` or the fourth moment
    map `μ₄^{X_swap}(B₁, B₂, B₃)`! -/
theorem no_unnested_weighted_count_all78 (cs : UnnestedComb) :
    evalUnnestedComb cs etaSwap ≠ nestedRainbowSwap ∧
    evalUnnestedComb cs etaSwap ≠ mu4Xswap := by
  have h0 := phiAll_comb_zero cs
  constructor
  · intro heq
    have h1 : phiAll (evalUnnestedComb cs etaSwap) = phiAll nestedRainbowSwap := congrArg phiAll heq
    rw [h0, phiAll_nestedRainbowSwap] at h1
    omega
  · intro heq
    have h1 : phiAll (evalUnnestedComb cs etaSwap) = phiAll mu4Xswap := congrArg phiAll heq
    rw [h0, phiAll_mu4Xswap] at h1
    omega

/-! ### Pure-Component Vanishing Convolution Witness (`X₁ = E₁₁ ⊗ s₀`, `Y₁ = E₂₂ ⊗ s₁`) -/

def opX1 : Mat2 FockOp := ⟨FockOp.semiOp false, 0, 0, 0⟩
def opY1 : Mat2 FockOp := ⟨0, 0, 0, FockOp.semiOp true⟩

theorem opX1_in_false : InMat2Color false opX1 :=
  ⟨FockOp.inColor_semiOp false, FockOp.InColor.const 0,
   FockOp.InColor.const 0, FockOp.InColor.const 0⟩

theorem opY1_in_true : InMat2Color true opY1 :=
  ⟨FockOp.InColor.const 0, FockOp.InColor.const 0,
   FockOp.InColor.const 0, FockOp.inColor_semiOp true⟩

theorem pure_moments_vanish_yet_conv_nonzero :
    mat2FockSpace.exp (opX1 * iotaMat2Fock Mat2.E21 * opX1 * iotaMat2Fock Mat2.E11 *
      opX1 * iotaMat2Fock Mat2.E12 * opX1) = 0 ∧
    mat2FockSpace.exp (opY1 * iotaMat2Fock Mat2.E21 * opY1 * iotaMat2Fock Mat2.E11 *
      opY1 * iotaMat2Fock Mat2.E12 * opY1) = 0 ∧
    mat2FockSpace.exp ((opX1 + opY1) * iotaMat2Fock Mat2.E21 * (opX1 + opY1)) = 0 ∧
    mat2FockSpace.exp ((opX1 + opY1) * iotaMat2Fock Mat2.E12 * (opX1 + opY1)) = 0 ∧
    mat2FockSpace.exp ((opX1 + opY1) * iotaMat2Fock Mat2.E21 * (opX1 + opY1) *
      iotaMat2Fock Mat2.E11 * (opX1 + opY1) * iotaMat2Fock Mat2.E12 * (opX1 + opY1)) = Mat2.E22 := by
  refine ⟨by ext <;> rfl, by ext <;> rfl, by ext <;> rfl, by ext <;> rfl, by ext <;> rfl⟩

end Conjecture00000004759
