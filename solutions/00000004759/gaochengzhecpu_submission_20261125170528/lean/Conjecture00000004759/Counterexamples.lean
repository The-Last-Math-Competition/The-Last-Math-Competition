import Conjecture00000004759.FockModel

/-
  Conjecture 00000004759 — Explicit Counterexamples to Moment/Cumulant Weighted-Count Convolutions
  Core Lean 4.19.0 (zero external dependencies).

  Establishes:
  1. `opX = I₂ ⊗ s₀` and `opXtilde = σ_x ⊗ s₀` have IDENTICAL un-inserted `B`-valued power
     moments `E(X^k) = E(X̃^k)` for ALL `k : Nat` (`all_power_moments_eq`).
  2. Yet with `Y_det = ι(E₁₁)` (`B`-free from both `X` and `X̃`), additive convolution agrees at
     `n = 1, 2` (depth 1) and FAILS at `n = 3` (nesting depth 2, minimal nested order):
       `E((X + Y_det)^3) = diag(4, 0) ≠ diag(3, 1) = E((X̃ + Y_det)^3)`,
     while multiplicative convolution FAILS already at `n = 2`:
       `E((X · Y_det)^2) = E₁₁ ≠ 0 = E((X̃ · Y_det)^2)`.
  3. With strictly centered `Y_semi = E₁₁ ⊗ s₁` (`B`-free to all orders from both `X` and `X̃`),
     additive convolution agrees at `n = 1, 2, 3` and FAILS at `n = 4` (depth 2):
       `E((X + Y_semi)^4) = diag(8, 2) ≠ diag(7, 3) = E((X̃ + Y_semi)^4)`,
     and at `n = 6` (depth 3):
       `E((X + Y_semi)^6) = diag(40, 5) ≠ diag(30, 12) = E((X̃ + Y_semi)^6)`.
  4. Therefore NO function of the single-variable moment sequences `{E(U^k), E(V^k)}_{k ∈ ℕ}` —
     in particular, NO scalar-weighted or `B`-weighted count over `NC(n)` formed from block
     moments or un-inserted cumulants — can compute operator-valued free convolution!
-/

namespace Conjecture00000004759

def opX : Mat2 FockOp := ⟨FockOp.semiOp false, 0, 0, FockOp.semiOp false⟩
def opXtilde : Mat2 FockOp := ⟨0, FockOp.semiOp false, FockOp.semiOp false, 0⟩
def opYdet : Mat2 FockOp := iotaMat2Fock Mat2.E11
def opYsemi : Mat2 FockOp := ⟨FockOp.semiOp true, 0, 0, 0⟩

theorem opX_in_false : InMat2Color false opX :=
  ⟨FockOp.inColor_semiOp false, FockOp.InColor.const 0,
   FockOp.InColor.const 0, FockOp.inColor_semiOp false⟩

theorem opXtilde_in_false : InMat2Color false opXtilde :=
  ⟨FockOp.InColor.const 0, FockOp.inColor_semiOp false,
   FockOp.inColor_semiOp false, FockOp.InColor.const 0⟩

theorem opYsemi_in_true : InMat2Color true opYsemi :=
  ⟨FockOp.inColor_semiOp true, FockOp.InColor.const 0,
   FockOp.InColor.const 0, FockOp.InColor.const 0⟩

theorem opYdet_in_iota : IotaSubalg mat2FockSpace opYdet := ⟨Mat2.E11, rfl⟩

/-! ### Parity Vanishing of Odd Semicircular Moments & All-`k` Moment Indistinguishability -/

private theorem semiOp_parity_step (c : Bool) (p : Nat) (hp : p < 2) (v : FockVec)
    (hv : ∀ w : List Bool, w.length % 2 = p → v w = 0) :
    ∀ w : List Bool, w.length % 2 = (p + 1) % 2 → (FockOp.semiOp c).fn v w = 0 := by
  intro w hw
  have hann : v (c :: w) = 0 := by
    apply hv (c :: w)
    have hlen : (c :: w).length = w.length + 1 := rfl
    omega
  have hcre : FockOp.createFn c v w = 0 := by
    cases w with
    | nil => rfl
    | cons b ws =>
        have hws : v ws = 0 := by
          apply hv ws
          have hlen : (b :: ws).length = ws.length + 1 := rfl
          omega
        by_cases hbc : (b == c) = true <;> simp [FockOp.createFn, hbc, hws]
  change v (c :: w) + FockOp.createFn c v w = 0
  rw [hann, hcre]; rfl

private theorem semiOp_pow_parity (c : Bool) :
    ∀ (k : Nat) (w : List Bool),
      w.length % 2 = (k + 1) % 2 → (ringPow (FockOp.semiOp c) k).fn vacVec w = 0
  | 0, w, hw => by
      cases w with
      | nil => simp at hw
      | cons _ _ => rfl
  | k + 1, w, hw => by
      change (FockOp.semiOp c).fn ((ringPow (FockOp.semiOp c) k).fn vacVec) w = 0
      apply semiOp_parity_step c ((k + 1) % 2) (by omega) _ (semiOp_pow_parity c k) w
      omega

theorem phi_semiOp_odd (c : Bool) {k : Nat} (hk : k % 2 = 1) :
    FockOp.phi (ringPow (FockOp.semiOp c) k) = 0 := by
  apply semiOp_pow_parity c k []
  simp; omega

private theorem mat2_fock_mul (M N : Mat2 FockOp) :
    M * N = Mat2.mulMat M N := rfl

private theorem opX_pow_shape : ∀ k : Nat,
    ringPow opX k = ⟨ringPow (FockOp.semiOp false) k, 0, 0, ringPow (FockOp.semiOp false) k⟩
  | 0 => rfl
  | k + 1 => by
      rw [ringPow, opX_pow_shape k, mat2_fock_mul]
      apply Mat2.ext <;> simp [opX, Mat2.mulMat, ringPow, mul_zero_ring, zero_mul_ring,
        add_zero_ring, zero_add_ring]

private theorem opXtilde_pow_shape : ∀ k : Nat,
    ringPow opXtilde k =
      if k % 2 = 0 then
        ⟨ringPow (FockOp.semiOp false) k, 0, 0, ringPow (FockOp.semiOp false) k⟩
      else
        ⟨0, ringPow (FockOp.semiOp false) k, ringPow (FockOp.semiOp false) k, 0⟩
  | 0 => rfl
  | k + 1 => by
      rw [ringPow, opXtilde_pow_shape k]
      by_cases hk : k % 2 = 0
      · have hk1 : (k + 1) % 2 ≠ 0 := by omega
        simp only [hk, hk1, ite_true, ite_false]
        rw [mat2_fock_mul]
        apply Mat2.ext <;> simp [opXtilde, Mat2.mulMat, ringPow, mul_zero_ring, zero_mul_ring,
          add_zero_ring, zero_add_ring]
      · have hk1 : (k + 1) % 2 = 0 := by omega
        simp only [hk, hk1, ite_false, ite_true]
        rw [mat2_fock_mul]
        apply Mat2.ext <;> simp [opXtilde, Mat2.mulMat, ringPow, mul_zero_ring, zero_mul_ring,
          add_zero_ring, zero_add_ring]

/-- `opX` and `opXtilde` have IDENTICAL un-inserted `B`-valued moments `E(X^k) = E(X̃^k)`
    for ALL natural numbers `k ∈ ℕ`! -/
theorem all_power_moments_eq (k : Nat) :
    mat2FockSpace.exp (ringPow opX k) = mat2FockSpace.exp (ringPow opXtilde k) := by
  rw [opX_pow_shape k, opXtilde_pow_shape k]
  by_cases hk : k % 2 = 0
  · simp [hk]
  · have hodd : k % 2 = 1 := by omega
    have hphi := phi_semiOp_odd false hodd
    simp [hk, mat2FockSpace, expMat2Fock, hphi, FockOp.phi_zero]

/-! ### Disproof Witness 1: Order `n = 3` (Minimal Nesting Depth 2) & Multiplicative `n = 2` -/

theorem conv_det_n1_eq :
    mat2FockSpace.exp (opX + opYdet) = mat2FockSpace.exp (opXtilde + opYdet) := by
  ext <;> rfl

theorem conv_det_n2_eq :
    mat2FockSpace.exp (ringPow (opX + opYdet) 2) =
      mat2FockSpace.exp (ringPow (opXtilde + opYdet) 2) := by
  ext <;> rfl

theorem conv_det_n3_X :
    mat2FockSpace.exp (ringPow (opX + opYdet) 3) = Mat2.diagMat 4 0 := by
  ext <;> rfl

theorem conv_det_n3_Xtilde :
    mat2FockSpace.exp (ringPow (opXtilde + opYdet) 3) = Mat2.diagMat 3 1 := by
  ext <;> rfl

theorem conv_det_n3_ne :
    mat2FockSpace.exp (ringPow (opX + opYdet) 3) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYdet) 3) := by
  rw [conv_det_n3_X, conv_det_n3_Xtilde]
  intro h
  have h11 := congrArg Mat2.a11 h
  dsimp [Mat2.diagMat] at h11
  omega

theorem mul_conv_det_n2_ne :
    mat2FockSpace.exp (ringPow (opX * opYdet) 2) ≠
      mat2FockSpace.exp (ringPow (opXtilde * opYdet) 2) := by
  have h1 : mat2FockSpace.exp (ringPow (opX * opYdet) 2) = Mat2.E11 := by ext <;> rfl
  have h2 : mat2FockSpace.exp (ringPow (opXtilde * opYdet) 2) = 0 := by ext <;> rfl
  rw [h1, h2]
  intro h
  have h11 := congrArg Mat2.a11 h
  change (1 : Int) = 0 at h11
  omega

/-! ### Disproof Witness 2: Strictly Centered `B`-Free Semicirculars at `n = 4` and `n = 6` -/

theorem centered_opX_opXtilde_opYsemi :
    mat2FockSpace.exp opX = 0 ∧
    mat2FockSpace.exp opXtilde = 0 ∧
    mat2FockSpace.exp opYsemi = 0 := by
  refine ⟨by ext <;> rfl, by ext <;> rfl, by ext <;> rfl⟩

theorem conv_semi_n123_eq :
    mat2FockSpace.exp (ringPow (opX + opYsemi) 1) =
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 1) ∧
    mat2FockSpace.exp (ringPow (opX + opYsemi) 2) =
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 2) ∧
    mat2FockSpace.exp (ringPow (opX + opYsemi) 3) =
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 3) := by
  refine ⟨by ext <;> rfl, by ext <;> rfl, by ext <;> rfl⟩

theorem conv_semi_n4_X :
    mat2FockSpace.exp (ringPow (opX + opYsemi) 4) = Mat2.diagMat 8 2 := by
  ext <;> rfl

theorem conv_semi_n4_Xtilde :
    mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 4) = Mat2.diagMat 7 3 := by
  ext <;> rfl

theorem conv_semi_n4_ne :
    mat2FockSpace.exp (ringPow (opX + opYsemi) 4) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 4) := by
  rw [conv_semi_n4_X, conv_semi_n4_Xtilde]
  intro h
  have h11 := congrArg Mat2.a11 h
  dsimp [Mat2.diagMat] at h11
  omega

theorem conv_semi_n6_X :
    mat2FockSpace.exp (ringPow (opX + opYsemi) 6) = Mat2.diagMat 40 5 := by
  ext <;> rfl

theorem conv_semi_n6_Xtilde :
    mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 6) = Mat2.diagMat 30 12 := by
  ext <;> rfl

theorem conv_semi_n6_ne :
    mat2FockSpace.exp (ringPow (opX + opYsemi) 6) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 6) := by
  rw [conv_semi_n6_X, conv_semi_n6_Xtilde]
  intro h
  have h11 := congrArg Mat2.a11 h
  dsimp [Mat2.diagMat] at h11
  omega

/-- No universal moment-sequence convolution rule `Φ : (ℕ → B) → (ℕ → B) → B` can compute
    `E((U + V)^3)` for `B`-free pairs `(U, V)` (not even at degree/depth `≤ 3`), nor `E((U + V)^4)`
    for strictly centered `B`-free semicirculars! -/
theorem no_uninserted_moment_convolution_recursion :
    (¬ ∃ Φ₃ : (Nat → Mat2 Int) → (Nat → Mat2 Int) → Mat2 Int,
        ∀ (P₀ P₁ : Mat2 FockOp → Prop) (_ : IsBFree mat2FockSpace P₀ P₁)
          (U V : Mat2 FockOp), P₀ U → P₁ V →
          mat2FockSpace.exp (ringPow (U + V) 3) =
            Φ₃ (fun k => mat2FockSpace.exp (ringPow U k))
               (fun k => mat2FockSpace.exp (ringPow V k))) ∧
    (¬ ∃ Φ₄ : (Nat → Mat2 Int) → (Nat → Mat2 Int) → Mat2 Int,
        ∀ (P₀ P₁ : Mat2 FockOp → Prop) (_ : IsBFree mat2FockSpace P₀ P₁)
          (U V : Mat2 FockOp), P₀ U → P₁ V →
          mat2FockSpace.exp U = 0 → mat2FockSpace.exp V = 0 →
          mat2FockSpace.exp (ringPow (U + V) 4) =
            Φ₄ (fun k => mat2FockSpace.exp (ringPow U k))
               (fun k => mat2FockSpace.exp (ringPow V k))) := by
  have hseq : (fun k => mat2FockSpace.exp (ringPow opX k)) =
      (fun k => mat2FockSpace.exp (ringPow opXtilde k)) := by
    funext k; exact all_power_moments_eq k
  constructor
  · rintro ⟨Φ₃, hΦ₃⟩
    have hF := isBFree_iotaSubalg mat2FockSpace (inMat2Color_isSubalgebra false)
    have eq1 := hΦ₃ _ _ hF opX opYdet opX_in_false opYdet_in_iota
    have eq2 := hΦ₃ _ _ hF opXtilde opYdet opXtilde_in_false opYdet_in_iota
    rw [hseq] at eq1
    exact conv_det_n3_ne (eq1.trans eq2.symm)
  · rintro ⟨Φ₄, hΦ₄⟩
    have hc := centered_opX_opXtilde_opYsemi
    have eq1 := hΦ₄ _ _ mat2Fock_isBFree opX opYsemi opX_in_false opYsemi_in_true hc.1 hc.2.2
    have eq2 := hΦ₄ _ _ mat2Fock_isBFree opXtilde opYsemi opXtilde_in_false opYsemi_in_true hc.2.1 hc.2.2
    rw [hseq] at eq1
    exact conv_semi_n4_ne (eq1.trans eq2.symm)

end Conjecture00000004759
