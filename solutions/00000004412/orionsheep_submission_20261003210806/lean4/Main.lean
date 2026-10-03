import Mathlib

/-!
# Refutation of TLMC conjecture 00000004412

**Conjecture.** "The characteristic function of the expected spectral measure
is given explicitly by the logarithm of the Fredholm determinant of the
kernel, and the determinant series converges if and only if the kernel is
square integrable."

**Refutation (the first conjunct fails for every kernel).**  We model the
graphon integral operator on a finite probability space `Fin m` (uniform
measure) by a symmetric real kernel `K`; the operator is `T = (1/m) • K`.

* The expected spectral measure is the empirical eigenvalue law
  `μ = (1/m) Σ_j δ_{λ_j}` of `T`.  Its characteristic function
  `φ(t) = (1/m) Σ_j e^{i t λ_j}` is the exponential generating function of
  the spectral moments `m_n = (1/m) Tr T^n`, and — being the characteristic
  function of a *probability* measure — satisfies `φ(0) = 1` for every
  kernel.

* The Fredholm determinant series is
  `det(I − zT) = 1 + Σ_{n≥1} a_n z^n` with
  `a_n = (−1)^n/n! · m^{−n} Σ_{x : Fin n → Fin m} det[K(x_i, x_j)]`,
  hence `det(I − 0·T) = 1`, so `log det(I − 0·T) = 0` for every kernel.

The conjectured identity `φ(t) = log det(I − tT)` therefore fails already at
`t = 0` — `1 ≠ 0` — on the simplest nonzero example, the constant-`1` graphon
on one point (the complete-graph limit).  No kernel can repair this: a
characteristic function is `1` at `0` while a log-determinant is `0` there.

(The second conjunct also fails in the "only if" direction — the rank-one
kernel `K(x,y) = y^{-3/4}` on `[0,1]` is not square integrable, yet its
Fredholm series collapses to the polynomial `1 − 4z`; see `reproduce.py`.
Since the conjunction is already refuted by the first conjunct, the Lean
development formalizes the spectral side only.)

All theorems are closed under the kernel; `#print axioms` in `Check.lean`
reports no extra axioms.
-/

namespace Submission00000004412

/-! ## The objects -/

/-- A graphon kernel on the finite probability space `Fin m` with uniform
    measure: a symmetric real `m × m` matrix. -/
structure FiniteGraphon (m : ℕ) where
  /-- The kernel `K : [0,1]² → ℝ`, discretized as a matrix. -/
  K : Matrix (Fin m) (Fin m) ℝ
  /-- `K` is symmetric, so the integral operator is self-adjoint and has a
      real spectrum. -/
  symm : ∀ i j, K i j = K j i

/-- The graphon integral operator `T f (x) = (1/m) Σ_y K(x,y) f(y)`. -/
noncomputable def intOp {m : ℕ} [NeZero m] (W : FiniteGraphon m) :
    Matrix (Fin m) (Fin m) ℝ :=
  (m : ℝ)⁻¹ • W.K

/-- The `n`-th moment of the *expected spectral measure* of `W`:
    `m_n = ∫ λ^n dμ = (1/m) Tr(T^n)`. -/
noncomputable def spectralMoment {m : ℕ} [NeZero m] (W : FiniteGraphon m)
    (n : ℕ) : ℝ :=
  (m : ℝ)⁻¹ * ((intOp W) ^ n).trace

/-- The characteristic function of the expected spectral measure,
    `φ(t) = Σ_n (i t)^n m_n / n!` — the exponential generating function of
    the spectral moments; for the finite model it equals
    `(1/m) Σ_j e^{i t λ_j}`. -/
noncomputable def spectralCharFn {m : ℕ} [NeZero m] (W : FiniteGraphon m)
    (t : ℝ) : ℂ :=
  ∑' n : ℕ, (Complex.I * (t : ℂ)) ^ n * (spectralMoment W n : ℂ) / Nat.factorial n

/-- The `n`-th Fredholm series coefficient of the kernel:
    `a_n = (−1)^n/n! · m^{−n} · Σ_{x : Fin n → Fin m} det [K(x_i, x_j)]`
    — the discretized `n`-fold integral of the determinant kernel. -/
noncomputable def fredholmCoeff {m : ℕ} (W : FiniteGraphon m) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Nat.factorial n * (m : ℝ) ^ (-(n : ℤ)) *
    ∑ x : Fin n → Fin m,
      (Matrix.of fun i j : Fin n => W.K (x i) (x j)).det

/-- The Fredholm determinant of the kernel operator,
    `det(I − z T_W) = 1 + Σ_{n ≥ 1} a_n z^n`. -/
noncomputable def fredholmDet {m : ℕ} (W : FiniteGraphon m) (z : ℝ) : ℝ :=
  1 + ∑' n : ℕ, fredholmCoeff W (n + 1) * z ^ (n + 1)

/-- The conjectured identity: the characteristic function of the expected
    spectral measure equals the logarithm of the Fredholm determinant, for
    every kernel and every parameter. -/
def FredholmLogClaim : Prop :=
  ∀ (m : ℕ) [NeZero m] (W : FiniteGraphon m) (t : ℝ),
    spectralCharFn W t = (Real.log (fredholmDet W t) : ℂ)

/-! ## Values at `t = 0` -/

/-- The `0`-th spectral moment: `(1/m) Tr(I) = 1`.  This is probability
    normalization of the expected spectral measure. -/
theorem spectralMoment_zero {m : ℕ} [NeZero m] (W : FiniteGraphon m) :
    spectralMoment W 0 = 1 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  unfold spectralMoment
  rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
  exact inv_mul_cancel₀ hm

/-- Every term `n ≥ 1` of the characteristic-function series vanishes at
    `t = 0`. -/
theorem spectralCharFn_term_zero {m : ℕ} [NeZero m] (W : FiniteGraphon m)
    {b : ℕ} (hb : b ≠ 0) :
    (Complex.I * ((0 : ℝ) : ℂ)) ^ b * (spectralMoment W b : ℂ) / Nat.factorial b = 0 := by
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  have : (Complex.I * ((0 : ℝ) : ℂ)) ^ b = 0 := by
    rw [h0, mul_zero]; exact zero_pow hb
  rw [this, zero_mul, zero_div]

/-- `φ(0) = 1`: the characteristic function of the expected spectral measure
    at `t = 0` — true for *every* kernel, since a characteristic function of
    a probability measure is `1` at `0`. -/
theorem spectralCharFn_zero {m : ℕ} [NeZero m] (W : FiniteGraphon m) :
    spectralCharFn W 0 = 1 := by
  unfold spectralCharFn
  rw [tsum_eq_single 0 (fun b hb => spectralCharFn_term_zero W hb)]
  simp [spectralMoment_zero W]

/-- `det(I − 0·T) = 1`: the Fredholm determinant at `z = 0` — true for
    *every* kernel. -/
theorem fredholmDet_zero {m : ℕ} (W : FiniteGraphon m) :
    fredholmDet W 0 = 1 := by
  unfold fredholmDet
  have : ∀ n : ℕ, fredholmCoeff W (n + 1) * (0 : ℝ) ^ (n + 1) = 0 := by
    intro n
    rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [tsum_congr this]
  simp

/-- Hence `log det(I − 0·T) = 0` for every kernel. -/
theorem logFredholmDet_zero {m : ℕ} (W : FiniteGraphon m) :
    Real.log (fredholmDet W 0) = 0 := by
  rw [fredholmDet_zero, Real.log_one]

/-! ## The counterexample -/

/-- The constant-`1` graphon on a one-point space: the complete-graph limit,
    the simplest non-degenerate exchangeable random graph limit. -/
def completeGraphon : FiniteGraphon 1 where
  K := fun _ _ => 1
  symm := fun _ _ => rfl

/-- At `t = 0` the conjectured identity reads `1 = 0`: already false for the
    complete graphon. -/
theorem instance_violates_claim :
    spectralCharFn completeGraphon 0 ≠
      (Real.log (fredholmDet completeGraphon 0) : ℂ) := by
  rw [spectralCharFn_zero, logFredholmDet_zero]
  simp

/-- **Refutation.** The conjectured identity `φ = log det` is false: it fails
    at `t = 0` on the complete graphon, where `φ(0) = 1` (probability
    normalization) but `log det(I) = 0`. -/
theorem conjecture_refuted : ¬ FredholmLogClaim := by
  intro h
  exact instance_violates_claim (h 1 completeGraphon 0)

end Submission00000004412
