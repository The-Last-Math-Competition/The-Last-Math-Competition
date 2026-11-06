import Mathlib

/-!
# Conjecture 00000007468 (weight-limsup shift spectral disk): disproof

Objects of the conjecture.
* `Hs` is the Hilbert space `l^2(N)`, `N = {0,1,2,...}`, realised as `lp (fun _ : N => ℂ) 2`.
* For a weight sequence `w : N → ℂ` with `‖w k‖ ≤ M` for all `k`, the unilateral forward
  weighted shift `W` is `W e_n = w_n e_{n+1}`, i.e. `(W x) 0 = 0` and `(W x) (n+1) = w n * x n`.
  It is the bounded operator `shiftOp w M hM : Hs →L[ℂ] Hs` (its norm is at most `M`).
* The spectrum `σ(W)` is Mathlib's `spectrum ℂ W` in the Banach algebra of bounded operators.
* The weight limsup is `Filter.limsup (fun k => ‖w k‖) Filter.atTop : ℝ`.

The conjecture ("the spectrum of a weighted shift is a disk whose radius is the limsup of the
weights") is recorded as `ConjectureHolds`, read universally over all bounded weight sequences,
with the centre of the disk left free.

Counterexample. `wgt k = 2` for odd `k` and `wgt k = 1/2` for even `k`. Then the limsup is `2`,
but `W^2` is an isometry (`W^2 e_n = e_{n+2}`, since `wgt (n+1) * wgt n = 1`), so the spectrum of
`W` lies in the closed unit disk. A closed disk of radius `2` cannot lie in the closed unit disk.
The main theorem `TLMC7468.conjecture_00000007468_fails` states `¬ ConjectureHolds`.
-/

open Filter Metric
open scoped ENNReal

noncomputable section

namespace TLMC7468

/-- The Hilbert space `l^2(N)` of square-summable complex sequences indexed by `N = {0,1,2,...}`. -/
abbrev Hs : Type := lp (fun _ : ℕ => ℂ) 2

/-- Coordinates of the forward weighted shift: `(W x) 0 = 0` and `(W x) (n+1) = w n * x n`. -/
def shiftCoord (w : ℕ → ℂ) (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => w n * x n

@[simp] lemma shiftCoord_zero (w x : ℕ → ℂ) : shiftCoord w x 0 = 0 := rfl

@[simp] lemma shiftCoord_succ (w x : ℕ → ℂ) (n : ℕ) :
    shiftCoord w x (n + 1) = w n * x n := rfl

/-- Square-summability of the norms of a vector of `l^2`. -/
lemma summable_sq (x : Hs) : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ 2 := by
  have h := Memℓp.summable (p := 2) (by norm_num) (lp.memℓp x)
  simpa [Real.rpow_two] using h

/-- The `l^2` norm squared is the sum of the squared moduli of the coordinates. -/
lemma norm_sq_eq_tsum (x : Hs) : ‖x‖ ^ 2 = ∑' n, ‖(x : ℕ → ℂ) n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simpa [Real.rpow_two] using h

/-- Shifting a square-summable coordinate sequence by a bounded weight keeps it
square-summable, with the obvious bound. -/
lemma summable_shiftCoord_sq (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : ℕ → ℂ)
    (hx : Summable fun n => ‖x n‖ ^ 2) : Summable fun n => ‖shiftCoord w x n‖ ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hx.mul_left (M ^ 2))
  have h := hM n
  simp only [shiftCoord_succ, norm_mul]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _)

/-- The weighted shift of an `l^2` vector is again in `l^2`. -/
lemma memℓp_shiftCoord (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : Hs) :
    Memℓp (shiftCoord w x) 2 := by
  apply memℓp_gen
  simpa [Real.rpow_two] using summable_shiftCoord_sq w M hM x (summable_sq x)

/-- The weighted shift as a map `Hs → Hs`. -/
def shiftFn (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : Hs) : Hs :=
  ⟨shiftCoord w x, memℓp_shiftCoord w M hM x⟩

lemma shiftFn_apply (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : Hs) (n : ℕ) :
    shiftFn w M hM x n = shiftCoord w x n := rfl

lemma norm_shiftFn_le (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : Hs) :
    ‖shiftFn w M hM x‖ ≤ M * ‖x‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply lp.norm_le_of_tsum_le (p := 2) (by norm_num) (mul_nonneg hM0 (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [mul_pow, norm_sq_eq_tsum x, ← tsum_mul_left]
  change ∑' n, ‖shiftCoord w x n‖ ^ 2 ≤ _
  have hs := summable_shiftCoord_sq w M hM x (summable_sq x)
  rw [hs.tsum_eq_zero_add]
  have h0 : ‖shiftCoord w x 0‖ ^ 2 = 0 := by simp
  rw [h0, zero_add]
  apply Summable.tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff 1).mpr hs)
    ((summable_sq x).mul_left _)
  have h := hM n
  simp only [shiftCoord_succ, norm_mul]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _)

lemma shiftCoord_add (w x y : ℕ → ℂ) (n : ℕ) :
    shiftCoord w (x + y) n = shiftCoord w x n + shiftCoord w y n := by
  cases n with
  | zero => simp
  | succ m => simp [mul_add]

lemma shiftCoord_smul (w x : ℕ → ℂ) (c : ℂ) (n : ℕ) :
    shiftCoord w (c • x) n = c • shiftCoord w x n := by
  cases n with
  | zero => simp
  | succ m => simp [Pi.smul_apply, smul_eq_mul]; ring

lemma shiftFn_add (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x y : Hs) :
    shiftFn w M hM (x + y) = shiftFn w M hM x + shiftFn w M hM y := by
  ext n
  show shiftCoord w ((x + y : Hs) : ℕ → ℂ) n
      = shiftCoord w (x : ℕ → ℂ) n + shiftCoord w (y : ℕ → ℂ) n
  rw [lp.coeFn_add, shiftCoord_add]

lemma shiftFn_smul (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (c : ℂ) (x : Hs) :
    shiftFn w M hM (c • x) = c • shiftFn w M hM x := by
  ext n
  show shiftCoord w ((c • x : Hs) : ℕ → ℂ) n = c • shiftCoord w (x : ℕ → ℂ) n
  rw [lp.coeFn_smul, shiftCoord_smul]

/-- The forward weighted shift `W` with weights `w` (bounded by `M`) as a bounded operator on
`l^2(N)`: `W e_n = w_n e_{n+1}`. -/
def shiftOp (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) : Hs →L[ℂ] Hs :=
  LinearMap.mkContinuous
    { toFun := shiftFn w M hM
      map_add' := shiftFn_add w M hM
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact shiftFn_smul w M hM c x }
    M (fun x => norm_shiftFn_le w M hM x)

lemma shiftOp_apply (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M) (x : Hs) :
    shiftOp w M hM x = shiftFn w M hM x := rfl

/-- The specific weights of the counterexample: `2` at odd indices, `1/2` at even indices. -/
def wgt (k : ℕ) : ℂ := if k % 2 = 1 then 2 else 1 / 2

lemma wgt_norm_le (k : ℕ) : ‖wgt k‖ ≤ 2 := by
  unfold wgt
  split_ifs
  · simp
  · rw [norm_div, norm_one]
    norm_num

lemma wgt_succ_mul (n : ℕ) : wgt (n + 1) * wgt n = 1 := by
  unfold wgt
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [h, h']

lemma shiftCoord_shiftCoord_add_two (x : ℕ → ℂ) (n : ℕ) :
    shiftCoord wgt (shiftCoord wgt x) (n + 1 + 1) = x n := by
  simp only [shiftCoord_succ]
  rw [← mul_assoc, wgt_succ_mul, one_mul]

lemma tsum_shift_shift (x : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) :
    ∑' n, ‖shiftCoord wgt (shiftCoord wgt x) n‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  have hy : Summable fun n => ‖shiftCoord wgt x n‖ ^ 2 :=
    summable_shiftCoord_sq wgt 2 wgt_norm_le x hx
  have hz : Summable fun n => ‖shiftCoord wgt (shiftCoord wgt x) n‖ ^ 2 :=
    summable_shiftCoord_sq wgt 2 wgt_norm_le _ hy
  rw [hz.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hz).tsum_eq_zero_add]
  have h2 : ∀ n, ‖shiftCoord wgt (shiftCoord wgt x) (n + 1 + 1)‖ ^ 2 = ‖x n‖ ^ 2 :=
    fun n => by rw [shiftCoord_shiftCoord_add_two]
  have h0 : ‖shiftCoord wgt (shiftCoord wgt x) 0‖ ^ 2 = 0 := by simp
  have h1 : ‖shiftCoord wgt (shiftCoord wgt x) (0 + 1)‖ ^ 2 = 0 := by simp
  simp only [h2]
  rw [h0, h1]
  simp

/-- `‖W^2 x‖ = ‖x‖` for the counterexample weights: `W^2` is an isometry. -/
lemma norm_shiftFn_sq (x : Hs) :
    ‖shiftFn wgt 2 wgt_norm_le (shiftFn wgt 2 wgt_norm_le x)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  change ∑' n, ‖shiftCoord wgt (shiftCoord wgt x) n‖ ^ 2 = ∑' n, ‖(x : ℕ → ℂ) n‖ ^ 2
  exact tsum_shift_shift x (summable_sq x)

lemma norm_WW_le (x : Hs) :
    ‖shiftFn wgt 2 wgt_norm_le (shiftFn wgt 2 wgt_norm_le x)‖ ≤ ‖x‖ := by
  have h := norm_shiftFn_sq x
  nlinarith [norm_nonneg (shiftFn wgt 2 wgt_norm_le (shiftFn wgt 2 wgt_norm_le x)),
    norm_nonneg x]

/-- The operator `W^2` has norm at most one. -/
lemma norm_WW_op_le : ‖shiftOp wgt 2 wgt_norm_le * shiftOp wgt 2 wgt_norm_le‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  show ‖shiftFn wgt 2 wgt_norm_le (shiftFn wgt 2 wgt_norm_le x)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact norm_WW_le x

instance : Nontrivial Hs := by
  refine ⟨⟨lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ), 0, ?_⟩⟩
  intro h
  have h1 : (lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) : Hs) 0 = 0 := by rw [h]; rfl
  rw [lp.single_apply_self] at h1
  exact one_ne_zero h1

/-- Spectral mapping for `W^2` gives `σ(W) ⊆ closed unit disk`. -/
lemma spectrum_shiftOp_subset :
    spectrum ℂ (shiftOp wgt 2 wgt_norm_le) ⊆ closedBall (0 : ℂ) 1 := by
  intro z hz
  have hpow : z ^ 2 ∈ spectrum ℂ (shiftOp wgt 2 wgt_norm_le ^ 2) := by
    rw [spectrum.map_pow_of_pos _ two_pos]
    exact ⟨z, hz, rfl⟩
  have hnorm : ‖shiftOp wgt 2 wgt_norm_le ^ 2‖ ≤ 1 := by
    rw [pow_two]
    exact norm_WW_op_le
  have h1 : z ^ 2 ∈ closedBall (0 : ℂ) 1 :=
    closedBall_subset_closedBall hnorm (spectrum.subset_closedBall_norm _ hpow)
  rw [mem_closedBall_zero_iff, norm_pow] at h1
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg z]

/-- Upper limit of the weight moduli, in `ℝ`. -/
lemma two_le_limsup_wgt : (2 : ℝ) ≤ Filter.limsup (fun k => ‖wgt k‖) Filter.atTop := by
  have hfreq : ∃ᶠ k in Filter.atTop, (2 : ℝ) ≤ ‖wgt k‖ := by
    apply Filter.frequently_atTop.2
    intro N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have h' : (2 * N + 1) % 2 = 1 := by omega
    simp [wgt, h']
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun k => ‖wgt k‖) :=
    Filter.isBoundedUnder_of ⟨2, fun k => wgt_norm_le k⟩
  exact Filter.le_limsup_of_frequently_le hfreq hbdd

/-- The conjecture 00000007468 read universally: for every bounded weight sequence `w`
with bound `M`, the spectrum of the weighted shift is a closed disk `closedBall c r`
with radius `r` equal to the limsup of the weight moduli. The centre `c` is free. -/
def ConjectureHolds : Prop :=
  ∀ (w : ℕ → ℂ) (M : ℝ) (hM : ∀ k, ‖w k‖ ≤ M),
    ∃ c : ℂ, spectrum ℂ (shiftOp w M hM) =
      closedBall c (Filter.limsup (fun k => ‖w k‖) Filter.atTop)

/-- The conjecture fails: the weights `wgt` (limsup `2`) give a spectrum equal to the closed
unit disk, which is not a closed disk of radius `2` at any centre. -/
theorem conjecture_00000007468_fails : ¬ ConjectureHolds := by
  intro h
  obtain ⟨c, hc⟩ := h wgt 2 wgt_norm_le
  have hsub := spectrum_shiftOp_subset
  rw [hc] at hsub
  set L := Filter.limsup (fun k => ‖wgt k‖) Filter.atTop with hLdef
  have hL2 : (2 : ℝ) ≤ L := two_le_limsup_wgt
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have h1 : c + (L : ℂ) ∈ closedBall c L := by
    simp [Metric.mem_closedBall, abs_of_nonneg hL0]
  have h2 : c - (L : ℂ) ∈ closedBall c L := by
    simp [Metric.mem_closedBall, abs_of_nonneg hL0]
  have k1 := hsub h1
  have k2 := hsub h2
  rw [mem_closedBall_zero_iff] at k1 k2
  have key : ‖(2 : ℂ) * (L : ℂ)‖ ≤ ‖c + (L : ℂ)‖ + ‖c - (L : ℂ)‖ := by
    have e : c + (L : ℂ) - (c - (L : ℂ)) = 2 * (L : ℂ) := by ring
    have := norm_sub_le (c + (L : ℂ)) (c - (L : ℂ))
    rwa [e] at this
  have e2 : ‖(2 : ℂ) * (L : ℂ)‖ = 2 * L := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0]
    norm_num
  linarith

end TLMC7468

end

#print axioms TLMC7468.conjecture_00000007468_fails
