import TLMC69.Kernel

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
namespace TLMC69

def kernel (n : ℕ) : ℝ[X] := Q n ^ 4

def mass (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (kernel n).eval x

def moment (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x^2 * (kernel n).eval x

lemma kernel_eval (n : ℕ) (x : ℝ) : (kernel n).eval x = ((Q n).eval x)^4 := by
  simp [kernel]

lemma kernel_nonneg (n : ℕ) (x : ℝ) : 0 ≤ (kernel n).eval x := by
  rw [kernel_eval]; positivity

lemma kernel_even (n : ℕ) (x : ℝ) : (kernel n).eval (-x) = (kernel n).eval x := by
  simp [kernel_eval, Q_even]

lemma kernel_degree (n : ℕ) : (kernel n).natDegree ≤ 8*n := by
  calc
    (kernel n).natDegree ≤ 4 * (Q n).natDegree := natDegree_pow_le
    _ ≤ 8*n := by have := Q_degree n; omega

lemma kernel_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    (kernel n).eval x ≤ (2*n+1)^4 := by
  rw [kernel_eval, ← (show Even (4:ℕ) by decide).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Q_bound n hx) 4

lemma kernel_weight_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    x^4 * (kernel n).eval x ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Q_mul_bound n hx) 4
  have he : |x * (Q n).eval x|^4 = x^4 * ((Q n).eval x)^4 := by
    rw [show (4:ℕ) = 2*2 by rfl, pow_mul, sq_abs, ← pow_mul, mul_pow]
  simpa only [he, one_pow, kernel_eval] using h

lemma mass_lower (n : ℕ) : (2*n+1)^3 / 64 ≤ mass n := by
  let N : ℝ := 2*n+1
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let a : ℝ := 1/(4*N)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; rw [div_le_iff₀ (by positivity : 0 < 4*N)]; linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) ha
    (continuous_const.intervalIntegrable (μ := volume) _ _) ((kernel n).continuous.intervalIntegrable _ _)
    (f := fun _ : ℝ => (N/2)^4) (g := fun x => (kernel n).eval x) (by
      intro x hx
      change (N/2)^4 ≤ (kernel n).eval x
      rw [kernel_eval]
      exact pow_le_pow_left₀ (by positivity) (Q_lower n hx) 4)
  have hi2 := intervalIntegral.integral_mono_interval (μ := volume) (a := 0) (b := a) (c := 0) (d := 1)
    le_rfl ha ha1 (Filter.Eventually.of_forall fun x => kernel_nonneg n x)
    ((kernel n).continuous.intervalIntegrable _ _)
  have he : (∫ _x in (0:ℝ)..a, (N/2)^4) = N^3/64 := by
    rw [intervalIntegral.integral_const]; dsimp [a]; simp only [sub_zero, smul_eq_mul]
    field_simp; ring
  rw [he] at hi
  exact hi.trans hi2

lemma mass_pos (n : ℕ) : 0 < mass n :=
  lt_of_lt_of_le (by positivity) (mass_lower n)

lemma moment_nonneg (n : ℕ) : 0 ≤ moment n := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
  intro x; exact mul_nonneg (sq_nonneg _) (kernel_nonneg n x)

lemma moment_upper (n : ℕ) : moment n ≤ 2 * (2*n+1) := by
  let N : ℝ := 2*n+1
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let a : ℝ := 1/N
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; rw [div_le_iff₀ hN]; simpa using hN1
  have hcont : Continuous (fun x : ℝ => x^2 * (kernel n).eval x) :=
    (continuous_id.pow 2).mul (kernel n).continuous
  have hsmall := intervalIntegral.integral_mono_on (μ := volume) ha.le (hcont.intervalIntegrable _ _)
    (((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _)
    (g := fun x : ℝ => x^2 * N^4) (by
      intro x hx
      exact mul_le_mul_of_nonneg_left (kernel_bound n ⟨by linarith [hx.1], hx.2.trans ha1⟩) (sq_nonneg x))
  have hbigint : IntervalIntegrable (fun x : ℝ => 1/x^2) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro x hx
    rw [uIcc_of_le ha1] at hx
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hx.1))
  have hbig := intervalIntegral.integral_mono_on (μ := volume) ha1 (hcont.intervalIntegrable _ _) hbigint
    (g := fun x : ℝ => 1/x^2) (by
      intro x hx
      have hx0 : 0 < x := ha.trans_le hx.1
      rw [le_div_iff₀ (sq_pos_of_pos hx0)]
      have h := kernel_weight_bound n ⟨by linarith, hx.2⟩
      nlinarith)
  have hesmall : (∫ x in (0:ℝ)..a, x^2*N^4) = N/3 := by
    rw [intervalIntegral.integral_mul_const, integral_pow]
    dsimp [a]
    norm_num
    field_simp
    ring
  have hebig : (∫ x in a..1, 1/x^2) = N-1 := by
    have hder : ∀ x ∈ uIcc a 1, HasDerivAt (fun x : ℝ => -(1/x)) (1/x^2) x := by
      intro x hx
      rw [uIcc_of_le ha1] at hx
      have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
      convert (hasDerivAt_inv hx0).neg using 1 <;> simp [one_div]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hbigint]
    dsimp [a]; field_simp; ring
  rw [hesmall] at hsmall
  rw [hebig] at hbig
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 a) (hcont.intervalIntegrable a 1)
  change (∫ x in (0:ℝ)..1, x^2*(kernel n).eval x) ≤ 2*N
  calc
    _ = (∫ x in (0:ℝ)..a, x^2*(kernel n).eval x) + ∫ x in a..1, x^2*(kernel n).eval x := he.symm
    _ ≤ N/3 + (N-1) := add_le_add hsmall hbig
    _ ≤ N+N := add_le_add (div_le_self hN.le (by norm_num)) (sub_le_self N zero_le_one)
    _ = 2*N := by ring

end TLMC69
