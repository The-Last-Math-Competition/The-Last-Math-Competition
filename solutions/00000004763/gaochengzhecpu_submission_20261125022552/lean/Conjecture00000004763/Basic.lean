/-
  Conjecture 00000004763 — Foundational Combinatorial & Moment-Cumulant Algebra
  Core Lean 4.19.0 (zero external dependencies).

  Defines finite integer sums, binomial coefficients, factorials, powers,
  classical moment-cumulant transformations (exponential generating recurrence),
  Speicher's free moment-cumulant transformations (noncrossing / R-transform
  convolution recurrence), and proves exact mutual inversion in both directions.
-/

namespace Conjecture00000004763

/-- Sum `f 0 + f 1 + ... + f (n - 1)` over `n` indices starting at `0`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_zero (f : Nat → Int) : sumRange 0 f = 0 := rfl

theorem sumRange_succ (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = sumRange n f + f n := rfl

theorem sumRange_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    have h1 : sumRange m f = sumRange m g := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : f m = g m := h m (Nat.lt_succ_self m)
    rw [h1, h2]

theorem sumRange_const_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [sumRange, ih]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_le {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i ≤ g i) : sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ m ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h m (Nat.lt_succ_self m)
    omega

theorem sumRange_abs_le (n : Nat) (f : Nat → Int) :
    sumRange n f ≤ sumRange n (fun i => Int.natAbs (f i)) := by
  apply sumRange_le
  intro i _
  exact Int.le_natAbs

theorem sumRange_single (n k : Nat) (v : Int) (hk : k < n) :
    sumRange n (fun i => if i = k then v else 0) = v := by
  induction n with
  | zero => cases hk
  | succ m ih =>
    simp only [sumRange]
    by_cases hkm : m = k
    · subst hkm
      have hzero : sumRange m (fun i => if i = m then v else 0) = 0 := by
        have hcong : sumRange m (fun i => if i = m then v else 0) = sumRange m (fun _ => 0) := by
          apply sumRange_congr
          intro i hi
          have hne : i ≠ m := Nat.ne_of_lt hi
          simp [hne]
        rw [hcong, sumRange_const_zero]
      simp [hzero]
    · have hlt : k < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) (Ne.symm hkm)
      rw [ih hlt]
      simp [hkm]

/-- Sum `f 1 + f 2 + ... + f n` over `1 ≤ k ≤ n`. -/
def sumIcc1 (n : Nat) (f : Nat → Int) : Int :=
  sumRange n (fun i => f (i + 1))

theorem sumIcc1_zero (f : Nat → Int) : sumIcc1 0 f = 0 := rfl

theorem sumIcc1_succ (n : Nat) (f : Nat → Int) :
    sumIcc1 (n + 1) f = sumIcc1 n f + f (n + 1) := rfl

theorem sumIcc1_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ k, 1 ≤ k → k ≤ n → f k = g k) : sumIcc1 n f = sumIcc1 n g := by
  unfold sumIcc1
  apply sumRange_congr
  intro i hi
  exact h (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) (Nat.succ_le_of_lt hi)

/-- Integer binomial coefficients `binom n k = C(n, k)`. -/
def binom : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

theorem binom_zero_left (k : Nat) : binom 0 (k + 1) = 0 := rfl

theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

theorem binom_gt {n k : Nat} (h : n < k) : binom n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => cases h
    | succ k' => rfl
  | succ m ih =>
    cases k with
    | zero => cases h
    | succ k' =>
      simp only [binom]
      have h1 : m < k' := Nat.lt_of_succ_lt_succ h
      have h2 : m < k' + 1 := Nat.lt_succ_of_lt h1
      rw [ih h1, ih h2]
      rfl

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [binom, ih, binom_gt (Nat.lt_succ_self m)]
    omega

theorem binom_one_right (n : Nat) : binom n 1 = (n : Int) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [binom, binom_zero_right, ih]
    omega

theorem two_mul_binom_two (n : Nat) :
    2 * binom n 2 = (n : Int) * ((n : Int) - 1) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [binom, binom_one_right, Int.mul_add, ih]
    have h1 : (((m + 1 : Nat) : Int) - 1) = (m : Int) := by omega
    have h2 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
    rw [h1, h2, Int.add_mul, Int.mul_sub]
    omega

theorem binom_nonneg (n k : Nat) : 0 ≤ binom n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [binom]
  | succ m ih =>
    cases k with
    | zero => simp [binom]
    | succ k' =>
      simp only [binom]
      have h1 := ih k'
      have h2 := ih (k' + 1)
      omega

/-- Integer factorial `factZ n = n!`. -/
def factZ : Nat → Int
  | 0 => 1
  | n + 1 => ((n + 1 : Nat) : Int) * factZ n

theorem factZ_pos (n : Nat) : 1 ≤ factZ n := by
  induction n with
  | zero => exact Int.le_refl 1
  | succ m ih =>
    simp only [factZ]
    have hm : (1 : Int) ≤ ((m + 1 : Nat) : Int) := by omega
    have := Int.mul_le_mul hm ih (by omega) (by omega)
    simpa using this

/-- Fundamental factorial identity `binom n k * k! * (n - k)! = n!` for `k ≤ n`. -/
theorem binom_mul_factZ :
    ∀ n k : Nat, k ≤ n → binom n k * factZ k * factZ (n - k) = factZ n := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    rfl
  | succ m ih =>
    intro k hk
    cases k with
    | zero =>
      simp [binom, factZ]
    | succ k' =>
      by_cases hlt : k' < m
      · have hle1 : k' ≤ m := Nat.le_of_lt hlt
        have hle2 : k' + 1 ≤ m := Nat.succ_le_of_lt hlt
        have ih1 := ih k' hle1
        have ih2 := ih (k' + 1) hle2
        have hsub : m - k' = (m - (k' + 1)) + 1 := by omega
        simp only [binom, Nat.succ_sub_succ_eq_sub]
        rw [Int.add_mul, Int.add_mul]
        -- Term 1: binom m k' * factZ (k' + 1) * factZ (m - k')
        have ht1 :
            binom m k' * factZ (k' + 1) * factZ (m - k') =
            ((k' + 1 : Nat) : Int) * (binom m k' * factZ k' * factZ (m - k')) := by
          simp only [factZ]
          rw [Int.mul_left_comm (binom m k'), Int.mul_assoc, Int.mul_assoc]
        -- Term 2: binom m (k' + 1) * factZ (k' + 1) * factZ (m - k')
        have ht2 :
            binom m (k' + 1) * factZ (k' + 1) * factZ (m - k') =
            ((m - (k' + 1) + 1 : Nat) : Int) *
              (binom m (k' + 1) * factZ (k' + 1) * factZ (m - (k' + 1))) := by
          rw [hsub]
          simp only [factZ]
          rw [← Int.mul_assoc, Int.mul_comm _ (((m - (k' + 1) + 1 : Nat) : Int)),
              Int.mul_assoc]
        have hsum_nat : ((k' + 1 : Nat) : Int) + ((m - (k' + 1) + 1 : Nat) : Int) =
            ((m + 1 : Nat) : Int) := by omega
        rw [ht1, ht2, ih1, ih2, ← Int.add_mul, hsum_nat]
        rfl
      · have heq : k' = m := by omega
        subst heq
        simp [binom_self, Nat.sub_self, factZ]

/-- Integer power `powZ a k = a^k`. -/
def powZ (a : Int) : Nat → Int
  | 0 => 1
  | k + 1 => a * powZ a k

theorem powZ_zero (a : Int) : powZ a 0 = 1 := rfl
theorem powZ_succ (a : Int) (k : Nat) : powZ a (k + 1) = a * powZ a k := rfl

theorem powZ_one (k : Nat) : powZ 1 k = 1 := by
  induction k with
  | zero => rfl
  | succ m ih => simp [powZ, ih]

theorem powZ_nonneg {a : Int} (ha : 0 ≤ a) (k : Nat) : 0 ≤ powZ a k := by
  induction k with
  | zero => exact Int.le_of_lt Int.zero_lt_one
  | succ m ih => exact Int.mul_nonneg ha ih

theorem powZ_pos {a : Int} (ha : 1 ≤ a) (k : Nat) : 1 ≤ powZ a k := by
  induction k with
  | zero => exact Int.le_refl 1
  | succ m ih =>
    have := Int.mul_le_mul ha ih (by omega) (by omega)
    simpa [powZ] using this

/-!
## 1. Classical Moment-Cumulant System

Moments `m_n` (`m_0 = 1`) and classical cumulants `c_n` (`n ≥ 1`) satisfy the
partition-lattice / EGF recurrence:
  `m_n = ∑_{k=1}^n binom(n - 1, k - 1) * c_k * m_{n - k}`.
-/

/-- Fuel-bounded classical moment evaluation (exact when `n ≤ fuel`). -/
def clMomentAux (c : Nat → Int) : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      sumRange (n + 1) (fun i => binom n i * c (i + 1) * clMomentAux c fuel (n - i))

theorem clMomentAux_zero (c : Nat → Int) (f : Nat) : clMomentAux c f 0 = 1 := by
  cases f <;> rfl

theorem clMomentAux_stable (c : Nat → Int) :
    ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → clMomentAux c f1 n = clMomentAux c f2 n
  | f1, f2, 0, _, _ => by rw [clMomentAux_zero, clMomentAux_zero]
  | 0, _, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, n + 1, h1, h2 => by
      simp only [clMomentAux]
      apply sumRange_congr
      intro i _
      have hsub1 : n - i ≤ f1 := Nat.le_trans (Nat.sub_le n i) (Nat.le_of_succ_le_succ h1)
      have hsub2 : n - i ≤ f2 := Nat.le_trans (Nat.sub_le n i) (Nat.le_of_succ_le_succ h2)
      rw [clMomentAux_stable c f1 f2 (n - i) hsub1 hsub2]

/-- Exact classical moment sequence generated by classical cumulants `c`. -/
def clMoment (c : Nat → Int) (n : Nat) : Int :=
  clMomentAux c n n

theorem clMoment_zero (c : Nat → Int) : clMoment c 0 = 1 := rfl

theorem clMoment_succ (c : Nat → Int) (n : Nat) :
    clMoment c (n + 1) =
      sumRange (n + 1) (fun i => binom n i * c (i + 1) * clMoment c (n - i)) := by
  unfold clMoment
  conv => lhs; simp only [clMomentAux]
  apply sumRange_congr
  intro i _
  rw [clMomentAux_stable c n (n - i) (n - i) (Nat.sub_le n i) (Nat.le_refl _)]

/-- Fuel-bounded classical cumulant extraction from moments `m` (`m 0 = 1`). -/
def clCumulantAux (m : Nat → Int) : Nat → Nat → Int
  | _, 0 => 0
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      m (n + 1) - sumRange n (fun i => binom n i * clCumulantAux m fuel (i + 1) * m (n - i))

theorem clCumulantAux_zero (m : Nat → Int) (f : Nat) : clCumulantAux m f 0 = 0 := by
  cases f <;> rfl

theorem clCumulantAux_stable (m : Nat → Int) :
    ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → clCumulantAux m f1 n = clCumulantAux m f2 n
  | f1, f2, 0, _, _ => by rw [clCumulantAux_zero, clCumulantAux_zero]
  | 0, _, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, n + 1, h1, h2 => by
      simp only [clCumulantAux]
      have hsum :
          sumRange n (fun i => binom n i * clCumulantAux m f1 (i + 1) * m (n - i)) =
          sumRange n (fun i => binom n i * clCumulantAux m f2 (i + 1) * m (n - i)) := by
        apply sumRange_congr
        intro i hi
        have hi1 : i + 1 ≤ f1 := Nat.le_trans (Nat.succ_le_of_lt hi) (Nat.le_of_succ_le_succ h1)
        have hi2 : i + 1 ≤ f2 := Nat.le_trans (Nat.succ_le_of_lt hi) (Nat.le_of_succ_le_succ h2)
        rw [clCumulantAux_stable m f1 f2 (i + 1) hi1 hi2]
      rw [hsum]

/-- Exact classical cumulant sequence extracted from moment sequence `m`. -/
def clCumulant (m : Nat → Int) (n : Nat) : Int :=
  clCumulantAux m n n

theorem clCumulant_zero (m : Nat → Int) : clCumulant m 0 = 0 := rfl

theorem clCumulant_succ (m : Nat → Int) (n : Nat) :
    clCumulant m (n + 1) =
      m (n + 1) - sumRange n (fun i => binom n i * clCumulant m (i + 1) * m (n - i)) := by
  unfold clCumulant
  conv => lhs; simp only [clCumulantAux]
  have hsum :
      sumRange n (fun i => binom n i * clCumulantAux m n (i + 1) * m (n - i)) =
      sumRange n (fun i => binom n i * clCumulantAux m (i + 1) (i + 1) * m (n - i)) := by
    apply sumRange_congr
    intro i hi
    rw [clCumulantAux_stable m n (i + 1) (i + 1) (Nat.succ_le_of_lt hi) (Nat.le_refl _)]
  rw [hsum]

/-- Exact inversion: extracting classical cumulants from classical moments recovers `c`. -/
theorem clCumulant_clMoment (c : Nat → Int) :
    ∀ n : Nat, 1 ≤ n → clCumulant (clMoment c) n = c n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ k =>
      rw [clCumulant_succ, clMoment_succ]
      rw [sumRange_succ]
      simp only [Nat.sub_self, binom_self, clMoment_zero, Int.one_mul, Int.mul_one]
      have hsum :
          sumRange k (fun i => binom k i * clCumulant (clMoment c) (i + 1) * clMoment c (k - i)) =
          sumRange k (fun i => binom k i * c (i + 1) * clMoment c (k - i)) := by
        apply sumRange_congr
        intro i hi
        rw [ih (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_le_succ (Nat.zero_le i))]
      rw [hsum]
      omega

/-- Exact inversion: generating classical moments from extracted cumulants recovers `m`. -/
theorem clMoment_clCumulant (m : Nat → Int) (hm0 : m 0 = 1) :
    ∀ n : Nat, clMoment (clCumulant m) n = m n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact hm0.symm
    | succ k =>
      rw [clMoment_succ, sumRange_succ]
      simp only [Nat.sub_self, binom_self, clMoment_zero, Int.one_mul, Int.mul_one]
      rw [clCumulant_succ]
      have hsum :
          sumRange k (fun i => binom k i * clCumulant m (i + 1) * clMoment (clCumulant m) (k - i)) =
          sumRange k (fun i => binom k i * clCumulant m (i + 1) * m (k - i)) := by
        apply sumRange_congr
        intro i _
        have hlt : k - i < k + 1 := Nat.lt_succ_of_le (Nat.sub_le k i)
        rw [ih (k - i) hlt]
      rw [hsum]
      omega

/-!
## 2. Speicher's Free Moment-Cumulant System

Let `M(z) = ∑_{d ≥ 0} m_d z^d` (`m_0 = 1`). Let `momentConv m r d = [z^d] M(z)^r`.
Speicher's noncrossing partition / R-transform formula `M(z) = C(z M(z))` is equivalent to:
  `m_n = ∑_{k=1}^n κ_k * momentConv m k (n - k)`.
-/

/-- Cauchy power convolution `momentConv m r d = [z^d] M(z)^r`. -/
def momentConv (m : Nat → Int) : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | r + 1, d => sumRange (d + 1) (fun j => m j * momentConv m r (d - j))

theorem momentConv_zero_left_zero (m : Nat → Int) : momentConv m 0 0 = 1 := rfl
theorem momentConv_zero_left_succ (m : Nat → Int) (d : Nat) : momentConv m 0 (d + 1) = 0 := rfl

theorem momentConv_zero_right (m : Nat → Int) (hm0 : m 0 = 1) :
    ∀ r : Nat, momentConv m r 0 = 1 := by
  intro r
  induction r with
  | zero => rfl
  | succ r' ih =>
    simp [momentConv, sumRange, hm0, ih]

theorem momentConv_congr {m1 m2 : Nat → Int} :
    ∀ r d : Nat, (∀ j, j ≤ d → m1 j = m2 j) → momentConv m1 r d = momentConv m2 r d := by
  intro r
  induction r with
  | zero =>
    intro d _
    cases d <;> rfl
  | succ r' ih =>
    intro d h
    simp only [momentConv]
    apply sumRange_congr
    intro j hj
    have hjle : j ≤ d := Nat.le_of_lt_succ hj
    rw [h j hjle]
    rw [ih (d - j) (fun t ht => h t (Nat.le_trans ht (Nat.sub_le d j)))]

/-- Fuel-bounded free moment evaluation from free cumulants `κ`. -/
def frMomentAux (κ : Nat → Int) : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      sumRange (n + 1) (fun i => κ (i + 1) * momentConv (frMomentAux κ fuel) (i + 1) (n - i))

theorem frMomentAux_zero (κ : Nat → Int) (f : Nat) : frMomentAux κ f 0 = 1 := by
  cases f <;> rfl

theorem frMomentAux_stable (κ : Nat → Int) :
    ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → frMomentAux κ f1 n = frMomentAux κ f2 n
  | _, _, 0, _, _ => by rw [frMomentAux_zero, frMomentAux_zero]
  | 0, _, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, n + 1, h1, h2 => by
      simp only [frMomentAux]
      apply sumRange_congr
      intro i _
      have hconv :
          momentConv (frMomentAux κ f1) (i + 1) (n - i) =
          momentConv (frMomentAux κ f2) (i + 1) (n - i) := by
        apply momentConv_congr
        intro j hj
        have hj1 : j ≤ f1 := Nat.le_trans hj (Nat.le_trans (Nat.sub_le n i) (Nat.le_of_succ_le_succ h1))
        have hj2 : j ≤ f2 := Nat.le_trans hj (Nat.le_trans (Nat.sub_le n i) (Nat.le_of_succ_le_succ h2))
        exact frMomentAux_stable κ f1 f2 j hj1 hj2
      rw [hconv]

/-- Exact free moment sequence generated by Speicher free cumulants `κ`. -/
def frMoment (κ : Nat → Int) (n : Nat) : Int :=
  frMomentAux κ n n

theorem frMoment_zero (κ : Nat → Int) : frMoment κ 0 = 1 := rfl

theorem frMoment_succ (κ : Nat → Int) (n : Nat) :
    frMoment κ (n + 1) =
      sumRange (n + 1) (fun i => κ (i + 1) * momentConv (frMoment κ) (i + 1) (n - i)) := by
  unfold frMoment
  conv => lhs; simp only [frMomentAux]
  apply sumRange_congr
  intro i _
  have hconv :
      momentConv (frMomentAux κ n) (i + 1) (n - i) =
      momentConv (fun t => frMomentAux κ t t) (i + 1) (n - i) := by
    apply momentConv_congr
    intro j hj
    exact frMomentAux_stable κ n j j (Nat.le_trans hj (Nat.sub_le n i)) (Nat.le_refl _)
  rw [hconv]

/-- Fuel-bounded free cumulant extraction from moments `m` (`m 0 = 1`). -/
def frCumulantAux (m : Nat → Int) : Nat → Nat → Int
  | _, 0 => 0
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      m (n + 1) - sumRange n (fun i => frCumulantAux m fuel (i + 1) * momentConv m (i + 1) (n - i))

theorem frCumulantAux_zero (m : Nat → Int) (f : Nat) : frCumulantAux m f 0 = 0 := by
  cases f <;> rfl

theorem frCumulantAux_stable (m : Nat → Int) :
    ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → frCumulantAux m f1 n = frCumulantAux m f2 n
  | f1, f2, 0, _, _ => by rw [frCumulantAux_zero, frCumulantAux_zero]
  | 0, _, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, n + 1, h1, h2 => by
      simp only [frCumulantAux]
      have hsum :
          sumRange n (fun i => frCumulantAux m f1 (i + 1) * momentConv m (i + 1) (n - i)) =
          sumRange n (fun i => frCumulantAux m f2 (i + 1) * momentConv m (i + 1) (n - i)) := by
        apply sumRange_congr
        intro i hi
        have hi1 : i + 1 ≤ f1 := Nat.le_trans (Nat.succ_le_of_lt hi) (Nat.le_of_succ_le_succ h1)
        have hi2 : i + 1 ≤ f2 := Nat.le_trans (Nat.succ_le_of_lt hi) (Nat.le_of_succ_le_succ h2)
        rw [frCumulantAux_stable m f1 f2 (i + 1) hi1 hi2]
      rw [hsum]

/-- Exact free cumulant sequence extracted from moment sequence `m`. -/
def frCumulant (m : Nat → Int) (n : Nat) : Int :=
  frCumulantAux m n n

theorem frCumulant_zero (m : Nat → Int) : frCumulant m 0 = 0 := rfl

theorem frCumulant_succ (m : Nat → Int) (n : Nat) :
    frCumulant m (n + 1) =
      m (n + 1) - sumRange n (fun i => frCumulant m (i + 1) * momentConv m (i + 1) (n - i)) := by
  unfold frCumulant
  conv => lhs; simp only [frCumulantAux]
  have hsum :
      sumRange n (fun i => frCumulantAux m n (i + 1) * momentConv m (i + 1) (n - i)) =
      sumRange n (fun i => frCumulantAux m (i + 1) (i + 1) * momentConv m (i + 1) (n - i)) := by
    apply sumRange_congr
    intro i hi
    rw [frCumulantAux_stable m n (i + 1) (i + 1) (Nat.succ_le_of_lt hi) (Nat.le_refl _)]
  rw [hsum]

/-- Exact inversion: extracting free cumulants from free moments recovers `κ`. -/
theorem frCumulant_frMoment (κ : Nat → Int) :
    ∀ n : Nat, 1 ≤ n → frCumulant (frMoment κ) n = κ n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ k =>
      rw [frCumulant_succ, frMoment_succ, sumRange_succ]
      simp only [Nat.sub_self, momentConv_zero_right (frMoment κ) (frMoment_zero κ), Int.mul_one]
      have hsum :
          sumRange k (fun i => frCumulant (frMoment κ) (i + 1) * momentConv (frMoment κ) (i + 1) (k - i)) =
          sumRange k (fun i => κ (i + 1) * momentConv (frMoment κ) (i + 1) (k - i)) := by
        apply sumRange_congr
        intro i hi
        rw [ih (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_le_succ (Nat.zero_le i))]
      rw [hsum]
      omega

/-- Exact inversion: generating free moments from extracted free cumulants recovers `m`. -/
theorem frMoment_frCumulant (m : Nat → Int) (hm0 : m 0 = 1) :
    ∀ n : Nat, frMoment (frCumulant m) n = m n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact hm0.symm
    | succ k =>
      rw [frMoment_succ, sumRange_succ]
      simp only [Nat.sub_self, momentConv_zero_right (frMoment (frCumulant m)) (frMoment_zero _), Int.mul_one]
      rw [frCumulant_succ]
      have hsum :
          sumRange k (fun i => frCumulant m (i + 1) * momentConv (frMoment (frCumulant m)) (i + 1) (k - i)) =
          sumRange k (fun i => frCumulant m (i + 1) * momentConv m (i + 1) (k - i)) := by
        apply sumRange_congr
        intro i _
        have hconv :
            momentConv (frMoment (frCumulant m)) (i + 1) (k - i) =
            momentConv m (i + 1) (k - i) := by
          apply momentConv_congr
          intro j hj
          exact ih j (Nat.lt_succ_of_le (Nat.le_trans hj (Nat.sub_le k i)))
        rw [hconv]
      rw [hsum]
      omega

/-!
## 3. Exact Free-Classical Cumulant Conversion Maps
-/

/-- Classical-to-free cumulant conversion `c ↦ κ(c)` matching moments `m_n`. -/
def classicalToFree (c : Nat → Int) : Nat → Int :=
  frCumulant (clMoment c)

/-- Free-to-classical cumulant conversion `κ ↦ c(κ)` matching moments `m_n`. -/
def freeToClassical (κ : Nat → Int) : Nat → Int :=
  clCumulant (frMoment κ)

theorem frMoment_classicalToFree (c : Nat → Int) (n : Nat) :
    frMoment (classicalToFree c) n = clMoment c n :=
  frMoment_frCumulant (clMoment c) (clMoment_zero c) n

theorem clMoment_freeToClassical (κ : Nat → Int) (n : Nat) :
    clMoment (freeToClassical κ) n = frMoment κ n :=
  clMoment_clCumulant (frMoment κ) (frMoment_zero κ) n

/-- Round-trip bijection: `freeToClassical (classicalToFree c) = c` on all orders `n ≥ 1`. -/
theorem freeToClassical_classicalToFree (c : Nat → Int) (n : Nat) (hn : 1 ≤ n) :
    freeToClassical (classicalToFree c) n = c n := by
  unfold freeToClassical
  have hcongr : clCumulant (frMoment (classicalToFree c)) n = clCumulant (clMoment c) n := by
    -- Functions `frMoment (classicalToFree c)` and `clMoment c` are pointwise equal!
    have hfun : frMoment (classicalToFree c) = clMoment c := by
      funext k
      exact frMoment_classicalToFree c k
    rw [hfun]
  rw [hcongr]
  exact clCumulant_clMoment c n hn

/-- Round-trip bijection: `classicalToFree (freeToClassical κ) = κ` on all orders `n ≥ 1`. -/
theorem classicalToFree_freeToClassical (κ : Nat → Int) (n : Nat) (hn : 1 ≤ n) :
    classicalToFree (freeToClassical κ) n = κ n := by
  unfold classicalToFree
  have hfun : clMoment (freeToClassical κ) = frMoment κ := by
    funext k
    exact clMoment_freeToClassical κ k
  rw [hfun]
  exact frCumulant_frMoment κ n hn

end Conjecture00000004763
