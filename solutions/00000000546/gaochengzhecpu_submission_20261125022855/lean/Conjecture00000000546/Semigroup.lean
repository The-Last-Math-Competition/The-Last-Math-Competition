/-
  Conjecture 00000000546 — Interval Numerical Semigroups, Eliahou Depth, and Symmetric Gaps
  Core Lean 4.19.0
-/
import Conjecture00000000546.Basic

namespace Conjecture00000000546

/-! ## 1. Interval Numerical Semigroup `⟨a, a+1, …, a+k⟩` and Generator Sumsets -/

/-- Exact membership in the numerical semigroup `S_{a,k} = ⟨a, a+1, …, a+k⟩`. -/
inductive InIntervalSemigroup (a k : Nat) : Nat → Prop where
  | zero : InIntervalSemigroup a k 0
  | add_gen {s g : Nat} :
      InIntervalSemigroup a k s → a ≤ g → g ≤ a + k → InIntervalSemigroup a k (s + g)

/-- Exact membership in the `r`-fold sumset `r · {a, a+1, …, a+k}`. -/
inductive InGenSumset (a k : Nat) : Nat → Nat → Prop where
  | zero : InGenSumset a k 0 0
  | step {r s g : Nat} :
      InGenSumset a k r s → a ≤ g → g ≤ a + k → InGenSumset a k (r + 1) (s + g)

theorem inGenSumset_iff_interval (a k r s : Nat) :
    InGenSumset a k r s ↔ r * a ≤ s ∧ s ≤ r * (a + k) := by
  induction r generalizing s with
  | zero =>
    constructor
    · intro h
      cases h
      omega
    · intro h
      have hs : s = 0 := by omega
      subst hs
      exact InGenSumset.zero
  | succ r ih =>
    constructor
    · intro h
      cases h with
      | step hprev hga hgk =>
        rcases (ih _).mp hprev with ⟨hlow, hhigh⟩
        have h1 : (r + 1) * a = r * a + a := Nat.succ_mul r a
        have h2 : (r + 1) * (a + k) = r * (a + k) + (a + k) := Nat.succ_mul r (a + k)
        omega
    · rintro ⟨hlow, hhigh⟩
      have h1 : (r + 1) * a = r * a + a := Nat.succ_mul r a
      have h2 : (r + 1) * (a + k) = r * (a + k) + (a + k) := Nat.succ_mul r (a + k)
      have hra_le : r * a ≤ r * (a + k) := Nat.mul_le_mul_left r (by omega)
      by_cases hcase : s - r * a ≤ a + k
      · have hs_eq : r * a + (s - r * a) = s := by omega
        rw [← hs_eq]
        exact InGenSumset.step ((ih (r * a)).mpr ⟨Nat.le_refl _, hra_le⟩) (by omega) hcase
      · have hs_eq : (s - (a + k)) + (a + k) = s := by omega
        rw [← hs_eq]
        exact InGenSumset.step
          ((ih (s - (a + k))).mpr ⟨by omega, by omega⟩)
          (by omega) (Nat.le_refl _)

theorem inIntervalSemigroup_iff_exists_sumset (a k s : Nat) :
    InIntervalSemigroup a k s ↔ ∃ r, InGenSumset a k r s := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨0, InGenSumset.zero⟩
    | add_gen _ hga hgk ih =>
      rcases ih with ⟨r, hr⟩
      exact ⟨r + 1, InGenSumset.step hr hga hgk⟩
  · rintro ⟨r, hr⟩
    induction hr with
    | zero => exact InIntervalSemigroup.zero
    | step _ hga hgk ih => exact InIntervalSemigroup.add_gen ih hga hgk

theorem inIntervalSemigroup_iff_exists_interval (a k s : Nat) :
    InIntervalSemigroup a k s ↔ ∃ r, r * a ≤ s ∧ s ≤ r * (a + k) := by
  rw [inIntervalSemigroup_iff_exists_sumset]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (inGenSumset_iff_interval a k r s).mp hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, (inGenSumset_iff_interval a k r s).mpr hr⟩

theorem inIntervalSemigroup_add {a k x y : Nat}
    (hx : InIntervalSemigroup a k x) (hy : InIntervalSemigroup a k y) :
    InIntervalSemigroup a k (x + y) := by
  rw [inIntervalSemigroup_iff_exists_interval] at hx hy ⊢
  rcases hx with ⟨r1, h1, h2⟩
  rcases hy with ⟨r2, h3, h4⟩
  refine ⟨r1 + r2, ?_, ?_⟩
  · rw [Nat.add_mul]
    omega
  · rw [Nat.add_mul]
    omega

theorem inIntervalSemigroup_ge_a {a k x : Nat}
    (hx : InIntervalSemigroup a k x) (hpos : 0 < x) : a ≤ x := by
  rw [inIntervalSemigroup_iff_exists_interval] at hx
  rcases hx with ⟨r, hlow, _⟩
  cases r with
  | zero => omega
  | succ r =>
    have : (r + 1) * a = r * a + a := Nat.succ_mul r a
    omega

/-! ## 2. General Numerical Semigroup Invariants -/

/-- `m` is the multiplicity (smallest positive element) of `S`. -/
def IsMultiplicity (S : Nat → Prop) (m : Nat) : Prop :=
  0 < m ∧ S m ∧ ∀ x, 0 < x → S x → m ≤ x

/-- `c` is the conductor (least integer from which all `n ≥ c` lie in `S`). -/
def IsConductor (S : Nat → Prop) (c : Nat) : Prop :=
  (∀ n, c ≤ n → S n) ∧ (∀ c', (∀ n, c' ≤ n → S n) → c ≤ c')

/-- `F` is the Frobenius number (largest gap) of `S`. -/
def IsFrobeniusNumber (S : Nat → Prop) (F : Nat) : Prop :=
  ¬ S F ∧ ∀ n, F < n → S n

/-- `S` has symmetric gaps (is a symmetric numerical semigroup) with Frobenius number `F`. -/
def HasSymmetricGaps (S : Nat → Prop) (F : Nat) : Prop :=
  IsFrobeniusNumber S F ∧ ∀ x, x ≤ F → (S x ↔ ¬ S (F - x))

/-- Eliahou's depth `q(S) = ⌈C(S) / m(S)⌉` of a numerical semigroup `S`. -/
def IsEliahouDepth (S : Nat → Prop) (q : Nat) : Prop :=
  ∃ c m, IsConductor S c ∧ IsMultiplicity S m ∧ q = ceilDiv c m

/-! ## 3. Exact Multiplicity, Conductor, Frobenius Number, and Eliahou Depth of `S_{a,k}` -/

theorem multiplicity_intervalSemigroup {a k : Nat} (ha : 0 < a) :
    IsMultiplicity (InIntervalSemigroup a k) a := by
  refine ⟨ha, ?_, ?_⟩
  · have hmem := InIntervalSemigroup.add_gen (a := a) (k := k)
      InIntervalSemigroup.zero (Nat.le_refl a) (by omega)
    rwa [Nat.zero_add] at hmem
  · intro x hx hs
    exact inIntervalSemigroup_ge_a hs hx

/-- Below `⌈(a-1)/k⌉ * a`, the intervals `[r*a, r*(a+k)]` do not hit `⌈(a-1)/k⌉ * a - 1`. -/
theorem gap_before_conductor {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) :
    ¬ InIntervalSemigroup a k (ceilDiv (a - 1) k * a - 1) := by
  have hq_pos : 0 < ceilDiv (a - 1) k := ceilDiv_pos (by omega) (by omega)
  have hq_low : (ceilDiv (a - 1) k - 1) * k < a - 1 := ceilDiv_spec_lower (by omega) (by omega)
  rw [inIntervalSemigroup_iff_exists_interval]
  rintro ⟨r, hr_low, hr_high⟩
  by_cases hrq : ceilDiv (a - 1) k ≤ r
  · have hmul : ceilDiv (a - 1) k * a ≤ r * a := Nat.mul_le_mul_right a hrq
    have hqa_pos : 0 < ceilDiv (a - 1) k * a := Nat.mul_pos hq_pos (by omega)
    omega
  · have hr_le : r ≤ ceilDiv (a - 1) k - 1 := by omega
    have hmul : r * (a + k) ≤ (ceilDiv (a - 1) k - 1) * (a + k) :=
      Nat.mul_le_mul_right (a + k) hr_le
    have hexp1 : (ceilDiv (a - 1) k - 1) * (a + k) =
        (ceilDiv (a - 1) k - 1) * a + (ceilDiv (a - 1) k - 1) * k :=
      Nat.mul_add _ a k
    have hexp2 : ceilDiv (a - 1) k * a = (ceilDiv (a - 1) k - 1) * a + a := by
      have : ceilDiv (a - 1) k - 1 + 1 = ceilDiv (a - 1) k := by omega
      calc ceilDiv (a - 1) k * a = (ceilDiv (a - 1) k - 1 + 1) * a := by rw [this]
        _ = (ceilDiv (a - 1) k - 1) * a + a := Nat.succ_mul _ a
    omega

/-- Every integer `n ≥ ⌈(a-1)/k⌉ * a` belongs to `S_{a,k}`. -/
theorem mem_of_ge_conductor {a k n : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k)
    (hn : ceilDiv (a - 1) k * a ≤ n) :
    InIntervalSemigroup a k n := by
  have hq_up : a - 1 ≤ ceilDiv (a - 1) k * k := ceilDiv_spec_upper (by omega)
  have hdiv := Nat.div_add_mod n a
  have hmod : n % a < a := Nat.mod_lt n (by omega)
  have hr_ge : ceilDiv (a - 1) k ≤ n / a := by
    by_cases hge : ceilDiv (a - 1) k ≤ n / a
    · exact hge
    · have hr1 : n / a + 1 ≤ ceilDiv (a - 1) k := by omega
      have hmul : a * (n / a + 1) ≤ a * ceilDiv (a - 1) k := Nat.mul_le_mul_left a hr1
      have hcomm1 : a * (n / a + 1) = a * (n / a) + a := Nat.mul_succ a (n / a)
      have hcomm2 : a * ceilDiv (a - 1) k = ceilDiv (a - 1) k * a := Nat.mul_comm a _
      omega
  rw [inIntervalSemigroup_iff_exists_interval]
  refine ⟨n / a, ?_, ?_⟩
  · have hcomm : (n / a) * a = a * (n / a) := Nat.mul_comm _ a
    omega
  · have hqk : ceilDiv (a - 1) k * k ≤ (n / a) * k := Nat.mul_le_mul_right k hr_ge
    have hexp : (n / a) * (a + k) = a * (n / a) + (n / a) * k := by
      rw [Nat.mul_add, Nat.mul_comm (n / a) a]
    omega

theorem conductor_intervalSemigroup {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) :
    IsConductor (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a) := by
  refine ⟨fun n hn => mem_of_ge_conductor ha hk hn, ?_⟩
  intro c' hc'
  by_cases hle : ceilDiv (a - 1) k * a ≤ c'
  · exact hle
  · have hq_pos : 0 < ceilDiv (a - 1) k := ceilDiv_pos (by omega) (by omega)
    have hqa_pos : 0 < ceilDiv (a - 1) k * a := Nat.mul_pos hq_pos (by omega)
    have hmem : InIntervalSemigroup a k (ceilDiv (a - 1) k * a - 1) := hc' _ (by omega)
    exact False.elim (gap_before_conductor ha hk hmem)

theorem frobenius_intervalSemigroup {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) :
    IsFrobeniusNumber (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1) := by
  have hq_pos : 0 < ceilDiv (a - 1) k := ceilDiv_pos (by omega) (by omega)
  have hqa_pos : 0 < ceilDiv (a - 1) k * a := Nat.mul_pos hq_pos (by omega)
  refine ⟨gap_before_conductor ha hk, ?_⟩
  intro n hn
  exact mem_of_ge_conductor ha hk (by omega)

/-- **Exact Eliahou Depth Theorem**: `q(S_{a,k}) = ⌈(a-1)/k⌉` for all `a ≥ 2, k ≥ 1`. -/
theorem eliahouDepth_intervalSemigroup {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) :
    IsEliahouDepth (InIntervalSemigroup a k) (ceilDiv (a - 1) k) := by
  refine ⟨ceilDiv (a - 1) k * a, a, conductor_intervalSemigroup ha hk,
          multiplicity_intervalSemigroup (by omega), ?_⟩
  exact (ceilDiv_mul_self (q := ceilDiv (a - 1) k) (k := a) (by omega)).symm

theorem eliahouDepth_unique {S : Nat → Prop} {q1 q2 : Nat}
    (h1 : IsEliahouDepth S q1) (h2 : IsEliahouDepth S q2) : q1 = q2 := by
  rcases h1 with ⟨c1, m1, hc1, hm1, rfl⟩
  rcases h2 with ⟨c2, m2, hc2, hm2, rfl⟩
  have hc : c1 = c2 := Nat.le_antisymm (hc1.2 c2 hc2.1) (hc2.2 c1 hc1.1)
  have hm : m1 = m2 := Nat.le_antisymm (hm1.2.2 m2 hm2.1 hm2.2.1) (hm2.2.2 m1 hm1.1 hm1.2.1)
  rw [hc, hm]

/-- **Exact Failure Locus of `⌈a/k⌉` vs True Eliahou Depth `⌈(a-1)/k⌉`**:
    They disagree if and only if `(a - 1) % k = 0` (including ALL `a ≥ 2` when `k = 1`). -/
theorem eliahouDepth_ne_conjectured_iff {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) :
    ceilDiv (a - 1) k ≠ ceilDiv a k ↔ (a - 1) % k = 0 := by
  have heq : (a - 1) + 1 = a := by omega
  have hiff := ceilDiv_succ_gt_iff (m := a - 1) (k := k) (by omega)
  have hle := ceilDiv_le_succ (a - 1) k
  rw [heq] at hiff hle
  omega

/-- Refutation for ALL `a ≥ 2` at `k = 1`: `q(⟨a, a+1⟩) = a - 1 ≠ a = ⌈a/1⌉`. -/
theorem eliahouDepth_k_eq_one_counterexample {a : Nat} (ha : 2 ≤ a) :
    ¬ IsEliahouDepth (InIntervalSemigroup a 1) (ceilDiv a 1) := by
  intro hbad
  have htrue := eliahouDepth_intervalSemigroup ha (Nat.le_refl 1)
  have heq := eliahouDepth_unique htrue hbad
  have hne : ceilDiv (a - 1) 1 ≠ ceilDiv a 1 :=
    (eliahouDepth_ne_conjectured_iff ha (Nat.le_refl 1)).mpr (Nat.mod_one _)
  exact hne heq

/-! ## 4. Ordinary Power-Truncation Semigroup `S_{a,k}^{(m)}` Threshold -/

/-- `m`-th power subsemigroup `{0} ∪ ⋃_{r ≥ m} r · {a, …, a+k}`. -/
def InPowerSemigroup (a k m s : Nat) : Prop :=
  s = 0 ∨ ∃ r, m ≤ r ∧ r * a ≤ s ∧ s ≤ r * (a + k)

/-- `S_{a,k}^{(m)}` is ordinary (every integer `≥ m*a` lies in `S_{a,k}^{(m)}`, so its
    Eliahou depth drops to `1`) if and only if `m ≥ ⌈(a-1)/k⌉`. -/
theorem powerSemigroup_ordinary_iff {a k m : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (∀ n, m * a ≤ n → InPowerSemigroup a k m n) ↔ ceilDiv (a - 1) k ≤ m := by
  constructor
  · intro hord
    rw [le_ceilDiv_iff (by omega)]
    by_cases hle : a - 1 ≤ m * k
    · exact hle
    · have hexp_mak : m * (a + k) = m * a + m * k := Nat.mul_add m a k
      have hn_ge : m * a ≤ m * (a + k) + 1 := by omega
      rcases hord (m * (a + k) + 1) hn_ge with hn0 | ⟨r, hmr, hr_low, hr_high⟩
      · omega
      · by_cases hrm : r = m
        · subst hrm
          omega
        · have hr1 : m + 1 ≤ r := by omega
          have hmul : (m + 1) * a ≤ r * a := Nat.mul_le_mul_right a hr1
          have hexp1 : (m + 1) * a = m * a + a := Nat.succ_mul m a
          omega
  · intro hm_ge n hn
    right
    have hmk : a - 1 ≤ m * k := (le_ceilDiv_iff (by omega)).mp hm_ge
    have hdiv := Nat.div_add_mod n a
    have hmod : n % a < a := Nat.mod_lt n (by omega)
    have hr_ge : m ≤ n / a := by
      by_cases hge : m ≤ n / a
      · exact hge
      · have hr1 : n / a + 1 ≤ m := by omega
        have hmul : a * (n / a + 1) ≤ a * m := Nat.mul_le_mul_left a hr1
        have hcomm1 : a * (n / a + 1) = a * (n / a) + a := Nat.mul_succ a (n / a)
        have hcomm2 : a * m = m * a := Nat.mul_comm a m
        omega
    refine ⟨n / a, hr_ge, ?_, ?_⟩
    · have hcomm : (n / a) * a = a * (n / a) := Nat.mul_comm _ a
      omega
    · have hmk_r : m * k ≤ (n / a) * k := Nat.mul_le_mul_right k hr_ge
      have hexp : (n / a) * (a + k) = a * (n / a) + (n / a) * k := by
        rw [Nat.mul_add, Nat.mul_comm (n / a) a]
      omega

/-! ## 5. Exact Classification of Symmetric Gaps & the Symmetric-Gap Depth Jump -/

/-- Below `⌈(a-1)/k⌉ * a`, `s ∈ S_{a,k}` iff `s % a ≤ (s / a) * k`. -/
theorem mem_below_conductor_iff {a k s : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k)
    (hs : s < ceilDiv (a - 1) k * a) :
    InIntervalSemigroup a k s ↔ s % a ≤ (s / a) * k := by
  have hq_pos : 0 < ceilDiv (a - 1) k := ceilDiv_pos (by omega) (by omega)
  have hq_low : (ceilDiv (a - 1) k - 1) * k < a - 1 := ceilDiv_spec_lower (by omega) (by omega)
  constructor
  · intro hmem
    rw [inIntervalSemigroup_iff_exists_interval] at hmem
    rcases hmem with ⟨r, hr_low, hr_high⟩
    have hr_lt : r < ceilDiv (a - 1) k := by
      by_cases hlt : r < ceilDiv (a - 1) k
      · exact hlt
      · have : ceilDiv (a - 1) k * a ≤ r * a := Nat.mul_le_mul_right a (by omega)
        omega
    have hr_le : r ≤ ceilDiv (a - 1) k - 1 := by omega
    have hrk_lt : r * k < a := by
      have : r * k ≤ (ceilDiv (a - 1) k - 1) * k := Nat.mul_le_mul_right k hr_le
      omega
    have hdiv := Nat.div_add_mod s a
    have hmod : s % a < a := Nat.mod_lt s (by omega)
    have hr_eq : s / a = r := by
      have hexp : r * (a + k) = r * a + r * k := Nat.mul_add r a k
      by_cases hlt1 : s / a < r
      · have h1 : s / a + 1 ≤ r := by omega
        have hmul : a * (s / a + 1) ≤ a * r := Nat.mul_le_mul_left a h1
        have hc1 : a * (s / a + 1) = a * (s / a) + a := Nat.mul_succ a (s / a)
        have hc2 : a * r = r * a := Nat.mul_comm a r
        omega
      · by_cases hgt1 : r < s / a
        · have h1 : r + 1 ≤ s / a := by omega
          have hmul : a * (r + 1) ≤ a * (s / a) := Nat.mul_le_mul_left a h1
          have hc1 : a * (r + 1) = r * a + a := by rw [Nat.mul_succ, Nat.mul_comm]
          omega
        · omega
    subst hr_eq
    have hexp : (s / a) * (a + k) = a * (s / a) + (s / a) * k := by
      rw [Nat.mul_add, Nat.mul_comm (s / a) a]
    omega
  · intro hmod_le
    rw [inIntervalSemigroup_iff_exists_interval]
    have hdiv := Nat.div_add_mod s a
    refine ⟨s / a, ?_, ?_⟩
    · have hc : (s / a) * a = a * (s / a) := Nat.mul_comm _ _
      omega
    · have hexp : (s / a) * (a + k) = a * (s / a) + (s / a) * k := by
        rw [Nat.mul_add, Nat.mul_comm (s / a) a]
      omega

/-- Helper lemma tying `(ceilDiv (a - 1) k - 1) * k = a - 2` to `k = 1 ∨ (a - 2) % k = 0`. -/
theorem sym_quotient_eq_of_mod {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k)
    (hcond : k = 1 ∨ (a - 2) % k = 0) :
    (ceilDiv (a - 1) k - 1) * k = a - 2 := by
  rcases hcond with rfl | hmod0
  · have hq : ceilDiv (a - 1) 1 = a - 1 := by
      rw [ceilDiv_eq_iff (by omega) (by omega)]
      omega
    rw [hq]
    omega
  · have hdiv := Nat.div_add_mod (a - 2) k
    have hm_eq : (a - 2) / k * k = a - 2 := by
      have hc : k * ((a - 2) / k) = (a - 2) / k * k := Nat.mul_comm _ _
      omega
    have hq_val : ceilDiv (a - 1) k = (a - 2) / k + 1 := by
      rw [ceilDiv_eq_iff (by omega) (by omega)]
      refine ⟨Nat.zero_lt_succ _, ?_, ?_⟩
      · rw [Nat.add_sub_cancel, hm_eq]
        omega
      · rw [Nat.succ_mul, hm_eq]
        omega
    rw [hq_val, Nat.add_sub_cancel, hm_eq]

/-- **Exact Symmetric-Gaps Classification**:
    For `a ≥ 2` and `1 ≤ k ≤ a - 1`, `S_{a,k}` has symmetric gaps if and only if
    `k = 1 ∨ (a - 2) % k = 0`. -/
theorem hasSymmetricGaps_iff {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a - 1) :
    HasSymmetricGaps (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1) ↔
      (k = 1 ∨ (a - 2) % k = 0) := by
  have hq_pos : 0 < ceilDiv (a - 1) k := ceilDiv_pos (by omega) (by omega)
  have hqa_ge : a ≤ ceilDiv (a - 1) k * a := by
    have : 1 * a ≤ ceilDiv (a - 1) k * a := Nat.mul_le_mul_right a hq_pos
    omega
  have hq_low : (ceilDiv (a - 1) k - 1) * k < a - 1 := ceilDiv_spec_lower (by omega) (by omega)
  constructor
  · intro hsym
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      have h1_not : ¬ InIntervalSemigroup a k 1 := by
        intro h1
        have := inIntervalSemigroup_ge_a h1 (by omega)
        omega
      have hF1_lt : (ceilDiv (a - 1) k * a - 1) - 1 < ceilDiv (a - 1) k * a := by omega
      have hmod_le : ((ceilDiv (a - 1) k * a - 1) - 1) % a ≤
          ((ceilDiv (a - 1) k * a - 1) - 1) / a * k := by
        have hiff := hsym.2 1 (by omega)
        have hmem_iff := mem_below_conductor_iff ha hk hF1_lt
        by_cases hle : ((ceilDiv (a - 1) k * a - 1) - 1) % a ≤
            ((ceilDiv (a - 1) k * a - 1) - 1) / a * k
        · exact hle
        · have hnot : ¬ InIntervalSemigroup a k ((ceilDiv (a - 1) k * a - 1) - 1) :=
            fun hm => hle (hmem_iff.mp hm)
          exact False.elim (h1_not (hiff.mpr hnot))
      have hsplit : (ceilDiv (a - 1) k * a - 1) - 1 =
          (a - 2) + a * (ceilDiv (a - 1) k - 1) := by
        have hexp : ceilDiv (a - 1) k * a = a * (ceilDiv (a - 1) k - 1) + a := by
          have hsub : ceilDiv (a - 1) k - 1 + 1 = ceilDiv (a - 1) k := by omega
          calc ceilDiv (a - 1) k * a = (ceilDiv (a - 1) k - 1 + 1) * a := by rw [hsub]
            _ = (ceilDiv (a - 1) k - 1) * a + a := Nat.succ_mul _ a
            _ = a * (ceilDiv (a - 1) k - 1) + a := by rw [Nat.mul_comm]
        omega
      have hdiv_eq : ((ceilDiv (a - 1) k * a - 1) - 1) / a = ceilDiv (a - 1) k - 1 := by
        rw [hsplit, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hmod_eq : ((ceilDiv (a - 1) k * a - 1) - 1) % a = a - 2 := by
        rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hdiv_eq, hmod_eq] at hmod_le
      have heq : (ceilDiv (a - 1) k - 1) * k = a - 2 := by omega
      rw [← heq, Nat.mul_mod_left]
  · intro hcond
    have _ := hka
    have hqk_eq : (ceilDiv (a - 1) k - 1) * k = a - 2 :=
      sym_quotient_eq_of_mod ha hk hcond
    refine ⟨frobenius_intervalSemigroup ha hk, ?_⟩
    intro x hx
    have hx_lt : x < ceilDiv (a - 1) k * a := by omega
    have hFx_lt : (ceilDiv (a - 1) k * a - 1) - x < ceilDiv (a - 1) k * a := by omega
    rw [mem_below_conductor_iff ha hk hx_lt, mem_below_conductor_iff ha hk hFx_lt]
    have hdiv_x : a * (x / a) + x % a = x := Nat.div_add_mod x a
    have hm_lt : x % a < a := Nat.mod_lt x (by omega)
    have hr_lt : x / a < ceilDiv (a - 1) k := by
      by_cases hlt : x / a < ceilDiv (a - 1) k
      · exact hlt
      · have hmul : ceilDiv (a - 1) k * a ≤ (x / a) * a := Nat.mul_le_mul_right a (by omega)
        have hc : (x / a) * a = a * (x / a) := Nat.mul_comm _ a
        omega
    have hFx_split : (ceilDiv (a - 1) k * a - 1) - x =
        (a - 1 - x % a) + a * (ceilDiv (a - 1) k - 1 - x / a) := by
      have hexp : ceilDiv (a - 1) k * a =
          a * (ceilDiv (a - 1) k - 1 - x / a) + a * (x / a) + a := by
        have hsum : (ceilDiv (a - 1) k - 1 - x / a) + x / a + 1 = ceilDiv (a - 1) k := by omega
        calc ceilDiv (a - 1) k * a
            = ((ceilDiv (a - 1) k - 1 - x / a) + x / a + 1) * a := by rw [hsum]
          _ = ((ceilDiv (a - 1) k - 1 - x / a) + x / a) * a + a := Nat.succ_mul _ a
          _ = (ceilDiv (a - 1) k - 1 - x / a) * a + (x / a) * a + a := by rw [Nat.add_mul]
          _ = a * (ceilDiv (a - 1) k - 1 - x / a) + a * (x / a) + a := by
                rw [Nat.mul_comm _ a, Nat.mul_comm (x / a) a]
      omega
    have hFx_div : ((ceilDiv (a - 1) k * a - 1) - x) / a =
        ceilDiv (a - 1) k - 1 - x / a := by
      rw [hFx_split, Nat.add_mul_div_left _ _ (by omega),
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have hFx_mod : ((ceilDiv (a - 1) k * a - 1) - x) % a = a - 1 - x % a := by
      rw [hFx_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hFx_div, hFx_mod]
    have hk_split : (ceilDiv (a - 1) k - 1 - x / a) * k + (x / a) * k = a - 2 := by
      have hsub : (ceilDiv (a - 1) k - 1 - x / a) + x / a = ceilDiv (a - 1) k - 1 := by omega
      calc (ceilDiv (a - 1) k - 1 - x / a) * k + (x / a) * k
          = ((ceilDiv (a - 1) k - 1 - x / a) + x / a) * k := (Nat.add_mul _ _ k).symm
        _ = (ceilDiv (a - 1) k - 1) * k := by rw [hsub]
        _ = a - 2 := hqk_eq
    omega

/-- **Exact Symmetric-Gap Depth-Jump Theorem** (for fixed `k ≥ 2`, stepping `a - 1 → a`):
    `S_{a,k}` has symmetric gaps if and only if the true Eliahou depth `q(S_{a,k}) = ⌈(a-1)/k⌉`
    jumps by `+1` over `q(S_{a-1,k}) = ⌈(a-2)/k⌉`! -/
theorem symmetricGaps_iff_eliahouDepth_jump {a k : Nat} (hk : 2 ≤ k) (ha : k + 2 ≤ a) :
    HasSymmetricGaps (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1) ↔
      ceilDiv (a - 2) k < ceilDiv (a - 1) k := by
  rw [hasSymmetricGaps_iff (by omega) (by omega) (by omega)]
  have heq : a - 1 = (a - 2) + 1 := by omega
  rw [heq, ceilDiv_succ_gt_iff (by omega)]
  constructor
  · rintro (rfl | hmod)
    · omega
    · exact hmod
  · intro hmod
    exact Or.inr hmod

/-- **Conjectured Formula `⌈a/k⌉` Destroys the Symmetric-Gap Depth Jump**:
    For every `k ≥ 2` and every symmetric-gap semigroup `S_{a,k}` (`a ≥ k + 2`),
    the conjectured quantity `⌈a/k⌉` has ZERO jump (`⌈a/k⌉ = ⌈(a-1)/k⌉`) between `a - 1` and `a`. -/
theorem conjectured_formula_no_jump_at_symmetricGaps {a k : Nat}
    (hk : 2 ≤ k) (ha : k + 2 ≤ a)
    (hsym : HasSymmetricGaps (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1)) :
    ceilDiv a k = ceilDiv (a - 1) k := by
  have hmod2 : (a - 2) % k = 0 := by
    rcases (hasSymmetricGaps_iff (by omega) (by omega) (by omega)).mp hsym with rfl | h
    · omega
    · exact h
  have hmod1_ne : (a - 1) % k ≠ 0 := by
    have heq1 : a - 1 = (a - 2) + 1 := by omega
    have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [heq1, Nat.add_mod, hmod2, Nat.zero_add, h1mod, h1mod]
    omega
  have heq : (a - 1) + 1 = a := by omega
  have hiff := ceilDiv_succ_gt_iff (m := a - 1) (k := k) (by omega)
  have hle := ceilDiv_le_succ (a - 1) k
  rw [heq] at hiff hle
  omega

/-- Dual depth-drop formulation as `k` increases (`k → k + 1`) at fixed `a`:
    Every symmetric-gap semigroup `S_{a,k}` (`1 ≤ k ≤ a - 2`) undergoes a strict Eliahou
    depth drop `q(S_{a,k+1}) < q(S_{a,k})`. -/
theorem eliahouDepth_strict_drop_at_symmetricGaps {a k : Nat}
    (hk : 1 ≤ k) (hka : k ≤ a - 2)
    (hsym : HasSymmetricGaps (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1)) :
    ceilDiv (a - 1) (k + 1) < ceilDiv (a - 1) k := by
  have hq_gt1 : 1 < ceilDiv (a - 1) k := by
    rw [lt_ceilDiv_iff (by omega)]
    omega
  have hcond := (hasSymmetricGaps_iff (by omega) (by omega) (by omega)).mp hsym
  have hqk_eq : (ceilDiv (a - 1) k - 1) * k = a - 2 :=
    sym_quotient_eq_of_mod (by omega) hk hcond
  have hle : ceilDiv (a - 1) (k + 1) ≤ ceilDiv (a - 1) k - 1 := by
    rw [le_ceilDiv_iff (by omega)]
    have hexp : (ceilDiv (a - 1) k - 1) * (k + 1) =
        (ceilDiv (a - 1) k - 1) * k + (ceilDiv (a - 1) k - 1) :=
      Nat.mul_succ _ k
    omega
  omega

end Conjecture00000000546
