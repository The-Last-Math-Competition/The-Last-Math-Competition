/-
  SpernerFD/Main.lean
  Main theorems resolving (disproving) Conjecture 00000008532 in both `FD(n)` and `FD_0(n)`:
    1. Explicit middle-slice antichain of size `binom (centralBinom n) (centralBinom n / 2)`
       giving doubly-exponential Sperner growth
       `w(FD(n)) ≥ 2^{centralBinom n} / (centralBinom n + 1)` and
       `w(FD(n)) ≥ 2^{2^{⌊n/2⌋ - 1}}` for all `n ≥ 2`.
    2. Complete classification of the sign of `Δ(n) = w(FD(n)) - binom(n, ⌊n/2⌋)`:
       `Δ(0) = Δ(1) = Δ(2) = 0` and `Δ(n) > 0 ↔ n ≥ 3` (refuting "always positive sign").
    3. Refutation of logarithmic order (as well as polynomial and singly-exponential order):
       for every threshold `n₀`, base `B`, and constants `C, D`, there exists `n ≥ n₀`
       with `Δ(n) > C * B^n + D` — in particular `Δ(n) ≠ O(log n)`.
-/

import SpernerFD.SmallN

namespace SpernerFD

/-! ## 1. Middle-Slice Monotone Boolean Function Family -/

/-- Given a subset `S` of the middle layer `weight x = n / 2`, define `midSliceRaw S : Cube n → Bool`
    taking `true` above the middle layer, `decide (x ∈ S)` on the middle layer, and `false` below. -/
def midSliceRaw {n : Nat} (S : List (Cube n)) (x : Cube n) : Bool :=
  if n / 2 < weight x then true
  else if weight x = n / 2 then decide (x ∈ S)
  else false

theorem midSliceRaw_isMonotone {n : Nat} (S : List (Cube n)) :
    IsMonotone (midSliceRaw S) := by
  intro x y hxy hfx
  have hwx : weight x ≤ weight y := cubeLe_weight_le hxy
  unfold midSliceRaw at hfx ⊢
  by_cases hgt : n / 2 < weight x
  · have hgy : n / 2 < weight y := by omega
    simp [hgy]
  · simp only [hgt, ↓reduceIte] at hfx
    by_cases heq : weight x = n / 2
    · simp only [heq, ↓reduceIte] at hfx
      by_cases hgy : n / 2 < weight y
      · simp [hgy]
      · have hwy : weight y = n / 2 := by omega
        have hxy_eq : x = y := cubeLe_eq_of_weight_eq hxy (by omega)
        subst hxy_eq
        simp [hgt, heq, hfx]
    · simp [heq] at hfx

/-- Monotone Boolean function `f_S ∈ FD n` associated with `S ⊆ {x : Cube n | weight x = n / 2}`. -/
def midSliceFD {n : Nat} (S : List (Cube n)) : FD n :=
  ⟨midSliceRaw S, midSliceRaw_isMonotone S⟩

/-- On subsets `S, T` of the middle layer, `f_S ≤ f_T` implies `S ⊆ T`. -/
theorem subset_of_midSliceFD_le {n : Nat} {S T : List (Cube n)}
    (hS : ∀ x ∈ S, weight x = n / 2)
    (hle : FDLe (midSliceFD S) (midSliceFD T)) :
    ∀ x ∈ S, x ∈ T := by
  intro x hxS
  have hwx : weight x = n / 2 := hS x hxS
  have hng : ¬ (n / 2 < weight x) := by omega
  have hfx : (midSliceFD S).val x = true := by
    change midSliceRaw S x = true
    simp [midSliceRaw, hng, hwx, hxS]
  have htx : (midSliceFD T).val x = true := hle x hfx
  change midSliceRaw T x = true at htx
  simp only [midSliceRaw, hwx, Nat.lt_irrefl, ↓reduceIte] at htx
  exact of_decide_eq_true htx

/-- Explicit middle-slice fixed-weight antichain in `FD n` of cardinality
    `binom (centralBinom n) (centralBinom n / 2)`. -/
def midSliceAntichain (n : Nat) : List (FD n) :=
  (chooseSublists (layerCubes n (n / 2)) (centralBinom n / 2)).map midSliceFD

theorem length_midSliceAntichain (n : Nat) :
    (midSliceAntichain n).length = centralBinom (centralBinom n) := by
  simp only [midSliceAntichain, List.length_map, length_chooseSublists,
    length_layerCubes, centralBinom]

theorem isAntichain_midSliceAntichain (n : Nat) :
    IsAntichain FDLe (midSliceAntichain n) := by
  let M := layerCubes n (n / 2)
  let k := centralBinom n / 2
  let subs := chooseSublists M k
  have hMnd : NoDup M := noDup_layerCubes n (n / 2)
  have hsubs_nd : NoDup subs := noDup_chooseSublists hMnd k
  -- Core rigidity: if `S, T ∈ subs` satisfy `FDLe (midSliceFD S) (midSliceFD T)`, then `S = T`.
  have hrigid : ∀ S ∈ subs, ∀ T ∈ subs, FDLe (midSliceFD S) (midSliceFD T) → S = T := by
    intro S hSm T hTm hle
    obtain ⟨hSlen, hSsubM⟩ := mem_chooseSublists_props hSm
    obtain ⟨hTlen, _⟩ := mem_chooseSublists_props hTm
    have hSnd : NoDup S := noDup_of_mem_chooseSublists hMnd hSm
    have hSwt : ∀ x ∈ S, weight x = n / 2 :=
      fun x hx => (mem_layerCubes_iff x).mp (hSsubM x hx)
    have hSsubT : ∀ x ∈ S, x ∈ T := subset_of_midSliceFD_le hSwt hle
    have hTsubS : ∀ x ∈ T, x ∈ S :=
      subset_symm_of_noDup_length_le hSnd hSsubT (by omega)
    exact eq_of_mem_chooseSublists_ext hMnd hSm hTm
      (fun x => ⟨hSsubT x, hTsubS x⟩)
  refine ⟨?_, ?_⟩
  · apply noDup_map _ hsubs_nd
    intro S hSm T hTm heq
    exact hrigid S hSm T hTm (by rw [heq]; exact fdLe_refl _)
  · intro f hf g hg hfg
    rcases List.mem_map.mp hf with ⟨S, hSm, rfl⟩
    rcases List.mem_map.mp hg with ⟨T, hTm, rfl⟩
    rw [hrigid S hSm T hTm hfg]

/-! ## 2. Doubly-Exponential Lower Bounds on `spernerFD` and `spernerFD0` -/

/-- **Iterated Central Binomial Lower Bound:**
    `w(FD(n)) ≥ binom(centralBinom n, centralBinom n / 2)` for every `n : Nat`. -/
theorem spernerFD_ge_iterated_centralBinom (n : Nat) :
    centralBinom (centralBinom n) ≤ spernerFD n := by
  rw [← length_midSliceAntichain n]
  exact antichain_le_spernerFD (isAntichain_midSliceAntichain n)

theorem spernerFD0_ge_iterated_centralBinom {n : Nat} (hn : 1 ≤ n) :
    centralBinom (centralBinom n) ≤ spernerFD0 n := by
  rw [spernerFD0_eq_spernerFD hn]
  exact spernerFD_ge_iterated_centralBinom n

/-- Explicit lower bound `(N_n + 1) * w(FD(n)) ≥ 2^{N_n}` where `N_n = binom(n, ⌊n/2⌋)`. -/
theorem spernerFD_mul_succ_ge_two_pow_centralBinom (n : Nat) :
    2 ^ (centralBinom n) ≤ (centralBinom n + 1) * spernerFD n := by
  have h1 := centralBinom_mul_succ_ge_two_pow (centralBinom n)
  have h2 := spernerFD_ge_iterated_centralBinom n
  exact Nat.le_trans h1 (Nat.mul_le_mul_left (centralBinom n + 1) h2)

/-- Denominator-free doubly-exponential lower bound:
    for all `n ≥ 2`, `w(FD(n)) = w(FD_0(n)) ≥ 2 ^ (2 ^ (n / 2 - 1))`. -/
theorem spernerFD_ge_double_exp {n : Nat} (hn : 2 ≤ n) :
    2 ^ (2 ^ (n / 2 - 1)) ≤ spernerFD n := by
  have hN : 2 ^ (n / 2) ≤ centralBinom n := centralBinom_ge_two_pow_half n
  have hpow : 2 * 2 ^ (n / 2 - 1) = 2 ^ (n / 2) := by
    have hdiv : n / 2 = (n / 2 - 1) + 1 := by omega
    conv => rhs; rw [hdiv, Nat.pow_succ]
    omega
  have hhalf : 2 ^ (n / 2 - 1) ≤ centralBinom n / 2 := by omega
  have hmono : ∀ a b : Nat, a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    have haux : ∀ d, 2 ^ a ≤ 2 ^ (a + d) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [Nat.add_succ, Nat.pow_succ]
        omega
    have := haux (b - a)
    rwa [Nat.add_sub_of_le hab] at this
  have hstep1 : 2 ^ (2 ^ (n / 2 - 1)) ≤ 2 ^ (centralBinom n / 2) := hmono _ _ hhalf
  have hstep2 : 2 ^ (centralBinom n / 2) ≤ centralBinom (centralBinom n) :=
    centralBinom_ge_two_pow_half (centralBinom n)
  exact Nat.le_trans hstep1 (Nat.le_trans hstep2 (spernerFD_ge_iterated_centralBinom n))

theorem spernerFD0_ge_double_exp {n : Nat} (hn : 2 ≤ n) :
    2 ^ (2 ^ (n / 2 - 1)) ≤ spernerFD0 n := by
  rw [spernerFD0_eq_spernerFD (by omega)]
  exact spernerFD_ge_double_exp hn

/-! ## 3. Complete Classification of Sign & Refutation of Always-Positive Sign -/

theorem centralBinom_ge_six_of_ge_four {n : Nat} (hn : 4 ≤ n) : 6 ≤ centralBinom n := by
  have hle : binom n 2 ≤ centralBinom n := binom_le_central n 2
  have htwo := binom_two_right n
  have hmul : 12 ≤ n * (n - 1) := by
    have h1 : 4 ≤ n := hn
    have h2 : 3 ≤ n - 1 := by omega
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
    omega
  omega

/-- Strict positivity of `Δ(n)` holds for every `n ≥ 3`. -/
theorem spernerCorrectionFD_pos_of_ge_three {n : Nat} (hn : 3 ≤ n) :
    0 < spernerCorrectionFD n := by
  by_cases hn3 : n = 3
  · subst hn3
    rw [spernerCorrectionFD_three]
    decide
  · have hn4 : 4 ≤ n := by omega
    have hN6 : 6 ≤ centralBinom n := centralBinom_ge_six_of_ge_four hn4
    have hgt : centralBinom n < centralBinom (centralBinom n) :=
      centralBinom_gt_self (by omega)
    have hsp : centralBinom (centralBinom n) ≤ spernerFD n :=
      spernerFD_ge_iterated_centralBinom n
    unfold spernerCorrectionFD
    omega

/-- **Exact Sign Classification for `FD(n)`:**
    `spernerCorrectionFD n > 0 ↔ 3 ≤ n` (while `Δ(0) = Δ(1) = Δ(2) = 0`). -/
theorem spernerCorrectionFD_pos_iff (n : Nat) :
    0 < spernerCorrectionFD n ↔ 3 ≤ n := by
  constructor
  · intro hpos
    match n with
    | 0 => rw [spernerCorrectionFD_zero] at hpos; omega
    | 1 => rw [spernerCorrectionFD_one] at hpos; omega
    | 2 => rw [spernerCorrectionFD_two] at hpos; omega
    | _ + 3 => omega
  · exact spernerCorrectionFD_pos_of_ge_three

/-- **Exact Sign Classification for `FD_0(n)` (`n ≥ 1`):**
    `spernerCorrectionFD0 n > 0 ↔ 3 ≤ n` (while `Δ_0(1) = Δ_0(2) = 0` and `Δ_0(0) = -1`). -/
theorem spernerCorrectionFD0_pos_iff {n : Nat} (hn : 1 ≤ n) :
    0 < spernerCorrectionFD0 n ↔ 3 ≤ n := by
  rw [spernerCorrectionFD0_eq_spernerCorrectionFD hn]
  exact spernerCorrectionFD_pos_iff n

/-- **Refutation of Always-Positive Sign (Part 1 of Conjecture 00000008532):**
    Fails at `n = 1` and `n = 2` (and `n = 0`) in both `FD(n)` and `FD_0(n)`. -/
theorem not_always_positive_FD : ¬ (∀ n : Nat, 0 < spernerCorrectionFD n) := by
  intro h
  have h1 := h 1
  rw [spernerCorrectionFD_one] at h1
  omega

theorem not_always_positive_FD_pos_n : ¬ (∀ n : Nat, 1 ≤ n → 0 < spernerCorrectionFD n) := by
  intro h
  have h2 := h 2 (by decide)
  rw [spernerCorrectionFD_two] at h2
  omega

theorem not_always_positive_FD0 : ¬ (∀ n : Nat, 0 < spernerCorrectionFD0 n) := by
  intro h
  have h1 := h 1
  rw [spernerCorrectionFD0_one] at h1
  omega

theorem not_always_positive_FD0_pos_n : ¬ (∀ n : Nat, 1 ≤ n → 0 < spernerCorrectionFD0 n) := by
  intro h
  have h2 := h 2 (by decide)
  rw [spernerCorrectionFD0_two] at h2
  omega

/-! ## 4. Doubly-Exponential Blowup & Refutation of Logarithmic Order -/

theorem two_pow_mono {a b : Nat} (hab : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  have haux : ∀ d, 2 ^ a ≤ 2 ^ (a + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, Nat.pow_succ]
      omega
  have := haux (b - a)
  rwa [Nat.add_sub_of_le hab] at this

theorem pow_mono_base {a b k : Nat} (hab : a ≤ b) : a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul ih hab

theorem quad_domination_aux {K M m : Nat}
    (hm4 : 4 ≤ m) (hmKM : 2 * K + M + 1 ≤ m) :
    K * (2 * (m + 1)) + (M + 1) ≤ 2 ^ m := by
  have hsq : m * m ≤ 2 ^ m := sq_le_two_pow hm4
  have hm_ge : 2 * K + 1 ≤ m := by omega
  have hmul : (2 * K + 1) * m ≤ m * m := Nat.mul_le_mul_right m hm_ge
  have hexpand : (2 * K + 1) * m = 2 * K * m + m := by
    rw [Nat.add_mul, Nat.one_mul]
  have hKn : K * (2 * (m + 1)) = 2 * K * m + 2 * K := by
    rw [← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_add, Nat.mul_one]
  have hle : K * (2 * (m + 1)) + (M + 1) ≤ (2 * K + 1) * m := by
    rw [hKn, hexpand]
    omega
  exact Nat.le_trans hle (Nat.le_trans hmul hsq)

theorem prod_three_gt_linear {X Y Z B_pow C D : Nat}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hBY : B_pow ≤ Y) (hZ : C + D + 3 ≤ Z) :
    X + C * B_pow + D + 2 ≤ X * Y * Z := by
  have hXY_ge_X : X ≤ X * Y := by
    have := Nat.mul_le_mul_left X hY
    simpa using this
  have hXY_ge_Y : Y ≤ X * Y := by
    have := Nat.mul_le_mul_right Y hX
    simpa using this
  have hXY_pos : 1 ≤ X * Y := Nat.le_trans hX hXY_ge_X
  have h1 : X * Y * (1 + C + (D + 2)) ≤ X * Y * Z :=
    Nat.mul_le_mul_left (X * Y) (by omega)
  have h2 : X * Y * (1 + C + (D + 2)) = X * Y + X * Y * C + X * Y * (D + 2) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have h3 : C * B_pow ≤ X * Y * C := by
    rw [Nat.mul_comm (X * Y) C]
    exact Nat.mul_le_mul_left C (Nat.le_trans hBY hXY_ge_Y)
  have h4 : D + 2 ≤ X * Y * (D + 2) := by
    have := Nat.mul_le_mul_right (D + 2) hXY_pos
    simpa using this
  exact Nat.le_trans (by omega) h1

theorem nat_log2_le_self (n : Nat) : Nat.log2 n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind k ih =>
    rw [Nat.log2]
    split
    · next hk2 =>
      have hlt : k / 2 < k := by omega
      have ihk := ih (k / 2) hlt
      omega
    · omega

theorem one_le_pow_of_pos (k : Nat) {b : Nat} (hb : 1 ≤ b) : 1 ≤ b ^ k := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
    rw [Nat.pow_succ]
    have hmul : b ^ k * 1 ≤ b ^ k * b := Nat.mul_le_mul_left (b ^ k) hb
    omega

theorem exp_decomp_aux (n B E : Nat) :
    2 ^ ((B + 1) * n + E) = 2 ^ n * (2 ^ B) ^ n * 2 ^ E := by
  have hbn : (B + 1) * n = n + B * n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hbn, Nat.pow_add, Nat.pow_add, Nat.pow_mul]

/-- **Master Super-Exponential Domination Theorem:**
    For every threshold `n₀`, base `B`, and constants `C, D`, there exists `n ≥ n₀`
    (with `n ≥ 10`) such that `Δ(n) = w(FD(n)) - binom(n, ⌊n/2⌋) > C * B^n + D`
    (simultaneously for both `FD(n)` and `FD_0(n)`). -/
theorem correction_exceeds_any_exponential (n₀ C D B : Nat) :
    ∃ n : Nat, n₀ ≤ n ∧ 1 ≤ n ∧
      ((C * B ^ n + D : Nat) : Int) < spernerCorrectionFD n ∧
      ((C * B ^ n + D : Nat) : Int) < spernerCorrectionFD0 n := by
  let K : Nat := B + 1
  let M : Nat := C + D + 2
  let m₀ : Nat := max 4 (max n₀ (2 * K + M + 1))
  have hm4 : 4 ≤ m₀ := by simp [m₀]; omega
  have hm_n0 : n₀ ≤ m₀ := by simp [m₀]; omega
  have hm_KM : 2 * K + M + 1 ≤ m₀ := by simp [m₀]; omega
  let n : Nat := 2 * (m₀ + 1)
  have hn_n0 : n₀ ≤ n := by omega
  have hn_ge2 : 2 ≤ n := by omega
  have hhalf : n / 2 - 1 = m₀ := by omega
  have hexp1 : (B + 1) * n + (C + D + 3) ≤ 2 ^ (n / 2 - 1) := by
    rw [hhalf]
    exact quad_domination_aux (K := K) (M := M) hm4 hm_KM
  have hsp_ge : 2 ^ ((B + 1) * n + (C + D + 3)) ≤ spernerFD n :=
    Nat.le_trans (two_pow_mono hexp1) (spernerFD_ge_double_exp hn_ge2)
  have hdecomp : 2 ^ ((B + 1) * n + (C + D + 3)) =
      2 ^ n * (2 ^ B) ^ n * 2 ^ (C + D + 3) :=
    exp_decomp_aux n B (C + D + 3)
  have hprod : 2 ^ n + C * B ^ n + D + 2 ≤ 2 ^ n * (2 ^ B) ^ n * 2 ^ (C + D + 3) :=
    prod_three_gt_linear
      (one_le_pow_of_pos n (by decide))
      (one_le_pow_of_pos n (one_le_pow_of_pos B (by decide)))
      (pow_mono_base (Nat.le_of_lt (lt_two_pow_self B)))
      (Nat.le_of_lt (lt_two_pow_self (C + D + 3)))
  have hN_le_X : centralBinom n ≤ 2 ^ n := binom_le_two_pow n (n / 2)
  have hsum_le_sp : 2 ^ n + C * B ^ n + D + 2 ≤ spernerFD n := by
    rw [hdecomp] at hsp_ge
    exact Nat.le_trans hprod hsp_ge
  have hnat_strict : centralBinom n + (C * B ^ n + D) < spernerFD n := by
    omega
  have hint_FD : ((C * B ^ n + D : Nat) : Int) < spernerCorrectionFD n := by
    unfold spernerCorrectionFD
    omega
  refine ⟨n, hn_n0, by omega, hint_FD, ?_⟩
  rw [spernerCorrectionFD0_eq_spernerCorrectionFD (by omega)]
  exact hint_FD

/-- **Refutation of Logarithmic Order (`O(log n)`, Part 2 of Conjecture 00000008532):**
    There exist NO threshold `n₀` and constants `C, D` such that
    `Δ(n) ≤ C * log₂(n) + D` for all `n ≥ n₀` (in either `FD(n)` or `FD_0(n)`). -/
theorem not_logarithmic_order_FD :
    ¬ ∃ (n₀ C D : Nat), ∀ n : Nat, n₀ ≤ n →
      spernerCorrectionFD n ≤ ((C * Nat.log2 n + D : Nat) : Int) := by
  rintro ⟨n₀, C, D, hbound⟩
  obtain ⟨n, hn₀, _, hgt, _⟩ := correction_exceeds_any_exponential n₀ C D 2
  have hle := hbound n hn₀
  have hlog_le : Nat.log2 n ≤ 2 ^ n :=
    Nat.le_trans (nat_log2_le_self n) (Nat.le_of_lt (lt_two_pow_self n))
  have hmul : C * Nat.log2 n ≤ C * 2 ^ n := Nat.mul_le_mul_left C hlog_le
  omega

theorem not_logarithmic_order_FD0 :
    ¬ ∃ (n₀ C D : Nat), ∀ n : Nat, n₀ ≤ n →
      spernerCorrectionFD0 n ≤ ((C * Nat.log2 n + D : Nat) : Int) := by
  rintro ⟨n₀, C, D, hbound⟩
  obtain ⟨n, hn₀, _, _, hgt⟩ := correction_exceeds_any_exponential n₀ C D 2
  have hle := hbound n hn₀
  have hlog_le : Nat.log2 n ≤ 2 ^ n :=
    Nat.le_trans (nat_log2_le_self n) (Nat.le_of_lt (lt_two_pow_self n))
  have hmul : C * Nat.log2 n ≤ C * 2 ^ n := Nat.mul_le_mul_left C hlog_le
  omega

/-- **Refutation of Polynomial Order (`O(n^d)`):** -/
theorem not_polynomial_order_FD :
    ¬ ∃ (n₀ C D d : Nat), ∀ n : Nat, n₀ ≤ n →
      spernerCorrectionFD n ≤ ((C * n ^ d + D : Nat) : Int) := by
  rintro ⟨n₀, C, D, d, hbound⟩
  obtain ⟨n, hn₀, _, hgt, _⟩ := correction_exceeds_any_exponential n₀ C D (2 ^ d)
  have hle := hbound n hn₀
  have hpow : C * n ^ d ≤ C * (2 ^ d) ^ n := Nat.mul_le_mul_left C (pow_le_exp_base n d)
  omega

/-- **Refutation of Singly-Exponential Order (`O(B^n)`):** -/
theorem not_exponential_order_FD :
    ¬ ∃ (n₀ C D B : Nat), ∀ n : Nat, n₀ ≤ n →
      spernerCorrectionFD n ≤ ((C * B ^ n + D : Nat) : Int) := by
  rintro ⟨n₀, C, D, B, hbound⟩
  obtain ⟨n, hn₀, _, hgt, _⟩ := correction_exceeds_any_exponential n₀ C D B
  have hle := hbound n hn₀
  omega

/-! ## 5. Combined Master Refutation of Conjecture 00000008532 -/

/-- Formal statement of Conjecture 00000008532 for `FD(n)`:
    (1) Always-positive central correction for `n ≥ 1`, AND
    (2) Asymptotic logarithmic upper bound `Δ(n) = O(log n)`. -/
def Conjecture00000008532_FD : Prop :=
  (∀ n : Nat, 1 ≤ n → 0 < spernerCorrectionFD n) ∧
  (∃ (n₀ C D : Nat), ∀ n : Nat, n₀ ≤ n →
    spernerCorrectionFD n ≤ ((C * Nat.log2 n + D : Nat) : Int))

/-- Formal statement of Conjecture 00000008532 for `FD_0(n)`: -/
def Conjecture00000008532_FD0 : Prop :=
  (∀ n : Nat, 1 ≤ n → 0 < spernerCorrectionFD0 n) ∧
  (∃ (n₀ C D : Nat), ∀ n : Nat, n₀ ≤ n →
    spernerCorrectionFD0 n ≤ ((C * Nat.log2 n + D : Nat) : Int))

/-- **Main Theorem (`FD(n)`):** Conjecture 00000008532 is false; in fact *both* halves fail. -/
theorem conjecture_00000008532_false_FD : ¬ Conjecture00000008532_FD :=
  fun h => not_logarithmic_order_FD h.2

/-- **Main Theorem (`FD_0(n)`):** Conjecture 00000008532 is false; in fact *both* halves fail. -/
theorem conjecture_00000008532_false_FD0 : ¬ Conjecture00000008532_FD0 :=
  fun h => not_logarithmic_order_FD0 h.2

end SpernerFD
