/-
  Conjecture 00000000546 — Maximal-Ideal Filtration and Tangent Cone `gr_m(K[[S_{a,k}]])`
  Core Lean 4.19.0
-/
import Conjecture00000000546.Semigroup

namespace Conjecture00000000546

/-! ## 1. Exact `m`-Adic Filtration and Order Formula `ν_m(s) = s / a` -/

/-- `t^s ∈ m^r` in `K[S_{a,k}]`: `s` is a sum of at least `r` generators in `[a, a+k]`. -/
def InMaxIdealPower (a k r s : Nat) : Prop :=
  ∃ j, r ≤ j ∧ InGenSumset a k j s

theorem inMaxIdealPower_imp_semigroup {a k r s : Nat} (h : InMaxIdealPower a k r s) :
    InIntervalSemigroup a k s := by
  rcases h with ⟨j, _, hj⟩
  exact (inIntervalSemigroup_iff_exists_sumset a k s).mpr ⟨j, hj⟩

/-- **Exact `m`-Adic Order Formula**:
    For every element `s ∈ S_{a,k}` (`a ≥ 1`), `t^s ∈ m^r` if and only if `r ≤ s / a`.
    Consequently, every `s ∈ S_{a,k}` has exact `m`-adic valuation `ν_m(s) = ⌊s / a⌋`. -/
theorem inMaxIdealPower_iff_le_div {a k r s : Nat} (ha : 1 ≤ a)
    (hs : InIntervalSemigroup a k s) :
    InMaxIdealPower a k r s ↔ r ≤ s / a := by
  constructor
  · rintro ⟨j, hrj, hj⟩
    rcases (inGenSumset_iff_interval a k j s).mp hj with ⟨hlow, _⟩
    have hdiv := Nat.div_add_mod s a
    have hmod : s % a < a := Nat.mod_lt s (by omega)
    have hja : r * a ≤ s := by
      have : r * a ≤ j * a := Nat.mul_le_mul_right a hrj
      omega
    by_cases hle : r ≤ s / a
    · exact hle
    · have h1 : s / a + 1 ≤ r := by omega
      have hmul : a * (s / a + 1) ≤ a * r := Nat.mul_le_mul_left a h1
      have hc1 : a * (s / a + 1) = a * (s / a) + a := Nat.mul_succ a (s / a)
      have hc2 : a * r = r * a := Nat.mul_comm a r
      omega
  · intro hr
    rcases (inIntervalSemigroup_iff_exists_interval a k s).mp hs with ⟨m, hm_low, hm_high⟩
    have hdiv := Nat.div_add_mod s a
    have hmod : s % a < a := Nat.mod_lt s (by omega)
    have hmj : m ≤ s / a := by
      by_cases hle : m ≤ s / a
      · exact hle
      · have h1 : s / a + 1 ≤ m := by omega
        have hmul : a * (s / a + 1) ≤ a * m := Nat.mul_le_mul_left a h1
        have hc1 : a * (s / a + 1) = a * (s / a) + a := Nat.mul_succ a (s / a)
        have hc2 : a * m = m * a := Nat.mul_comm a m
        omega
    refine ⟨s / a, hr, (inGenSumset_iff_interval a k (s / a) s).mpr ⟨?_, ?_⟩⟩
    · have hc : (s / a) * a = a * (s / a) := Nat.mul_comm _ a
      omega
    · by_cases hmeq : m = s / a
      · subst hmeq
        exact hm_high
      · have hm1 : m + 1 ≤ s / a := by omega
        have hja : (m + 1) * a ≤ (s / a) * a := Nat.mul_le_mul_right a hm1
        have hc : (s / a) * a = a * (s / a) := Nat.mul_comm _ a
        have hexp_m : m * (a + k) = m * a + m * k := Nat.mul_add m a k
        have hexp_m1 : (m + 1) * a = m * a + a := Nat.succ_mul m a
        have ha_le_mk : a ≤ m * k := by omega
        have hmk_jk : (m + 1) * k ≤ (s / a) * k := Nat.mul_le_mul_right k hm1
        have hexp_mk : (m + 1) * k = m * k + k := Nat.succ_mul m k
        have hexp_j : (s / a) * (a + k) = a * (s / a) + (s / a) * k := by
          rw [Nat.mul_add, Nat.mul_comm (s / a) a]
        omega

/-! ## 2. Constant Cohen–Macaulayness (Depth 1) of `gr_m(K[[S_{a,k}]])` -/

/-- Exact `m`-adic order shifts additively by `+1` under `+a` for EVERY `s ∈ S_{a,k}`,
    so `t^a + m^2` is a nonzerodivisor on `gr_m(K[[S_{a,k}]])` (Sally's criterion). -/
theorem tangentCone_exactOrder_shift {a k r s : Nat} (ha : 1 ≤ a)
    (hs : InIntervalSemigroup a k s) :
    (InMaxIdealPower a k r s ∧ ¬ InMaxIdealPower a k (r + 1) s) ↔
      (InMaxIdealPower a k (r + 1) (s + a) ∧ ¬ InMaxIdealPower a k (r + 2) (s + a)) := by
  have hsa : InIntervalSemigroup a k (s + a) :=
    InIntervalSemigroup.add_gen hs (Nat.le_refl a) (by omega)
  rw [inMaxIdealPower_iff_le_div ha hs, inMaxIdealPower_iff_le_div ha hs,
      inMaxIdealPower_iff_le_div ha hsa, inMaxIdealPower_iff_le_div ha hsa]
  have hdiv : (s + a) / a = s / a + 1 := Nat.add_div_right s (by omega)
  rw [hdiv]
  omega

/-- Full-polynomial version on `gr_m(K[S_{a,k}])_r = m^r / m^{r+1}`:
    For any field `K` and any polynomial `p` supported on `m^r` that is nonzero modulo `m^{r+1}`,
    `t^a * p` is supported on `m^{r+1}` and remains nonzero modulo `m^{r+2}`. -/
theorem tangentCone_ta_nonzerodivisor_poly {K : Type} [FieldCoeff K]
    {a k r : Nat} (ha : 1 ≤ a) (p : Poly1 K)
    (hp_supp : ∀ s, coeff1 p s ≠ FieldCoeff.zero → InMaxIdealPower a k r s)
    (hp_nz : ∃ s, coeff1 p s ≠ FieldCoeff.zero ∧ ¬ InMaxIdealPower a k (r + 1) s) :
    (∀ s', coeff1 (polyMul (monomial1 FieldCoeff.one a) p) s' ≠ FieldCoeff.zero →
      InMaxIdealPower a k (r + 1) s') ∧
    (∃ s', coeff1 (polyMul (monomial1 FieldCoeff.one a) p) s' ≠ FieldCoeff.zero ∧
      ¬ InMaxIdealPower a k (r + 2) s') := by
  constructor
  · intro s' hs'
    by_cases hlt : s' < a
    · rw [coeff1_mul_monomial1_lt a p hlt] at hs'
      exact False.elim (hs' rfl)
    · have hsplit : s' = a + (s' - a) := by omega
      rw [hsplit, coeff1_mul_monomial1_add a p (s' - a)] at hs'
      rcases hp_supp (s' - a) hs' with ⟨j, hrj, hj⟩
      refine ⟨j + 1, by omega, ?_⟩
      have hcomm : s' = (s' - a) + a := by omega
      rw [hcomm]
      exact InGenSumset.step hj (Nat.le_refl a) (by omega)
  · rcases hp_nz with ⟨s, hcs, hnot⟩
    refine ⟨a + s, ?_, ?_⟩
    · rwa [coeff1_mul_monomial1_add a p s]
    · have hs_mem : InIntervalSemigroup a k s := inMaxIdealPower_imp_semigroup (hp_supp s hcs)
      have hr_mem : InMaxIdealPower a k r s := hp_supp s hcs
      have hshift := (tangentCone_exactOrder_shift ha hs_mem).mp ⟨hr_mem, hnot⟩
      have hcomm : a + s = s + a := Nat.add_comm a s
      rw [hcomm]
      exact hshift.2

/-! ## 3. Two Exact Thresholds Inside `gr_m(K[[S_{a,k}]])`: `⌈(a-1)/k⌉` vs `⌈a/k⌉` -/

/-- **Reduction Number & Hilbert Stabilization Threshold (`⌈(a-1)/k⌉`)**:
    `m^{r+1} = t^a · m^r` holds if and only if `r ≥ ⌈(a-1)/k⌉`. -/
theorem reductionNumber_threshold_iff {a k r : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (∀ s, InMaxIdealPower a k (r + 1) s ↔ (a ≤ s ∧ InMaxIdealPower a k r (s - a))) ↔
      ceilDiv (a - 1) k ≤ r := by
  constructor
  · intro hred
    rw [le_ceilDiv_iff (by omega)]
    by_cases hle : a - 1 ≤ r * k
    · exact hle
    · have hs_in : InMaxIdealPower a k (r + 1) ((r + 1) * a + r * k + 1) := by
        refine ⟨r + 1, Nat.le_refl _,
                (inGenSumset_iff_interval a k (r + 1) _).mpr ⟨by omega, ?_⟩⟩
        have hexp : (r + 1) * (a + k) = (r + 1) * a + r * k + k := by
          rw [Nat.mul_add, Nat.succ_mul r k, ← Nat.add_assoc]
        omega
      have hsa_in : InMaxIdealPower a k r (((r + 1) * a + r * k + 1) - a) :=
        ((hred ((r + 1) * a + r * k + 1)).mp hs_in).2
      have hsa_mem : InIntervalSemigroup a k (((r + 1) * a + r * k + 1) - a) :=
        inMaxIdealPower_imp_semigroup hsa_in
      rw [inIntervalSemigroup_iff_exists_interval] at hsa_mem
      rcases hsa_mem with ⟨j, hj_low, hj_high⟩
      have hsa_val : ((r + 1) * a + r * k + 1) - a = r * a + r * k + 1 := by
        have : (r + 1) * a = r * a + a := Nat.succ_mul r a
        omega
      by_cases hjr : j ≤ r
      · have hmul : j * (a + k) ≤ r * (a + k) := Nat.mul_le_mul_right (a + k) hjr
        have hexp : r * (a + k) = r * a + r * k := Nat.mul_add r a k
        omega
      · have hj1 : r + 1 ≤ j := by omega
        have hmul : (r + 1) * a ≤ j * a := Nat.mul_le_mul_right a hj1
        have hexp : (r + 1) * a = r * a + a := Nat.succ_mul r a
        omega
  · intro hr_ge s
    constructor
    · intro hs
      have hs_mem : InIntervalSemigroup a k s := inMaxIdealPower_imp_semigroup hs
      have hr1_le : r + 1 ≤ s / a := (inMaxIdealPower_iff_le_div (by omega) hs_mem).mp hs
      have hdiv := Nat.div_add_mod s a
      have hsa_ge : r * a ≤ s - a := by
        have hmul : a * (r + 1) ≤ a * (s / a) := Nat.mul_le_mul_left a hr1_le
        have hc1 : a * (r + 1) = r * a + a := by rw [Nat.mul_succ, Nat.mul_comm]
        omega
      have ha_le_s : a ≤ s := by
        have : 1 * a ≤ r * a := Nat.mul_le_mul_right a hr
        omega
      have hcond_le : ceilDiv (a - 1) k * a ≤ s - a := by
        have : ceilDiv (a - 1) k * a ≤ r * a := Nat.mul_le_mul_right a hr_ge
        omega
      have hsa_mem : InIntervalSemigroup a k (s - a) := mem_of_ge_conductor ha hk hcond_le
      refine ⟨ha_le_s, (inMaxIdealPower_iff_le_div (by omega) hsa_mem).mpr ?_⟩
      have hdiv2 : s / a = (s - a + a) / a := by
        have : s - a + a = s := by omega
        rw [this]
      rw [Nat.add_div_right _ (by omega)] at hdiv2
      omega
    · rintro ⟨ha_le_s, j, hrj, hj⟩
      refine ⟨j + 1, by omega, ?_⟩
      have hsplit : s = (s - a) + a := by omega
      rw [hsplit]
      exact InGenSumset.step hj (Nat.le_refl a) (by omega)

/-- **Sumset-Overlap & Top-Generator Nilpotency Threshold (`⌈a/k⌉`)**:
    `r G_{a,k} ∩ (r+1) G_{a,k} ≠ ∅` (equivalently, `(t^{a+k})^r ∈ m^{r+1}`, i.e.
    `(t^{a+k} + m^2)^r = 0` in `gr_m(K[[S_{a,k}]])`) holds if and only if `r ≥ ⌈a/k⌉`. -/
theorem sumset_overlap_iff_ceilDiv {a k r : Nat} (ha : 1 ≤ a) (hk : 1 ≤ k) :
    (∃ s, InGenSumset a k r s ∧ InGenSumset a k (r + 1) s) ↔ ceilDiv a k ≤ r := by
  rw [le_ceilDiv_iff hk]
  constructor
  · rintro ⟨s, h1, h2⟩
    rcases (inGenSumset_iff_interval a k r s).mp h1 with ⟨_, h1_up⟩
    rcases (inGenSumset_iff_interval a k (r + 1) s).mp h2 with ⟨h2_low, _⟩
    have hexp1 : r * (a + k) = r * a + r * k := Nat.mul_add r a k
    have hexp2 : (r + 1) * a = r * a + a := Nat.succ_mul r a
    omega
  · intro hrk
    refine ⟨r * (a + k), (inGenSumset_iff_interval a k r _).mpr ⟨?_, Nat.le_refl _⟩,
            (inGenSumset_iff_interval a k (r + 1) _).mpr ⟨?_, ?_⟩⟩
    · exact Nat.mul_le_mul_left r (by omega)
    · have hexp1 : r * (a + k) = r * a + r * k := Nat.mul_add r a k
      have hexp2 : (r + 1) * a = r * a + a := Nat.succ_mul r a
      omega
    · have hexp : (r + 1) * (a + k) = r * (a + k) + (a + k) := Nat.succ_mul r (a + k)
      omega

theorem topGenerator_nilpotent_in_gr_iff {a k r : Nat} (ha : 1 ≤ a) (hk : 1 ≤ k) :
    InMaxIdealPower a k (r + 1) (r * (a + k)) ↔ ceilDiv a k ≤ r := by
  have hmem : InIntervalSemigroup a k (r * (a + k)) :=
    (inIntervalSemigroup_iff_exists_interval a k _).mpr
      ⟨r, Nat.mul_le_mul_left r (by omega), Nat.le_refl _⟩
  rw [inMaxIdealPower_iff_le_div ha hmem, le_ceilDiv_iff hk]
  have hexp : r * (a + k) = r * k + a * r := by
    rw [Nat.mul_add, Nat.mul_comm r a, Nat.add_comm]
  rw [hexp, Nat.add_mul_div_left _ _ (by omega)]
  constructor
  · intro h
    have hkdiv : 1 ≤ r * k / a := by
      rw [Nat.add_comm (r * k / a) r] at h
      exact Nat.le_of_add_le_add_left h
    have hdiv := Nat.div_add_mod (r * k) a
    have hmul : a * 1 ≤ a * (r * k / a) := Nat.mul_le_mul_left a hkdiv
    omega
  · intro h
    have h1 := Nat.div_add_mod (r * k) a
    have hmod : (r * k) % a < a := Nat.mod_lt _ (by omega)
    cases hdiv_eq : r * k / a with
    | zero =>
      rw [hdiv_eq] at h1
      omega
    | succ d =>
      rw [Nat.add_comm r 1]
      exact Nat.add_le_add_right (Nat.zero_lt_succ d) r

end Conjecture00000000546
