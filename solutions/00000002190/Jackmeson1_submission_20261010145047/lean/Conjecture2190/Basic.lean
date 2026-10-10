import Mathlib
import Conjecture2190.Statement

/-! # Conjecture 2190: "The Sperner capacity of C_{2k+1} equals cos(pi/(2k+1))"

Disproof.  The cycle C_{2k+1} lives on `Fin (2k+1)`.  Sperner capacity is read for every
orientation of the cycle, in exponential units, in bits and in nats; the undirected
(Shannon confusability) capacity is also covered.  In every case the claim fails already
at `k = 1`.  Natural-log units are refuted only through `k = 1` (Sperner reading). -/

-- (formal statement: see Statement.lean)

namespace C2190
open Filter Topology

/-- One arc `a -> b` gives `2^n <= (n+1) * M_n`. -/
theorem arc_bound {α : Type} [Fintype α] [DecidableEq α] (E : α → α → Prop) {a b : α}
    (hab : E a b) (hne : a ≠ b) (n : ℕ) :
    2 ^ n ≤ (n + 1) * maxCode (SpernerCode (n := n) E) := by
  classical
  let w : Finset (Fin n) → (Fin n → α) := fun T i => if i ∈ T then b else a
  have hw : Function.Injective w := by
    intro T T' h
    ext i
    have := congrFun h i
    simp only [w] at this
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ T' <;> simp_all
  set S := (Finset.powersetCard (n / 2) (Finset.univ : Finset (Fin n))).image w with hS
  have hcard : S.card = n.choose (n / 2) := by
    rw [hS, Finset.card_image_of_injective _ hw, Finset.card_powersetCard]; simp
  have hcode : SpernerCode (n := n) E S := by
    intro x hx y hy hxy
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_powersetCard] at hT hT'
    have hTT : T ≠ T' := fun h => hxy (by rw [h])
    have : ¬ T' ⊆ T := fun hs =>
      hTT (Finset.eq_of_subset_of_card_le hs (by rw [hT.2, hT'.2])).symm
    obtain ⟨j, hj1, hj2⟩ := Finset.not_subset.1 this
    exact ⟨j, by simpa [w, hj1, hj2] using hab⟩
  have hle : S.card ≤ maxCode (SpernerCode (n := n) E) := by
    unfold maxCode
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcode⟩)
  have hsum : 2 ^ n = ∑ i ∈ Finset.range (n + 1), n.choose i := (Nat.sum_range_choose n).symm
  have hmid : ∑ i ∈ Finset.range (n + 1), n.choose i ≤ (n + 1) * n.choose (n / 2) := by
    have := Finset.sum_le_card_nsmul (Finset.range (n + 1)) (fun i => n.choose i)
      (n.choose (n / 2)) (fun i _ => Nat.choose_le_middle i n)
    simpa using this
  calc 2 ^ n ≤ (n + 1) * n.choose (n / 2) := hsum ▸ hmid
    _ ≤ (n + 1) * maxCode (SpernerCode (n := n) E) := by
        apply Nat.mul_le_mul_left; rw [← hcard]; exact hle

/-- Explicit lower sequence tending to `2`. -/
theorem g_tendsto :
    Tendsto (fun n : ℕ => 2 / ((2 : ℝ) ^ ((1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n)))
      atTop (𝓝 2) := by
  have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).rpow tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl two_ne_zero)
    simpa using this
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have := (tendsto_const_nhds (x := (2 : ℝ))).div (h1.mul h2) (by norm_num)
  rw [show (2 : ℝ) / (1 * 1) = 2 by norm_num] at this
  exact this

theorem g_le {α : Type} [Fintype α] [DecidableEq α] (E : α → α → Prop) {a b : α}
    (hab : E a b) (hne : a ≠ b) (n : ℕ) (hn : 1 ≤ n) :
    2 / ((2 : ℝ) ^ ((1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n)) ≤
      (maxCode (SpernerCode (n := n) E) : ℝ) ^ ((1 : ℝ) / n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * maxCode (SpernerCode (n := n) E) := by
    exact_mod_cast arc_bound E hab hne n
  set M : ℝ := ((maxCode (SpernerCode (n := n) E) : ℕ) : ℝ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n) := by positivity
  rw [div_le_iff₀ hden]
  have h2n : (2 : ℝ) ≤ M ^ ((1 : ℝ) / n) * ((2 : ℝ) ^ ((1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n)) := by
    rw [← Real.mul_rpow (by norm_num) hnr.le, ← Real.mul_rpow hM0 (by positivity)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : ((2 : ℝ) ^ n) ≤ M * (2 * n) := by nlinarith [mul_nonneg hM0 (sub_nonneg.2 hn1)]
    calc (2 : ℝ) = ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) := by
          rw [one_div, Real.pow_rpow_inv_natCast (by norm_num) (by omega)]
      _ ≤ (M * (2 * n)) ^ ((1 : ℝ) / n) :=
          Real.rpow_le_rpow (by positivity) this (by positivity)
  linarith

/-- Any unit `u` that is monotone on positives and continuous at `2` forces `c ≥ u 2`
when one arc is present. -/
theorem reading_ge {α : Type} [Fintype α] [DecidableEq α] (E : α → α → Prop) {a b : α}
    (hab : E a b) (hne : a ≠ b) (u : ℝ → ℝ) (hm : MonotoneOn u (Set.Ioi 0))
    (hc : ContinuousAt u 2) (c : ℝ)
    (h : Reading u (fun n => maxCode (SpernerCode (n := n) E)) c) : u 2 ≤ c := by
  have hg := hc.tendsto.comp g_tendsto
  refine le_of_tendsto_of_tendsto hg h ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  exact hm (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; have := g_le E hab hne n hn
        have : (0:ℝ) < 2 / ((2 : ℝ) ^ ((1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n)) := by positivity
        linarith [g_le E hab hne n hn]) (g_le E hab hne n hn)

theorem cos_k1 : Real.cos (Real.pi / (2 * ((1 : ℕ) : ℝ) + 1)) = 1 / 2 := by
  norm_num [Real.cos_pi_div_three]

theorem sperner_refuted (u : ℝ → ℝ) (hm : MonotoneOn u (Set.Ioi 0)) (hc : ContinuousAt u 2)
    (hu : 1 / 2 < u 2) : ¬ ConjSperner u := by
  intro hconj
  obtain ⟨E, ⟨-, hx⟩, h⟩ := hconj 1 le_rfl
  have hne : nxt 1 (0 : Fin (2 * 1 + 1)) ≠ 0 := by decide
  rw [cos_k1] at h
  rcases hx 0 with ⟨h1, -⟩ | ⟨h2, -⟩
  · have := reading_ge E h1 hne.symm u hm hc _ h; linarith
  · have := reading_ge E h2 hne u hm hc _ h; linarith

theorem shannon_M (n : ℕ) : maxCode (ShannonCode 1 (n := n)) = 1 := by
  have hadj : ∀ a b : Fin (2 * 1 + 1), a ≠ b → Adj 1 a b := by
    unfold Adj nxt; decide
  classical
  unfold maxCode
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    have hS' := (Finset.mem_filter.1 hS).2
    apply Finset.card_le_one.2
    intro x hx y hy
    by_contra hxy
    obtain ⟨i, h1, h2⟩ := hS' x hx y hy hxy
    exact h2 (hadj _ _ h1)
  · have hmem : ({fun _ => (0 : Fin (2 * 1 + 1))} : Finset (Fin n → Fin (2 * 1 + 1))) ∈
        (Finset.univ : Finset (Finset (Fin n → Fin (2 * 1 + 1)))).filter
          (ShannonCode 1 (n := n)) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      intro x hx y hy hxy
      exact absurd ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm) hxy
    simpa using Finset.le_sup (f := Finset.card) hmem

theorem shannon_refuted (u : ℝ → ℝ) (hu : u 1 ≠ 1 / 2) : ¬ ConjShannon u := by
  intro hconj
  have h := hconj 1 le_rfl
  rw [cos_k1] at h
  have h2 : Tendsto (fun n : ℕ => u (((maxCode (ShannonCode 1 (n := n)) : ℕ) : ℝ) ^ ((1 : ℝ) / n)))
      atTop (𝓝 (u 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n _
    rw [shannon_M n]; simp
  exact hu (tendsto_nhds_unique h2 h)

theorem logb_mono : MonotoneOn (Real.logb 2) (Set.Ioi 0) := fun x hx y _ hxy =>
  Real.logb_le_logb_of_le (by norm_num) hx hxy

theorem main : Claim := by
  have hid : MonotoneOn (id : ℝ → ℝ) (Set.Ioi 0) := fun x _ y _ h => h
  have hlog : MonotoneOn Real.log (Set.Ioi 0) := fun x hx y _ hxy => Real.log_le_log hx hxy
  have cl : ContinuousAt (Real.logb 2) 2 := by
    unfold Real.logb; exact (Real.continuousAt_log two_ne_zero).div_const _
  have l2 := Real.log_two_gt_d9
  refine ⟨⟨sperner_refuted id hid continuousAt_id (by norm_num),
    sperner_refuted _ logb_mono cl (by rw [Real.logb_self_eq_one (by norm_num)]; norm_num),
    sperner_refuted _ hlog (Real.continuousAt_log two_ne_zero) (by linarith)⟩,
    shannon_refuted id (by norm_num),
    shannon_refuted _ (by norm_num), shannon_refuted _ (by norm_num)⟩

end C2190
