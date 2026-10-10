import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Sequence214

def diff (u : ℕ → ℝ) (n : ℕ) : ℝ := u (n + 1) - u n

lemma linear_upper (u : ℕ → ℝ) (a : ℝ)
    (h : ∀ n, diff u n ≤ a) (n : ℕ) : u n ≤ u 0 + (n : ℝ) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n
    dsimp [diff] at hn
    push_cast
    nlinarith

lemma nonneg_slope (u : ℕ → ℝ) (a : ℝ)
    (hu : ∀ n, 0 ≤ u n) (h : ∀ n, diff u n ≤ a) : 0 ≤ a := by
  by_contra ha
  have ha' : a < 0 := lt_of_not_ge ha
  obtain ⟨n, hn⟩ := exists_nat_gt (u 0 / (-a))
  have hm : u 0 < (n : ℝ) * (-a) :=
    (div_lt_iff₀ (neg_pos.mpr ha')).mp hn
  have hlin := linear_upper u a h n
  have hzero := hu n
  nlinarith

lemma diff_nonneg_of_antitone (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (diff u)) (n : ℕ) :
    0 ≤ diff u n := by
  apply nonneg_slope (fun k => u (n + k)) (diff u n)
  · intro k
    exact hu (n + k)
  · intro k
    have hk := hd (Nat.le_add_right n k)
    simpa only [diff, Nat.add_assoc] using hk

lemma second_nonneg (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (diff (diff u))) (n : ℕ) :
    0 ≤ diff (diff u) n := by
  by_contra hn
  have hn' : diff (diff u) n < 0 := lt_of_not_ge hn
  have htail : ∀ k, diff (diff u) (n + k) ≤ diff (diff u) n := by
    intro k
    exact hd (Nat.le_add_right n k)
  have hanti : Antitone (diff (fun k => u (n + k))) := by
    apply antitone_nat_of_succ_le
    intro k
    have hk : diff (diff u) (n + k) ≤ 0 := le_trans (htail k) hn'.le
    dsimp [diff] at hk ⊢
    simp only [Nat.add_assoc] at *
    linarith
  have hnonneg : ∀ k, 0 ≤ diff u (n + k) := by
    intro k
    have hk := diff_nonneg_of_antitone (fun k => u (n + k))
      (fun k => hu (n + k)) hanti k
    simpa only [diff, Nat.add_assoc] using hk
  have hbad : 0 ≤ diff (diff u) n := by
    apply nonneg_slope (fun k => diff u (n + k)) (diff (diff u) n) hnonneg
    intro k
    simpa only [diff, Nat.add_assoc] using htail k
  linarith

lemma linear_lower (u : ℕ → ℝ) (a : ℝ)
    (h : ∀ n, a ≤ diff u n) (n : ℕ) : u 0 + (n : ℝ) * a ≤ u n := by
  have hh : ∀ n, diff (fun k => -u k) n ≤ -a := by
    intro n
    have hn := h n
    dsimp [diff] at hn ⊢
    linarith
  have hn := linear_upper (fun k => -u k) (-a) hh n
  linarith

lemma bounded_prefix (u : ℕ → ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ n, n ≤ N → u n ≤ C := by
  induction N with
  | zero =>
    refine ⟨u 0, ?_⟩
    intro n hn
    have hn' : n = 0 := Nat.eq_zero_of_le_zero hn
    simp [hn']
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨max C (u (N + 1)), ?_⟩
    intro n hn
    rcases lt_or_eq_of_le hn with hlt | heq
    · exact le_trans (hC n (Nat.le_of_lt_succ hlt)) (le_max_left _ _)
    · subst n
      exact le_max_right _ _

/-- A nonnegative, unbounded sequence with no positive affine lower bound
cannot have nonpositive third differences throughout a tail. -/
theorem not_eventually_nonpos_third (f : ℕ → ℝ)
    (hzero : ∀ n, 0 ≤ f n)
    (hunbounded : ∀ C : ℝ, ∃ n, C < f n)
    (hno_affine_lower : ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      ∃ n : ℕ, f n < b + a * (n : ℝ)) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      f (n + 3) - 3 * f (n + 2) + 3 * f (n + 1) - f n ≤ 0 := by
  rintro ⟨N, hN⟩
  let u : ℕ → ℝ := fun k => f (N + k)
  have hu : ∀ k, 0 ≤ u k := fun k => hzero (N + k)
  have hanti2 : Antitone (diff (diff u)) := by
    apply antitone_nat_of_succ_le
    intro k
    have hk := hN (N + k) (Nat.le_add_right N k)
    dsimp [diff, u]
    simp only [Nat.add_assoc] at hk ⊢
    linarith
  have hmono1 : Monotone (diff u) := by
    apply monotone_nat_of_le_succ
    intro k
    have hk := second_nonneg u hu hanti2 k
    dsimp [diff] at hk ⊢
    linarith
  have hfirst : ∀ k, diff u k ≤ 0 := by
    intro k
    by_contra hk
    have hk' : 0 < diff u k := lt_of_not_ge hk
    let a := diff u k
    let M := N + k
    have ha : 0 < a := hk'
    have hsteps : ∀ j, a ≤ diff (fun t => f (M + t)) j := by
      intro j
      have hj := hmono1 (Nat.le_add_right k j)
      simpa only [a, M, u, diff, Nat.add_assoc] using hj
    have hlower : ∀ j : ℕ, (j : ℝ) * a ≤ f (M + j) := by
      intro j
      have hj := linear_lower (fun t => f (M + t)) a hsteps j
      have hz := hzero M
      simp only [Nat.add_zero] at hj
      linarith
    obtain ⟨n, hn⟩ := hno_affine_lower a ha (-a * (M : ℝ))
    by_cases hnm : n ≤ M
    · have hcast : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnm
      have hz := hzero n
      nlinarith
    · have hmn : M ≤ n := le_of_lt (Nat.lt_of_not_ge hnm)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have hj := hlower j
      push_cast at hn
      nlinarith
  have hanti : Antitone u := by
    apply antitone_nat_of_succ_le
    intro k
    have hk := hfirst k
    dsimp [diff] at hk
    linarith
  obtain ⟨C, hC⟩ := bounded_prefix f N
  have hbound : ∀ n, f n ≤ C := by
    intro n
    by_cases hn : n ≤ N
    · exact hC n hn
    · have hNn : N ≤ n := le_of_lt (Nat.lt_of_not_ge hn)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNn
      have hk := hanti (Nat.zero_le k)
      have hbase := hC N le_rfl
      dsimp [u] at hk
      simp only [Nat.add_zero] at hk
      linarith
  obtain ⟨n, hn⟩ := hunbounded C
  linarith [hbound n]

theorem not_eventually_negative_third (f : ℕ → ℝ)
    (hzero : ∀ n, 0 ≤ f n)
    (hunbounded : ∀ C : ℝ, ∃ n, C < f n)
    (hno_affine_lower : ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      ∃ n : ℕ, f n < b + a * (n : ℝ)) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      f (n + 3) - 3 * f (n + 2) + 3 * f (n + 1) - f n < 0 := by
  intro h
  apply not_eventually_nonpos_third f hzero hunbounded hno_affine_lower
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).le⟩

lemma no_affine_lower_of_sublinear (f : ℕ → ℝ)
    (hsub : ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ n, f n ≤ C + c * (n : ℝ)) :
    ∀ a : ℝ, 0 < a → ∀ b : ℝ, ∃ n : ℕ, f n < b + a * (n : ℝ) := by
  intro a ha b
  have hc : 0 < a / 2 := by positivity
  obtain ⟨C, hC⟩ := hsub (a / 2) hc
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - b) / (a / 2))
  have hm : C - b < (n : ℝ) * (a / 2) := (div_lt_iff₀ hc).mp hn
  refine ⟨n, ?_⟩
  have hh := hC n
  nlinarith

theorem not_eventually_negative_third_of_sublinear (f : ℕ → ℝ)
    (hzero : ∀ n, 0 ≤ f n)
    (hunbounded : ∀ C : ℝ, ∃ n, C < f n)
    (hsub : ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ n, f n ≤ C + c * (n : ℝ)) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      f (n + 3) - 3 * f (n + 2) + 3 * f (n + 1) - f n < 0 :=
  not_eventually_negative_third f hzero hunbounded (no_affine_lower_of_sublinear f hsub)

end Sequence214
