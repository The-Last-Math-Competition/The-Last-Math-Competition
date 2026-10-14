import Conjecture1421.Walk
import Conjecture1421.Powers
import Conjecture1421.Spectrum
import Conjecture1421.MixingBase

/-!
# Failure of the explicit multiplicity/gap sufficient condition

All conclusions refer to the defined exactly-half-lazy uniform Cayley walk on
`ZMod 2 × ZMod (n+4)`, its matrix powers, its actual characters, and its true
least-threshold total-variation mixing times. The unquantified phrases
"conditional spectral gap", "second-order behavior", and the unnamed comparison
characterization in the source are not assigned invented meanings here.
-/
noncomputable section
open Filter Polynomial
open scoped BigOperators Topology
namespace Conjecture1421

theorem minTransitionRatio_tendsto :
    Tendsto (fun n => (minTransitionMultiplicity n : ℝ) / spectralGap n) atTop atTop := by
  simp_rw [minTransitionRatio_eq]
  apply tendsto_atTop_mono (fun n => ?_) size_tendsto
  have hn := size_ge_four n
  nlinarith

theorem gapModeRatio_tendsto :
    Tendsto (fun n => (gapModeMultiplicity n : ℝ) / spectralGap n) atTop atTop := by
  simpa only [gapModeRatio_eq] using size_tendsto

/-- A complete certificate, with no remaining hypotheses, for the actual family. -/
structure CounterexampleCertificate : Prop where
  group_cardinality : ∀ n, Fintype.card (State n) = 2 * (n + 4)
  group_orders_diverge : Tendsto (fun n => (Fintype.card (State n) : ℝ)) atTop atTop
  support_cardinality : ∀ n, (support n).card = n + 4
  support_excludes_zero : ∀ n, (0 : State n) ∉ support n
  support_is_symmetric : ∀ n (g : State n), -g ∈ support n ↔ g ∈ support n
  support_generates_group : ∀ n, AddSubgroup.closure (support n : Set (State n)) = ⊤
  uniform_cayley_kernel : ∀ n (x y : State n), transition n x y =
    (if x = y then (1 / 2 : ℝ) else 0) +
      if y - x ∈ support n then 1 / (2 * ((support n).card : ℝ)) else 0
  exact_half_holding : ∀ n (x : State n), transition n x x = 1 / 2
  stochastic_kernel : ∀ n, transition n ∈ doublyStochastic ℝ (State n)
  all_power_kernels_stochastic : ∀ n t, transition n ^ t ∈ doublyStochastic ℝ (State n)
  uniform_law_mass_one : ∀ n, (∑ _x : State n, (1 / (2 * size n) : ℝ)) = 1
  uniform_law_nonnegative : ∀ n, (0 : ℝ) ≤ 1 / (2 * size n)
  reversible_kernel : ∀ n (x y : State n), transition n x y = transition n y x
  uniform_law_stationary : ∀ n (y : State n),
    ∑ x, (1 / (2 * size n)) * transition n x y = 1 / (2 * size n)
  positive_two_step_kernel : ∀ n (x y : State n), 0 < (transition n ^ 2) x y
  complete_character_basis : ∀ n, ∃ b : Basis (Characters n) ℂ (State n → ℂ),
    ∀ ψ, b ψ = (ψ : State n → ℂ)
  genuine_character_action : ∀ n (ψ : Characters n),
    (complexTransition n).mulVec ψ = fourierEigenvalue n ψ • (ψ : State n → ℂ)
  character_eigenvalues_real : ∀ n (ψ : Characters n), (fourierEigenvalue n ψ).im = 0
  character_eigenvalues_positive : ∀ n (ψ : Characters n), 0 < (fourierEigenvalue n ψ).re
  unique_stationary_character : ∀ n (ψ : Characters n), fourierEigenvalue n ψ = 1 ↔ ψ = 0
  actual_characteristic_polynomial : ∀ n, (complexTransition n).charpoly =
    (X - C (1 : ℂ)) * (X - C (q n : ℂ)) *
      (X - C (r : ℂ)) ^ (n + 3) * (X - C (s n : ℂ)) ^ (n + 3)
  actual_transition_roots : ∀ n (z : ℂ), IsRoot (complexTransition n).charpoly z ↔
    z = 1 ∨ z = (q n : ℂ) ∨ z = (r : ℂ) ∨ z = (s n : ℂ)
  genuine_complement_action : ∀ n (ψ : Characters n),
    (complexComplement n).mulVec ψ = (1 - fourierEigenvalue n ψ) • (ψ : State n → ℂ)
  actual_complement_polynomial : ∀ n, (complexComplement n).charpoly =
    (X - C (0 : ℂ)) * (X - C (1 - (q n : ℂ))) *
      (X - C (1 - (r : ℂ))) ^ (n + 3) * (X - C (1 - (s n : ℂ))) ^ (n + 3)
  eigenvalues_strictly_ordered : ∀ n, 0 < s n ∧ s n < r ∧ r < q n ∧ q n < 1
  maximum_nontrivial_eigenvalue : ∀ n, maxNontrivialEigenvalue n = q n
  minimum_nontrivial_eigenvalue : ∀ n, minTransitionEigenvalue n = s n
  ordinary_spectral_gap : ∀ n, spectralGap n = 1 / size n
  ordinary_spectral_gap_positive : ∀ n, 0 < spectralGap n
  minimum_positive_complement_eigenvalue : ∀ n,
    minPositiveComplementEigenvalue n = spectralGap n
  complement_spectrum_nonnegative : ∀ n (z : ℂ),
    IsRoot (complexComplement n).charpoly z → z.im = 0 ∧ 0 ≤ z.re
  gap_le_every_positive_complement_root : ∀ n (z : ℂ),
    IsRoot (complexComplement n).charpoly z → 0 < z.re → spectralGap n ≤ z.re
  literal_minimum_multiplicity : ∀ n, minTransitionMultiplicity n = n + 3
  gap_mode_multiplicity : ∀ n, gapModeMultiplicity n = 1
  actual_transition_powers : ∀ n t (x y : State n),
    (transition n ^ t) x y =
      (1 + (if x.1 = y.1 then 1 else -1) * q n ^ t +
        (size n * (if x.2 = y.2 then 1 else 0) - 1) *
          (r ^ t + (if x.1 = y.1 then 1 else -1) * s n ^ t)) / (2 * size n)
  actual_total_variation : ∀ n t (x : State n), tvFrom n t x =
    if t = 0 then 1 - 1 / (2 * size n) else q n ^ t / 2
  actual_worst_start_distance : ∀ n t, worstTV n t =
    if t = 0 then 1 - 1 / (2 * size n) else q n ^ t / 2
  finite_threshold_times : ∀ n ε, 0 < ε → {t : ℕ | worstTV n t ≤ ε}.Nonempty
  mixing_time_attains_threshold : ∀ n ε, 0 < ε → worstTV n (mixingTime n ε) ≤ ε
  mixing_time_is_least : ∀ n t ε, t < mixingTime n ε → ε < worstTV n t
  high_tolerance_time : ∀ n, mixingTime n (3 / 4) = 1
  ordinary_mixing_time_lower_bound : ∀ n, size n / 2 ≤ totalTime n
  ordinary_mixing_times_diverge : Tendsto totalTime atTop atTop
  positive_actual_window : ∀ n, 0 < window n
  bounded_actual_window_ratio : ∀ n, windowRatio n ≤ 2
  actual_window_ratio_limit : Tendsto windowRatio atTop (𝓝 1)
  no_time_window_separation : ¬ Tendsto windowRatio atTop atTop
  literal_spectral_ratio_diverges :
    Tendsto (fun n => (minTransitionMultiplicity n : ℝ) / spectralGap n) atTop atTop
  gap_mode_spectral_ratio_diverges :
    Tendsto (fun n => (gapModeMultiplicity n : ℝ) / spectralGap n) atTop atTop
  no_quantified_tv_cutoff : ¬ HasTVCutoff

/-- The actual Cayley family violates the sufficient direction in both eigenvalue readings. -/
theorem verified_counterexample : CounterexampleCertificate where
  group_cardinality := state_card
  group_orders_diverge := group_order_tendsto
  support_cardinality := support_card
  support_excludes_zero := zero_not_mem_support
  support_is_symmetric := support_symmetric
  support_generates_group := support_generates
  uniform_cayley_kernel := transition_uniform
  exact_half_holding := transition_diagonal
  stochastic_kernel := transition_doublyStochastic
  all_power_kernels_stochastic := transition_pow_doublyStochastic
  uniform_law_mass_one := uniform_mass_one
  uniform_law_nonnegative := uniform_nonneg
  reversible_kernel := transition_symmetric
  uniform_law_stationary := uniform_stationary
  positive_two_step_kernel := transition_sq_pos
  complete_character_basis n := ⟨AddChar.complexBasis (State n), AddChar.complexBasis_apply⟩
  genuine_character_action := character_action
  character_eigenvalues_real := fourierEigenvalue_im_eq_zero
  character_eigenvalues_positive := fourierEigenvalue_positive
  unique_stationary_character := fourierEigenvalue_eq_one_iff
  actual_characteristic_polynomial := complexTransition_charpoly
  actual_transition_roots := charpoly_isRoot_iff
  genuine_complement_action := complement_character_action
  actual_complement_polynomial := complexComplement_charpoly
  eigenvalues_strictly_ordered := eigenvalues_ordered
  maximum_nontrivial_eigenvalue := maxNontrivialEigenvalue_eq_q
  minimum_nontrivial_eigenvalue := minTransitionEigenvalue_eq_s
  ordinary_spectral_gap := spectralGap_eq
  ordinary_spectral_gap_positive := spectralGap_pos
  minimum_positive_complement_eigenvalue := minPositiveComplementEigenvalue_eq_gap
  complement_spectrum_nonnegative := complement_roots_nonnegative
  gap_le_every_positive_complement_root := spectralGap_le_positive_complement_root
  literal_minimum_multiplicity := minTransitionMultiplicity_eq
  gap_mode_multiplicity := gapModeMultiplicity_eq_one
  actual_transition_powers := transition_pow_apply
  actual_total_variation := tvFrom_eq
  actual_worst_start_distance := worstTV_eq
  finite_threshold_times := threshold_nonempty worstTV_eq
  mixing_time_attains_threshold := mixingTime_attained worstTV_eq
  mixing_time_is_least := mixingTime_minimal
  high_tolerance_time := mixingTime_three_quarters worstTV_eq
  ordinary_mixing_time_lower_bound := quarter_time_lower_bound worstTV_eq
  ordinary_mixing_times_diverge := totalTime_tendsto worstTV_eq
  positive_actual_window := window_pos worstTV_eq
  bounded_actual_window_ratio := windowRatio_le_two worstTV_eq
  actual_window_ratio_limit := windowRatio_tendsto_one worstTV_eq
  no_time_window_separation := windowRatio_not_tendsto_atTop worstTV_eq
  literal_spectral_ratio_diverges := minTransitionRatio_tendsto
  gap_mode_spectral_ratio_diverges := gapModeRatio_tendsto
  no_quantified_tv_cutoff := not_hasTVCutoff worstTV_eq

theorem literal_sufficient_criterion_false :
    ¬ ((Tendsto (fun n => (minTransitionMultiplicity n : ℝ) / spectralGap n) atTop atTop)
      → HasTVCutoff) := by
  intro h
  exact verified_counterexample.no_quantified_tv_cutoff
    (h verified_counterexample.literal_spectral_ratio_diverges)

theorem gap_mode_sufficient_criterion_false :
    ¬ ((Tendsto (fun n => (gapModeMultiplicity n : ℝ) / spectralGap n) atTop atTop)
      → HasTVCutoff) := by
  intro h
  exact verified_counterexample.no_quantified_tv_cutoff
    (h verified_counterexample.gap_mode_spectral_ratio_diverges)

theorem literal_window_sufficient_criterion_false :
    ¬ ((Tendsto (fun n => (minTransitionMultiplicity n : ℝ) / spectralGap n) atTop atTop)
      → Tendsto windowRatio atTop atTop) := by
  intro h
  exact verified_counterexample.no_time_window_separation
    (h verified_counterexample.literal_spectral_ratio_diverges)

theorem gap_mode_window_sufficient_criterion_false :
    ¬ ((Tendsto (fun n => (gapModeMultiplicity n : ℝ) / spectralGap n) atTop atTop)
      → Tendsto windowRatio atTop atTop) := by
  intro h
  exact verified_counterexample.no_time_window_separation
    (h verified_counterexample.gap_mode_spectral_ratio_diverges)

end Conjecture1421
