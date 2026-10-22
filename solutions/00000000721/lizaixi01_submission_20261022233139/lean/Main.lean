import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace TLMC721
open Filter Topology
abbrev K := PadicAlgCl 2

noncomputable def term (a : ℕ → Fin 2) (n : ℕ) : K :=
  (a n).val * (2 : K) ^ (-(((n + 1).factorial : ℕ) : ℤ))

/-- Source indices n>=1 are represented by n+1 in a zero-based sequence. -/
theorem term_matches_source (a : ℕ → Fin 2) (n : ℕ) :
    term (fun m => a (m + 1)) n =
      (a (n + 1)).val * (2 : K) ^ (-(((n + 1).factorial : ℕ) : ℤ)) := rfl

theorem positive_reindex_surjective :
    Function.Surjective (fun a : ℕ → Fin 2 => fun n => a (n + 1)) := by
  intro a
  refine ⟨fun n => if n = 0 then 0 else a (n - 1), ?_⟩
  funext n
  simp

theorem norm_two : ‖(2 : K)‖ = (2 : ℝ)⁻¹ := by
  calc
    ‖(2 : K)‖ = ‖(2 : ℚ_[2])‖ := by
      convert PadicAlgCl.norm_extends 2 (2 : ℚ_[2]) using 1; norm_cast
    _ = (2 : ℝ)⁻¹ := Padic.norm_p

theorem norm_term_of_nonzero (a : ℕ → Fin 2) (n : ℕ) (hn : a n ≠ 0) :
    1 ≤ ‖term a n‖ := by
  have hv : (a n).val = 1 := by
    have hlt := (a n).isLt
    have hz : (a n).val ≠ 0 := fun h => hn (Fin.ext h)
    omega
  simp only [term, hv, Nat.cast_one, one_mul]
  rw [norm_zpow, norm_two]
  simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv]
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem vanishing_eventually_zero (a : ℕ → Fin 2)
    (h : Tendsto (term a) atTop (nhds 0)) :
    ∀ᶠ n in atTop, a n = 0 := by
  have ht := h.norm
  have he : ∀ᶠ n in atTop, ‖term a n‖ < 1 :=
    (tendsto_order.mp ht).2 1 (by norm_num)
  filter_upwards [he] with n hn
  by_contra hne
  exact (not_lt_of_ge (norm_term_of_nonzero a n hne)) hn

theorem summable_eventually_zero (a : ℕ → Fin 2) (h : Summable (term a)) :
    ∀ᶠ n in atTop, a n = 0 :=
  vanishing_eventually_zero a h.tendsto_atTop_zero

noncomputable def seriesValues : Set K :=
  {x | ∃ a : ℕ → Fin 2, HasSum (term a) x}

/-- The source starts at n=1; use successor reindexing rather than a zeroth term. -/
noncomputable def sourceSeriesValues : Set K :=
  {x | ∃ a : ℕ → Fin 2, HasSum (term (fun n => a (n + 1))) x}

theorem sourceSeriesValues_eq : sourceSeriesValues = seriesValues := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun n => a (n + 1), ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := positive_reindex_surjective a
    refine ⟨b, ?_⟩
    change (fun n => b (n + 1)) = a at hb
    rw [hb]
    exact ha

theorem series_value_rational {x : K} (hx : x ∈ seriesValues) :
    ∃ q : ℚ, (q : K) = x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (summable_eventually_zero a ha.summable))
  let q : ℚ := ∑ n ∈ Finset.range N,
    (a n).val * (2 : ℚ) ^ (-(((n + 1).factorial : ℕ) : ℤ))
  refine ⟨q, ?_⟩
  have hs : HasSum (term a) (∑ n ∈ Finset.range N, term a n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    simp [term, hN n hnN]
  have he := ha.unique hs
  rw [he]
  simp [q, term]

theorem seriesValues_countable : seriesValues.Countable := by
  apply (Set.countable_range (fun q : ℚ => (q : K))).mono
  intro x hx
  exact series_value_rational hx

theorem no_uncountable_subfamily :
    ¬ ∃ S : Set K, S ⊆ sourceSeriesValues ∧ ¬ S.Countable := by
  rintro ⟨S, hS, huncountable⟩
  rw [sourceSeriesValues_eq] at hS
  exact huncountable (seriesValues_countable.mono hS)

def SequentialSum (a : ℕ → Fin 2) (x : K) : Prop :=
  Tendsto (fun N => ∑ n ∈ Finset.range N, term a n) atTop (nhds x)

theorem sequential_hasSum (a : ℕ → Fin 2) (x : K) (h : SequentialSum a x) :
    HasSum (term a) x := by
  have h1 := h.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (term a) atTop (nhds 0) := by
    have hd := h1.sub h
    simpa [Finset.sum_range_succ] using hd
  obtain ⟨N, hN⟩ := eventually_atTop.1 (vanishing_eventually_zero a ht)
  have hs : HasSum (term a) (∑ n ∈ Finset.range N, term a n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    simp [term, hN n hnN]
  have he := tendsto_nhds_unique h hs.tendsto_sum_nat
  simpa [he] using hs

noncomputable def sourceSequentialValues : Set K :=
  {x | ∃ a : ℕ → Fin 2, SequentialSum (fun n => a (n + 1)) x}

theorem sourceSequentialValues_eq : sourceSequentialValues = sourceSeriesValues := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, sequential_hasSum _ _ ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.tendsto_sum_nat⟩

theorem no_uncountable_sequential_subfamily :
    ¬ ∃ S : Set K, S ⊆ sourceSequentialValues ∧ ¬ S.Countable := by
  rw [sourceSequentialValues_eq]
  exact no_uncountable_subfamily

theorem no_continuum_subfamily :
    ¬ ∃ S : Set K, S ⊆ sourceSequentialValues ∧
      Cardinal.mk S = 2 ^ Cardinal.aleph0 := by
  rintro ⟨S, hS, hcard⟩
  have hs : S.Countable := by
    apply seriesValues_countable.mono
    simpa [sourceSequentialValues_eq, sourceSeriesValues_eq] using hS
  let : Countable S := hs.to_subtype
  have hle := Cardinal.mk_le_aleph0 (α := S)
  rw [hcard, Cardinal.two_power_aleph0] at hle
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hle

end TLMC721
