import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.WellFoundedSet
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# The numerical incompatibility in Conjecture 00000007914

Every set of nonnegative real numbers is covered: nothing concerning arithmetic
Fuchsian groups, the choice of a limit spectrum, or triangle groups is assumed.
The rank is zero-based, so rank `n` means the source's `(n + 1)`-st element.
-/

open Filter Asymptotics
open scoped Topology

namespace CovolumeSpectrum

/-- Exactly the comparison function written in the source.  The values at
`k = 0` and `k = 1` are harmless totalizations: only the tail `k ≥ 2` matters. -/
noncomputable def scale (c : ℝ) (k : ℕ) : ℝ :=
  c * (k : ℝ)⁻¹ * (Real.log (k : ℝ)) ^ (-(2 / 3 : ℝ))

/-- Every finite real leading constant gives a comparison function tending to zero. -/
theorem scale_tendsto_zero (c : ℝ) : Tendsto (scale c) atTop (𝓝 0) := by
  have hindex : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv := hindex.inv_tendsto_atTop
  have hlog := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (Real.tendsto_log_atTop.comp hindex)
  simpa [scale] using (tendsto_const_nhds.mul hinv).mul hlog

/-- For a nonzero leading constant, the standard quotient definition of
asymptotic equivalence agrees with the Mathlib definition used below. -/
theorem asymptotic_iff_ratio {v : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0) :
    v ~[atTop] scale c ↔ Tendsto (fun k => v k / scale c k) atTop (𝓝 1) := by
  apply isEquivalent_iff_tendsto_one
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hkreal : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkreal
  exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hkreal))))
    (ne_of_gt (Real.rpow_pos_of_pos hlog _))

/-- The exact finite-rank meaning of 'the k-th element': `x` is in `S`
and exactly `n` distinct elements of `S` are strictly smaller than `x`. -/
def HasRank (S : Set ℝ) (n : ℕ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∃ below : Finset ℝ,
    (∀ y : ℝ, y ∈ below ↔ y ∈ S ∧ y < x) ∧ below.card = n

/-- Finite ranks determine a strictly increasing sequence. -/
theorem rank_strictMono {S : Set ℝ} {v : ℕ → ℝ}
    (hv : ∀ n, HasRank S n (v n)) : StrictMono v := by
  intro m n hmn
  by_contra hnot
  have hvnm : v n ≤ v m := le_of_not_gt hnot
  obtain ⟨_, bm, hbm, hcm⟩ := hv m
  obtain ⟨_, bn, hbn, hcn⟩ := hv n
  have hsub : bn ⊆ bm := by
    intro y hy
    obtain ⟨hyS, hylt⟩ := (hbn y).mp hy
    exact (hbm y).mpr ⟨hyS, lt_of_lt_of_le hylt hvnm⟩
  have hc := Finset.card_le_card hsub
  rw [hcm, hcn] at hc
  omega

/-- The exact finite-index assertions from the source.  Its first element has
rank zero; no claim is made that these finite ranks exhaust a transfinite order. -/
def RankedAsymptotic (S : Set ℝ) : Prop :=
  ∃ (v : ℕ → ℝ) (c : ℝ),
    (∀ k, 1 ≤ k → HasRank S (k - 1) (v k)) ∧ v ~[atTop] scale c

/-- The rank assertions and asymptotic cannot both hold in any nonnegative set.
This includes sets containing zero and all real leading constants. -/
theorem no_rankedAsymptotic {S : Set ℝ} (hS : S ⊆ Set.Ici 0) :
    ¬ RankedAsymptotic S := by
  rintro ⟨v, c, hv, hasym⟩
  have hrank : ∀ n, HasRank S n (v (n + 1)) := by
    intro n
    simpa using hv (n + 1) (by omega)
  have hmono := rank_strictMono hrank
  have hv1 : 0 ≤ v 1 := hS (hv 1 (by omega)).1
  have hv2 : 0 < v 2 := lt_of_le_of_lt hv1 (hmono (by omega : 0 < 1))
  have htend : Tendsto v atTop (𝓝 0) :=
    hasym.symm.tendsto_nhds (scale_tendsto_zero c)
  have htail : ∀ᶠ k in atTop, v 2 ≤ v k := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      hmono.monotone (by omega : 1 ≤ k - 1)
  have hle : v 2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htend htail
  exact (not_lt_of_ge hle) hv2

/-- Closedness of the nonnegative half-line proves nonnegativity for every
set selected from the closure of a nonnegative set of raw covolumes. -/
theorem limit_spectrum_nonnegative {C S : Set ℝ}
    (hC : C ⊆ Set.Ici 0) (hS : S ⊆ closure C) : S ⊆ Set.Ici 0 :=
  hS.trans (closure_minimal hC isClosed_Ici)

/-- Explicitly, a real limit of eventually nonnegative values is nonnegative.
It is not asserted to be strictly positive. -/
theorem limit_nonnegative {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → ℝ} {x : ℝ} (hf : ∀ᶠ i in l, 0 ≤ f i)
    (hx : Tendsto f l (𝓝 x)) : 0 ≤ x :=
  le_of_tendsto_of_tendsto tendsto_const_nhds hx hf

/-- The Chinese phrase can also mean a limit inferior.  A finite real value
of the extended-real liminf of eventually nonnegative numbers is nonnegative.
Using extended reals avoids any hidden boundedness hypothesis. -/
theorem finite_liminf_nonnegative {ι : Type*} {l : Filter ι}
    {f : ι → ℝ} {x : ℝ} (hf : ∀ᶠ i in l, 0 ≤ f i)
    (hx : Filter.liminf (fun i => (f i : EReal)) l = (x : EReal)) : 0 ≤ x := by
  have h : (0 : EReal) ≤ Filter.liminf (fun i => (f i : EReal)) l :=
    le_liminf_of_le (by isBoundedDefault) (hf.mono fun _ hi => EReal.coe_nonneg.mpr hi)
  rw [hx] at h
  exact EReal.coe_nonneg.mp h

/-- The well-ordering and enumeration/asymptotic clauses of the source.
All arithmetic and triangle-group clauses can only further restrict this. -/
def NumericalConjecture (S : Set ℝ) : Prop :=
  S.IsWF ∧ RankedAsymptotic S

/-- The necessary source clauses are impossible for every nonnegative set. -/
theorem no_numericalConjecture {S : Set ℝ} (hS : S ⊆ Set.Ici 0) :
    ¬ NumericalConjecture S := by
  rintro ⟨_, h⟩
  exact no_rankedAsymptotic hS h

/-- A universal disproof including any additional clauses of the original
conjunction, for any spectrum selected from limits of nonnegative covolumes. -/
theorem no_full_conjunction {C S : Set ℝ}
    (hC : C ⊆ Set.Ici 0) (hS : S ⊆ closure C) (rest : Prop) :
    ¬ (NumericalConjecture S ∧ rest) := by
  rintro ⟨h, _⟩
  exact no_numericalConjecture (limit_spectrum_nonnegative hC hS) h

/-- Finite total volumes of an arbitrary family of measured spaces.
A family of measured hyperbolic quotients is a special case. -/
def finiteMeasureValues {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, MeasureTheory.Measure (X i)) : Set ℝ :=
  {x | ∃ i, μ i Set.univ ≠ ⊤ ∧ x = (μ i Set.univ).toReal}

/-- Nonnegativity is supplied by the measure-valued definition of volume,
with no positivity or finiteness theorem for arithmetic groups assumed. -/
theorem finiteMeasureValues_nonnegative {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, MeasureTheory.Measure (X i)) :
    finiteMeasureValues μ ⊆ Set.Ici 0 := by
  rintro x ⟨i, _, rfl⟩
  exact ENNReal.toReal_nonneg

/-- The conjunction is false for every limit spectrum of finite volumes of
an arbitrary family of measured spaces, including measured group quotients. -/
theorem no_measure_spectrum_conjunction {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, MeasureTheory.Measure (X i))
    {S : Set ℝ} (hS : S ⊆ closure (finiteMeasureValues μ)) (rest : Prop) :
    ¬ (NumericalConjecture S ∧ rest) :=
  no_full_conjunction (finiteMeasureValues_nonnegative μ) hS rest

/-- The same source conjunction is impossible if 'limit-from-below spectrum'
is interpreted as a selection of finite sequential limit inferiors. -/
theorem no_liminf_spectrum_conjunction {C S : Set ℝ}
    (hC : C ⊆ Set.Ici 0)
    (hS : ∀ x ∈ S, ∃ f : ℕ → ℝ,
      (∀ n, f n ∈ C) ∧ Filter.liminf (fun n => (f n : EReal)) atTop = (x : EReal))
    (rest : Prop) : ¬ (NumericalConjecture S ∧ rest) := by
  have hnonneg : S ⊆ Set.Ici 0 := by
    intro x hx
    obtain ⟨f, hf, hlim⟩ := hS x hx
    exact finite_liminf_nonnegative (Filter.Eventually.of_forall fun n => hC (hf n)) hlim
  rintro ⟨h, _⟩
  exact no_numericalConjecture hnonneg h

end CovolumeSpectrum
