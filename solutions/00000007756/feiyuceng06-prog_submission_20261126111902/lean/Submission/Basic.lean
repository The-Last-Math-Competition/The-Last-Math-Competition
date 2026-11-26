import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Order.Field

namespace Submission00000007756

open Filter Function
open scoped Topology

/-- The successor map of the functional digraph modulo `p`. -/
def quadraticMap (p : ℕ) (x : ZMod p) : ZMod p := x ^ 2 + 1

/-- Every vertex reaches a cycle within one step, and some vertex is off the cycles. -/
def MaxTailOne (p : ℕ) : Prop :=
  (∀ x, quadraticMap p x ∈ periodicPts (quadraticMap p)) ∧
    ∃ x, x ∉ periodicPts (quadraticMap p)

private theorem quadraticMap_neg (p : ℕ) (x : ZMod p) :
    quadraticMap p (-x) = quadraticMap p x := by
  simp [quadraticMap]

private theorem natCast_ne_zero_of_pos_of_lt {a p : ℕ} (ha : 0 < a) (hp : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  exact (Nat.not_le_of_gt hp) (Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff _ _).mp h))

/-- More than half of the field consists of images of the residues from 0 through p / 2. -/
private theorem exists_antipodes_in_range {p : ℕ} (hp : p.Prime) (hp₂ : 2 < p) :
    ∃ z, z ∈ Set.range (quadraticMap p) ∧ -z ∈ Set.range (quadraticMap p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpOdd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  let g (a : Fin (p / 2 + 1)) := quadraticMap p (a.val : ZMod p)
  have hg : Injective g := by
    intro a b hab
    have ha : a.val < p := by have := a.isLt; omega
    have hb : b.val < p := by have := b.isLt; omega
    have hsquares : (a.val : ZMod p) ^ 2 = (b.val : ZMod p) ^ 2 := by
      exact add_right_cancel hab
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
    · apply Fin.ext
      simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb]
        using congrArg ZMod.val h
    · have hsum : (↑(a.val + b.val) : ZMod p) = 0 := by
        rw [Nat.cast_add, h, neg_add_cancel]
      have hlt : a.val + b.val < p := by
        have := a.isLt
        have := b.isLt
        omega
      have hzero : a.val + b.val = 0 := by
        simpa only [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] using congrArg ZMod.val hsum
      exact Fin.ext (by omega)
  let images : Finset (ZMod p) := Finset.univ.image g
  have hcard : images.card = p / 2 + 1 := by
    simp [images, Finset.card_image_of_injective _ hg]
  have hnegCard : (images.image (fun z => -z)).card = images.card :=
    Finset.card_image_of_injective _ neg_injective
  have hnotDisjoint : ¬ Disjoint images (images.image fun z => -z) := by
    intro hdisjoint
    have hle := Finset.card_le_univ (images ∪ images.image fun z => -z)
    rw [Finset.card_union_of_disjoint hdisjoint, hnegCard, hcard, ZMod.card] at hle
    omega
  obtain ⟨z, hz, hzneg⟩ := Finset.not_disjoint_iff.mp hnotDisjoint
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hz
  obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzneg
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hw
  refine ⟨z, ⟨a.val, ha⟩, b.val, ?_⟩
  change g b = -z
  rw [hb, ← hwz, neg_neg]

/-- In every prime field of size greater than five, some successor is still off-cycle. -/
theorem exists_successor_off_cycle {p : ℕ} (hp : p.Prime) (hp₅ : 5 < p) :
    ∃ x, quadraticMap p x ∉ periodicPts (quadraticMap p) := by
  classical
  by_contra! hall
  have : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_pos_of_lt (a := 2) (by decide) (by omega)
  have hfive : (5 : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_pos_of_lt (a := 5) (by decide) hp₅
  have antipodes_zero {z : ZMod p} (hz : z ∈ Set.range (quadraticMap p))
      (hnz : -z ∈ Set.range (quadraticMap p)) : z = 0 := by
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hnz
    have h := (bijOn_periodicPts (quadraticMap p)).injOn
      (hall a) (hb ▸ hall b) (quadraticMap_neg p (quadraticMap p a)).symm
    have heq : 2 * quadraticMap p a = 0 := by linear_combination h
    exact (mul_eq_zero.mp heq).resolve_left htwo
  obtain ⟨z, hz, hnz⟩ := exists_antipodes_in_range hp (by omega)
  have hz₀ := antipodes_zero hz hnz
  obtain ⟨i, hi⟩ : (0 : ZMod p) ∈ Set.range (quadraticMap p) := hz₀ ▸ hz
  have hiSq : i ^ 2 = -1 := by
    have h : i ^ 2 + 1 = 0 := hi
    linear_combination h
  let x : ZMod p := 1 / 2
  let y : ZMod p := 3 * i / 2
  have hpair : quadraticMap p y = -(quadraticMap p x) := by
    dsimp [quadraticMap, x, y]
    field_simp
    linear_combination 9 * hiSq
  have hzero := antipodes_zero (Set.mem_range_self x) ⟨y, hpair⟩
  have h : (1 / 2 : ZMod p) ^ 2 + 1 = 0 := hzero
  field_simp at h
  apply hfive
  linear_combination h

theorem not_maxTailOne_of_five_lt {p : ℕ} (hp : p.Prime) (hp₅ : 5 < p) :
    ¬ MaxTailOne p := by
  obtain ⟨x, hx⟩ := exists_successor_off_cycle hp hp₅
  exact fun h => hx (h.1 x)

/-- Some vertex is off-cycle but its successor is on a cycle. -/
def ContainsTailOne (p : ℕ) : Prop :=
  ∃ x, x ∉ periodicPts (quadraticMap p) ∧ quadraticMap p x ∈ periodicPts (quadraticMap p)

private theorem exists_periodic_iterate {α : Type*} [Finite α] (f : α → α) (x : α) :
    ∃ n, f^[n] x ∈ periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] x = f^[n] x ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  wlog hlt : m < n generalizing m n
  · exact this n m heq.symm hne.symm (by omega)
  refine ⟨m, mk_mem_periodicPts (n := n - m) (by omega) ?_⟩
  change f^[n - m] (f^[m] x) = f^[m] x
  rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le, heq]

theorem containsTailOne_of_two_lt {p : ℕ} (hp₂ : 2 < p) : ContainsTailOne p := by
  classical
  have : NeZero p := ⟨by omega⟩
  obtain ⟨x, hx⟩ : ∃ x, x ∉ periodicPts (quadraticMap p) := by
    by_contra! hall
    have heq := (bijOn_periodicPts (quadraticMap p)).injOn
      (hall (-1)) (hall 1) (quadraticMap_neg p 1)
    have htwo : (2 : ZMod p) = 0 := by linear_combination -heq
    exact natCast_ne_zero_of_pos_of_lt (a := 2) (by decide) hp₂ htwo
  obtain ⟨n, hn⟩ := exists_periodic_iterate (quadraticMap p) x
  induction n with
  | zero => exact (hx hn).elim
  | succ n ih =>
    by_cases h : (quadraticMap p)^[n] x ∈ periodicPts (quadraticMap p)
    · exact ih h
    · exact ⟨(quadraticMap p)^[n] x, h, by rwa [iterate_succ_apply'] at hn⟩

private theorem mem_periodicPts_iff_fixed_within_card (p : ℕ) [NeZero p] (x : ZMod p) :
    x ∈ periodicPts (quadraticMap p) ↔
      ∃ k : Fin p, (quadraticMap p)^[k.val + 1] x = x := by
  constructor
  · intro h
    let n := minimalPeriod (quadraticMap p) x
    have hpos : 0 < n := minimalPeriod_pos_of_mem_periodicPts h
    have hle : n ≤ p := by
      simpa only [ZMod.card] using
        (minimalPeriod_le_card (f := quadraticMap p) (x := x))
    refine ⟨⟨n - 1, by omega⟩, ?_⟩
    change (quadraticMap p)^[n - 1 + 1] x = x
    rw [show n - 1 + 1 = n by omega]
    exact isPeriodicPt_minimalPeriod _ _
  · rintro ⟨k, hk⟩
    exact mk_mem_periodicPts (Nat.succ_pos _) hk

private theorem maxTailOne_iff_fixed_within_card (p : ℕ) [NeZero p] :
    MaxTailOne p ↔
      (∀ x, ∃ k : Fin p, (quadraticMap p)^[k.val + 1] (quadraticMap p x) =
        quadraticMap p x) ∧
      ∃ x, ¬ ∃ k : Fin p, (quadraticMap p)^[k.val + 1] x = x := by
  simp only [MaxTailOne, mem_periodicPts_iff_fixed_within_card]

theorem not_maxTailOne_two : ¬ MaxTailOne 2 := by
  rw [maxTailOne_iff_fixed_within_card]
  decide

theorem not_maxTailOne_three : ¬ MaxTailOne 3 := by
  rw [maxTailOne_iff_fixed_within_card]
  decide

theorem maxTailOne_five : MaxTailOne 5 := by
  rw [maxTailOne_iff_fixed_within_card]
  decide

/-- The only prime whose graph has maximum tail length one is five. -/
theorem maxTailOne_iff_eq_five {p : ℕ} (hp : p.Prime) :
    MaxTailOne p ↔ p = 5 := by
  refine ⟨fun h => ?_, fun h => h ▸ maxTailOne_five⟩
  have hle : p ≤ 5 := by
    by_contra! hlarge
    exact not_maxTailOne_of_five_lt hp hlarge h
  have h₂ := hp.two_le
  interval_cases p
  · exact (not_maxTailOne_two h).elim
  · exact (not_maxTailOne_three h).elim
  · exact ((by decide : ¬ Nat.Prime 4) hp).elim
  · rfl

/-- The primes up to `X` whose functional graph has maximum tail length one. -/
noncomputable def maxTailOnePrimes (X : ℕ) : Finset ℕ := by
  classical
  exact X.primesLE.filter MaxTailOne

/-- Relative frequency of a graph property among primes up to the cutoff. -/
noncomputable def primeGraphFrequency (property : ℕ → Prop) (X : ℕ) : ℝ := by
  classical
  exact (X.primesLE.filter property).card / (X.primeCounting : ℝ)

noncomputable def tailOneFrequency : ℕ → ℝ := primeGraphFrequency MaxTailOne

theorem maxTailOnePrimes_eq_singleton (X : ℕ) (hX : 5 ≤ X) :
    maxTailOnePrimes X = {5} := by
  ext p
  simp only [maxTailOnePrimes, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_singleton]
  exact ⟨fun h => (maxTailOne_iff_eq_five h.1.2).mp h.2,
    fun h => h ▸ ⟨⟨hX, by decide⟩, maxTailOne_five⟩⟩

theorem tailOneFrequency_eq_inv {X : ℕ} (hX : 5 ≤ X) :
    tailOneFrequency X = (X.primeCounting : ℝ)⁻¹ := by
  change ((maxTailOnePrimes X).card : ℝ) / (X.primeCounting : ℝ) = _
  simp [maxTailOnePrimes_eq_singleton X hX, one_div]

private theorem primeCounting_tendsto_atTop_real :
    Tendsto (fun X : ℕ => (X.primeCounting : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting

theorem tailOneFrequency_tendsto_zero : Tendsto tailOneFrequency atTop (𝓝 0) := by
  refine (tendsto_inv_atTop_zero.comp primeCounting_tendsto_atTop_real).congr' ?_
  filter_upwards [eventually_ge_atTop 5] with X hX
  exact (tailOneFrequency_eq_inv hX).symm

private theorem not_containsTailOne_two : ¬ ContainsTailOne 2 := by
  simp only [ContainsTailOne, mem_periodicPts_iff_fixed_within_card]
  decide

theorem containsTailOneFrequency_tendsto_one :
    Tendsto (primeGraphFrequency ContainsTailOne) atTop (𝓝 1) := by
  classical
  have h := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop) |>.sub
    (tendsto_inv_atTop_zero.comp primeCounting_tendsto_atTop_real)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hmem : 2 ∈ X.primesLE := Nat.mem_primesLE.mpr ⟨hX, Nat.prime_two⟩
  have hset : X.primesLE.filter ContainsTailOne = X.primesLE.erase 2 := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_filter]
    refine ⟨fun ⟨hp, ht⟩ => ⟨fun he => not_containsTailOne_two (he ▸ ht), hp⟩, ?_⟩
    rintro ⟨hne, hp⟩
    have hp₂ := (Nat.mem_primesLE.mp hp).2.two_le
    exact ⟨hp, containsTailOne_of_two_lt (lt_of_le_of_ne hp₂ hne.symm)⟩
  have hpos : 0 < X.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr ⟨2, hmem⟩
  have hπ : (X.primeCounting : ℝ) ≠ 0 := by positivity
  simp only [primeGraphFrequency, hset, Finset.card_erase_of_mem hmem,
    Nat.primesLE_card_eq_primeCounting, Nat.cast_sub (Nat.succ_le_of_lt hpos), Nat.cast_one]
  rw [sub_div, div_self hπ, one_div]
  rfl

/-- The first conjunct of the conjecture, with one functional graph per prime. -/
def TailFrequencyClaim : Prop :=
  Tendsto tailOneFrequency atTop (𝓝 (3 - 4 * Real.log 2))

theorem not_tailFrequencyClaim : ¬ TailFrequencyClaim := by
  intro h
  have heq := tendsto_nhds_unique tailOneFrequency_tendsto_zero h
  have hlog := Real.log_two_lt_d9
  linarith

theorem conjecture_00000007756_false (cycleLengthClause : Prop) :
    ¬ (TailFrequencyClaim ∧ cycleLengthClause) :=
  fun h => not_tailFrequencyClaim h.1

theorem not_containsTailFrequencyClaim :
    ¬ Tendsto (primeGraphFrequency ContainsTailOne) atTop (𝓝 (3 - 4 * Real.log 2)) := by
  intro h
  have heq := tendsto_nhds_unique containsTailOneFrequency_tendsto_one h
  have hlog := Real.log_two_gt_d9
  linarith

#print axioms exists_successor_off_cycle
#print axioms maxTailOne_iff_eq_five
#print axioms tailOneFrequency_tendsto_zero
#print axioms not_containsTailFrequencyClaim
#print axioms conjecture_00000007756_false

end Submission00000007756
