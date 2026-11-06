import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped Uniformity SetRel ENNReal NNReal

namespace TLMC8488

abbrev Stream := ℕ → Bool

instance streamMetric : MetricSpace Stream :=
  PiNat.metricSpaceOfDiscreteUniformity (E := fun _ => Bool) (fun _ => rfl)

def uniqueOne (x : Stream) : Prop :=
  ∀ i j, x i = true → x j = true → i = j

theorem uniqueOne_closed : IsClosed {x : Stream | uniqueOne x} := by
  change IsClosed {x : Stream | ∀ i j, x i = true → x j = true → i = j}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have heq : {x : Stream | x i = true → x j = true → i = j} =
        {x : Stream | x i = false} ∪ {x : Stream | x j = false} := by
      ext x
      cases hi : x i <;> cases hj : x j <;> simp [hi, hj, hij]
    rw [heq]
    exact (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply j) continuous_const)

abbrev X := {x : Stream // uniqueOne x}

instance compactX : CompactSpace X :=
  isCompact_iff_compactSpace.mp uniqueOne_closed.isCompact

def zero : X := ⟨fun _ => false, by simp [uniqueOne]⟩

instance nonemptyX : Nonempty X := ⟨zero⟩

def spike (k : ℕ) : X :=
  ⟨fun i => if i = k then true else false, by
    intro i j hi hj
    have hik : i = k := by
      by_contra h
      simp [h] at hi
    have hjk : j = k := by
      by_contra h
      simp [h] at hj
    exact hik.trans hjk.symm⟩

def shift (x : X) : X :=
  ⟨fun i => x.val (i + 1), by
    intro i j hi hj
    have h := x.property (i + 1) (j + 1) hi hj
    omega⟩

theorem shift_continuous : Continuous shift := by
  have hv : Continuous (fun x : X => x.val) := continuous_subtype_val
  exact (continuous_pi fun i => (continuous_apply (i + 1)).comp hv).subtype_mk _

theorem shift_iterate_apply (n : ℕ) (x : X) (i : ℕ) :
    ((shift^[n]) x).val i = x.val (i + n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp [Function.iterate_succ_apply, ih, shift, Nat.add_assoc]

def cylinderRel (m : ℕ) : SetRel X X :=
  {p | ∀ i < m, p.1.val i = p.2.val i}

instance prefix_refl (m : ℕ) : (cylinderRel m).IsRefl :=
  ⟨fun _ _ _ => rfl⟩

instance prefix_symm (m : ℕ) : (cylinderRel m).IsSymm :=
  ⟨fun _ _ h i hi => (h i hi).symm⟩

theorem prefix_comp (m : ℕ) : cylinderRel m ○ cylinderRel m = cylinderRel m := by
  ext p
  constructor
  · rintro ⟨z, hxz, hzy⟩ i hi
    exact (hxz i hi).trans (hzy i hi)
  · intro h
    exact ⟨p.1, fun _ _ => rfl, h⟩

theorem prefix_iff_dist (m : ℕ) (x y : X) :
    (x, y) ∈ cylinderRel m ↔ dist x y ≤ (1 / 2 : ℝ) ^ m := by
  exact PiNat.mem_cylinder_iff_dist_le (x := y.val) (y := x.val)

theorem prefix_uniformity (m : ℕ) : cylinderRel m ∈ 𝓤 X := by
  apply Metric.mem_uniformity_dist.mpr
  refine ⟨(1 / 2 : ℝ) ^ m, by positivity, ?_⟩
  intro x y hp
  exact (prefix_iff_dist m x y).mpr hp.le

theorem prefix_cofinal (U : SetRel X X) (hU : U ∈ 𝓤 X) :
    ∃ m, cylinderRel m ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨m, fun p hp => hsub ((prefix_iff_dist m p.1 p.2).mp hp |>.trans_lt hm)⟩

def representative {n : ℕ} : Option (Fin n) → X
  | none => zero
  | some k => spike k.val

theorem representative_prefix_injective {n : ℕ} {a b : Option (Fin n)}
    (h : (representative a, representative b) ∈ cylinderRel n) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hh := h b.val b.isLt
      simp [representative, zero, spike] at hh
  | some a =>
    cases b with
    | none =>
      have hh := h a.val a.isLt
      simp [representative, zero, spike] at hh
    | some b =>
      have hh := h a.val a.isLt
      by_cases hab : a.val = b.val
      · exact congrArg some (Fin.ext hab)
      · simp [representative, spike, hab] at hh

theorem representative_injective (n : ℕ) :
    Function.Injective (@representative n) := by
  intro a b hab
  apply representative_prefix_injective
  rw [hab]
  exact fun _ _ => rfl

def centers (n : ℕ) : Finset X :=
  by
    classical
    exact Finset.univ.image (@representative n)

theorem centers_card (n : ℕ) : (centers n).card = n + 1 := by
  classical
  rw [centers, Finset.card_image_of_injective _ (representative_injective n)]
  simp

theorem prefix_representative (n : ℕ) (x : X) :
    ∃ a : Option (Fin n), (x, representative a) ∈ cylinderRel n := by
  classical
  by_cases h : ∃ i : Fin n, x.val i = true
  · obtain ⟨i, hi⟩ := h
    refine ⟨some i, ?_⟩
    intro j hj
    by_cases hji : j = i.val
    · subst j
      simpa [representative, spike] using hi
    · have hxj : x.val j = false := by
        cases hx : x.val j with
        | false => rfl
        | true =>
          have hij := x.property i.val j hi hx
          exact False.elim (hji hij.symm)
      simp [representative, spike, hji, hxj]
  · refine ⟨none, ?_⟩
    intro j hj
    have hxj : x.val j = false := by
      cases hx : x.val j with
      | false => rfl
      | true => exact False.elim (h ⟨⟨j, hj⟩, hx⟩)
    simpa [representative, zero] using hxj

theorem dyn_prefix_one (n : ℕ) :
    Dynamics.dynEntourage shift (cylinderRel 1) n = cylinderRel n := by
  ext p
  rw [Dynamics.mem_dynEntourage]
  constructor
  · intro h i hi
    have hh := h i hi 0 (by omega)
    simpa [shift_iterate_apply] using hh
  · intro h k hk i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [shift_iterate_apply] using h k hk

theorem centers_cover_one (n : ℕ) :
    Dynamics.IsDynCoverOf shift Set.univ (cylinderRel 1) n (centers n) := by
  classical
  intro x _
  obtain ⟨a, ha⟩ := prefix_representative n x
  refine ⟨representative a, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · rw [dyn_prefix_one]
    exact ha

theorem centers_net_one (n : ℕ) :
    Dynamics.IsDynNetIn shift Set.univ (cylinderRel 1) n (centers n) := by
  classical
  refine ⟨Set.subset_univ _, ?_⟩
  intro x hx y hy hxy
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  change (x, z) ∈ Dynamics.dynEntourage shift (cylinderRel 1) n at hxz
  change (y, z) ∈ Dynamics.dynEntourage shift (cylinderRel 1) n at hyz
  rw [dyn_prefix_one] at hxz hyz
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  have hab : a = b := representative_prefix_injective
    (fun i hi => (hxz i hi).trans (hyz i hi).symm)
  exact hxy (congrArg representative hab)

theorem actual_coverMincard (n : ℕ) :
    Dynamics.coverMincard shift Set.univ (cylinderRel 1) n = (n + 1 : ℕ) := by
  apply le_antisymm
  · have h := (centers_cover_one n).coverMincard_le_card
    simpa [centers_card] using h
  · have h := (centers_net_one n).card_le_netMaxcard
    rw [centers_card] at h
    exact h.trans (Dynamics.netMaxcard_le_coverMincard shift Set.univ n)

theorem actual_coverMincard_finite (n : ℕ) :
    Dynamics.coverMincard shift Set.univ (cylinderRel 1) n < ⊤ := by
  rw [actual_coverMincard]
  exact ENat.natCast_lt_top (n + 1)

theorem centers_cover (m n : ℕ) :
    Dynamics.IsDynCoverOf shift Set.univ (cylinderRel m) n (centers (m + n)) := by
  classical
  intro x _
  obtain ⟨a, ha⟩ := prefix_representative (m + n) x
  refine ⟨representative a, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · rw [Dynamics.mem_dynEntourage]
    intro k hk i hi
    simp only [shift_iterate_apply]
    exact ha (i + k) (by omega)

theorem log_linear_tendsto (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + c + 1) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + c + 1) atTop atTop :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(c : ℝ)) 1 one_ne_zero).comp ht
  convert h using 1
  funext n
  simp only [Function.comp_apply, pow_one, one_mul]
  congr 1
  ring

theorem ennreal_log_nat (k : ℕ) (hk : 0 < k) :
    ENNReal.log (k : ℝ≥0∞) = (Real.log (k : ℝ) : EReal) := by
  have hc : ENNReal.ofReal (k : ℝ) = (k : ℝ≥0∞) := by simp
  rw [← hc, ENNReal.log_ofReal_of_pos (by exact_mod_cast hk)]

theorem prefix_entropy_zero (m : ℕ) :
    Dynamics.coverEntropyEntourage shift Set.univ (cylinderRel m) = 0 := by
  have hb (n : ℕ) : Dynamics.coverEntropyEntourage shift Set.univ (cylinderRel m) ≤
      ((Real.log ((n : ℝ) + (m + 1 : ℕ) + 1) / ((n : ℝ) + 1) : ℝ) : EReal) := by
    have h := (centers_cover m (n + 1)).coverEntropyEntourage_le_log_card_div
      (Set.mapsTo_univ _ _) (by omega : n + 1 ≠ 0)
    rw [prefix_comp, centers_card] at h
    convert h using 1
    rw [ennreal_log_nat (m + (n + 1) + 1) (by omega)]
    rw [← EReal.coe_coe_eq_natCast (n + 1), ← EReal.coe_div]
    congr 2 <;> push_cast <;> ring_nf
  apply le_antisymm
  · exact ge_of_tendsto (EReal.tendsto_coe.mpr (log_linear_tendsto (m + 1)))
      (Filter.Eventually.of_forall hb)
  · exact Dynamics.coverEntropyEntourage_nonneg shift Set.univ_nonempty (cylinderRel m)

theorem native_topological_entropy_zero :
    Dynamics.coverEntropy shift Set.univ = 0 := by
  apply le_antisymm
  · change (⨆ U ∈ 𝓤 X, Dynamics.coverEntropyEntourage shift Set.univ U) ≤ 0
    refine iSup₂_le fun U hU => ?_
    obtain ⟨m, hm⟩ := prefix_cofinal U hU
    calc
      Dynamics.coverEntropyEntourage shift Set.univ U ≤
          Dynamics.coverEntropyEntourage shift Set.univ (cylinderRel m) :=
        Dynamics.coverEntropyEntourage_antitone shift Set.univ hm
      _ = 0 := prefix_entropy_zero m
  · exact Dynamics.coverEntropy_nonneg shift Set.univ_nonempty

def finiteTimeValue (n : ℕ) : ℝ :=
  Real.log ((Dynamics.coverMincard shift Set.univ (cylinderRel 1) n).toNat : ℝ) / n

theorem finiteTimeValue_eq (n : ℕ) :
    finiteTimeValue n = Real.log ((n + 1 : ℕ) : ℝ) / n := by
  simp [finiteTimeValue, actual_coverMincard, ENat.toNat_add]

theorem finiteTimeValue_tendsto : Tendsto finiteTimeValue atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  convert h using 1
  funext n
  simp only [Function.comp_apply, pow_one, one_mul, finiteTimeValue_eq, Nat.cast_add,
    Nat.cast_one]
  congr 1
  ring

theorem no_harmonic_bound (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ C / n < |finiteTimeValue n - 0| := by
  have ht : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop C)
  let n := max M (max N 1)
  have hn : 1 ≤ n := le_trans (le_max_right N 1) (le_max_right M (max N 1))
  refine ⟨n, le_trans (le_max_left N 1) (le_max_right M (max N 1)), hn, ?_⟩
  rw [finiteTimeValue_eq, sub_zero, abs_of_nonneg
    (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))]
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hn0 : (0 : ℝ) < n)).mpr
  simpa using hM n (le_max_left M (max N 1))

theorem counterexample :
    IsCompact (Set.univ : Set X) ∧ Continuous shift ∧
    Dynamics.coverEntropy shift Set.univ = 0 ∧
    (∀ n, Dynamics.coverMincard shift Set.univ (cylinderRel 1) n = (n + 1 : ℕ)) ∧
    ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ 1 ≤ n ∧ C / n < |finiteTimeValue n - 0| := by
  exact ⟨isCompact_univ, shift_continuous, native_topological_entropy_zero,
    actual_coverMincard, no_harmonic_bound⟩

end TLMC8488

