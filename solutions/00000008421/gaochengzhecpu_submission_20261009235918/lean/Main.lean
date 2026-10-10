import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology

namespace Conjecture8421

/-- The usual finite covering problem, with no repeated blocks. -/
def Covers {N : ℕ} (k t : ℕ) (B : Finset (Finset (Fin N))) : Prop :=
  (∀ b ∈ B, b.card = k) ∧
    ∀ s : Finset (Fin N), s.card = t → ∃ b ∈ B, s ⊆ b

abbrev Vertex (n : ℕ) := Fin (n + 2)

def block {n : ℕ} (v : Vertex n) : Finset (Vertex n) := Finset.univ.erase v

theorem block_card {n : ℕ} (v : Vertex n) : (block v).card = n + 1 := by
  simp [block]

theorem block_injective (n : ℕ) : Function.Injective (@block n) := by
  intro a b hab
  by_contra hne
  have ha : a ∈ block b := by simp [block, hne]
  rw [← hab] at ha
  simp [block] at ha

theorem block_representation {n : ℕ} {b : Finset (Vertex n)}
    (hb : b.card = n + 1) : ∃ v : Vertex n, b = block v := by
  have hcard : (Finset.univ \ b).card = 1 := by
    rw [Finset.card_sdiff (Finset.subset_univ b)]
    simp [hb]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, ?_⟩
  ext x
  have hx := Finset.ext_iff.mp hv x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hx
  simp only [block, Finset.mem_erase, Finset.mem_univ, and_true]
  simpa only [not_not] using not_congr hx

def omissions {n : ℕ} (B : Finset (Finset (Vertex n))) : Finset (Vertex n) :=
  Finset.univ.filter (fun v => block v ∈ B)

theorem mem_omissions {n : ℕ} {B : Finset (Finset (Vertex n))} {v : Vertex n} :
    v ∈ omissions B ↔ block v ∈ B := by simp [omissions]

theorem image_omissions {n : ℕ} {B : Finset (Finset (Vertex n))}
    (hB : ∀ b ∈ B, b.card = n + 1) : (omissions B).image block = B := by
  ext b
  constructor
  · intro hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact mem_omissions.mp hv
  · intro hb
    obtain ⟨v, rfl⟩ := block_representation (hB b hb)
    exact Finset.mem_image.mpr ⟨v, mem_omissions.mpr hb, rfl⟩

theorem card_omissions {n : ℕ} {B : Finset (Finset (Vertex n))}
    (hB : ∀ b ∈ B, b.card = n + 1) : (omissions B).card = B.card := by
  calc
    _ = ((omissions B).image block).card :=
      (Finset.card_image_of_injective _ (block_injective n)).symm
    _ = B.card := congrArg Finset.card (image_omissions hB)

theorem cover_lower_bound {n : ℕ} {B : Finset (Finset (Vertex n))}
    (hB : Covers (n + 1) n B) : n + 1 ≤ B.card := by
  have hs : (Finset.univ \ omissions B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have hna : a ∉ omissions B := (Finset.mem_sdiff.mp ha).2
    have hnb : b ∉ omissions B := (Finset.mem_sdiff.mp hb).2
    let s : Finset (Vertex n) := (Finset.univ.erase a).erase b
    have hscard : s.card = n := by
      simp [s, Finset.card_erase_of_mem, Ne.symm hab]
    obtain ⟨d, hdB, hsd⟩ := hB.2 s hscard
    obtain ⟨v, rfl⟩ := block_representation (hB.1 d hdB)
    have hv : v ∈ omissions B := mem_omissions.mpr hdB
    have hva : v ≠ a := fun h => hna (h ▸ hv)
    have hvb : v ≠ b := fun h => hnb (h ▸ hv)
    have hvs : v ∈ s := by simp [s, hva, hvb]
    have hbad := hsd hvs
    simp [block] at hbad
  rw [Finset.card_sdiff (Finset.subset_univ _), card_omissions hB.1] at hs
  have hc : (Finset.univ : Finset (Vertex n)).card = n + 2 := by simp
  rw [hc] at hs
  omega

def optimalFamily (n : ℕ) : Finset (Finset (Vertex n)) :=
  (Finset.univ.erase (0 : Vertex n)).image block

theorem optimalFamily_card (n : ℕ) : (optimalFamily n).card = n + 1 := by
  rw [optimalFamily, Finset.card_image_of_injective _ (block_injective n)]
  simp

theorem optimalFamily_covers (n : ℕ) : Covers (n + 1) n (optimalFamily n) := by
  constructor
  · intro b hb
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
    exact block_card v
  · intro s hs
    have hc : (Finset.univ \ s).card = 2 := by
      rw [Finset.card_sdiff (Finset.subset_univ s)]
      simp [hs]
    obtain ⟨v, hv, hv0⟩ := Finset.exists_ne_of_one_lt_card (by omega :
        1 < (Finset.univ \ s).card) (0 : Vertex n)
    refine ⟨block v, Finset.mem_image.mpr ⟨v, ?_, rfl⟩, ?_⟩
    · simp [hv0]
    · intro x hx
      have hvnot : v ∉ s := (Finset.mem_sdiff.mp hv).2
      have hxv : x ≠ v := fun h => hvnot (h ▸ hx)
      simp [block, hxv]

/-- The minimum among all genuine covering families, not a surrogate count. -/
def coveringNumber (N k t : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ B : Finset (Finset (Fin N)), Covers k t B ∧ B.card = m}

theorem coveringNumber_exact (n : ℕ) : coveringNumber (n + 2) (n + 1) n = n + 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨optimalFamily n, optimalFamily_covers n, optimalFamily_card n⟩
  · apply le_csInf
    · exact ⟨n + 1, optimalFamily n, optimalFamily_covers n, optimalFamily_card n⟩
    · intro m hm
      obtain ⟨B, hB, rfl⟩ := hm
      exact cover_lower_bound hB

def countingBound (N k t : ℕ) : ℝ :=
  (Nat.choose N t : ℝ) / (Nat.choose k t : ℝ)

theorem countingBound_exact (n : ℕ) :
    countingBound (n + 2) (n + 1) n = (n + 2 : ℝ) / 2 := by
  have h := Nat.choose_mul_succ_eq (n + 1) n
  rw [Nat.choose_succ_self_right] at h
  have h' : (n + 1 : ℝ) * (n + 2) = ((n + 2).choose n : ℝ) * 2 := by
    exact_mod_cast (by simpa [Nat.add_assoc] using h)
  rw [countingBound, Nat.choose_succ_self_right]
  push_cast
  apply (div_eq_iff (by positivity : (n + 1 : ℝ) ≠ 0)).mpr
  nlinarith

/-- The correction to the ordinary counting lower bound in the source. -/
def excess (n : ℕ) : ℝ :=
  (coveringNumber (n + 2) (n + 1) n : ℝ) /
    countingBound (n + 2) (n + 1) n - 1

theorem excess_exact (n : ℕ) : excess n = (n : ℝ) / (n + 2) := by
  rw [excess, coveringNumber_exact, countingBound_exact]
  push_cast
  field_simp
  ring

theorem excess_lt_one (n : ℕ) : excess n < 1 := by
  rw [excess_exact]
  exact (div_lt_one (by positivity)).mpr (by linarith)

/-- Even the positive lower inequality required by Theta(log t) fails. -/
theorem no_eventual_log_lower_bound (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧ excess n < c * Real.log n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl : ∀ᶠ n : ℕ in atTop, 1 / c < Real.log (n : ℝ) :=
    hlog.eventually (eventually_gt_atTop (1 / c))
  obtain ⟨n, hn, hln⟩ := ((eventually_ge_atTop (max N 2)).and hl).exists
  refine ⟨n, le_trans (le_max_left _ _) hn, le_trans (le_max_right _ _) hn, ?_⟩
  have hlarge : 1 < c * Real.log (n : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hln
    nlinarith
  exact (excess_lt_one n).trans hlarge

theorem conjecture8421_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n → 2 ≤ n → c * Real.log n ≤ excess n := by
  rintro ⟨c, hc, N, hN⟩
  obtain ⟨n, hn, hn2, hbad⟩ := no_eventual_log_lower_bound c hc N
  exact (not_lt_of_ge (hN n hn hn2)) hbad

end Conjecture8421

#print axioms Conjecture8421.coveringNumber_exact
#print axioms Conjecture8421.countingBound_exact
#print axioms Conjecture8421.excess_exact
#print axioms Conjecture8421.no_eventual_log_lower_bound
#print axioms Conjecture8421.conjecture8421_false
