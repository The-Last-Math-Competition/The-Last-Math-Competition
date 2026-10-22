import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! The actual integer group, with its shortest-word metric for ±1, is
0-hyperbolic and torsion free but contains no free subgroup of rank two.
The statement's universal construction omits the non-elementary hypothesis. -/
namespace TLMC4858

def SignedWord (w : List ℤ) : Prop := ∀ a ∈ w, a = 1 ∨ a = -1

theorem signed_word_bound (w : List ℤ) (hw : SignedWord w) :
    w.sum.natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht : SignedWord w := fun b hb => hw b (by simp [hb])
    have h := Int.natAbs_add_le a w.sum
    rcases ha with rfl | rfl <;> simp only [List.sum_cons, List.length_cons] <;>
      have h' := ih ht <;> norm_num at h <;> omega

theorem shortest_signed_word (z : ℤ) :
    ∃ w : List ℤ, SignedWord w ∧ w.sum = z ∧ w.length = z.natAbs := by
  cases z with
  | ofNat n =>
    refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
    · intro a ha; left; simpa using List.eq_of_mem_replicate ha
    · simp
    · simp
  | negSucc n =>
    refine ⟨List.replicate (n+1) (-1), ?_, ?_, ?_⟩
    · intro a ha; right; simpa using List.eq_of_mem_replicate ha
    · simp; omega
    · simp

/-- True shortest length among all signed generator words, not an assigned formula. -/
noncomputable def wordLength (z : ℤ) : ℕ :=
  sInf {n : ℕ | ∃ w : List ℤ, SignedWord w ∧ w.sum = z ∧ w.length = n}

theorem wordLength_eq (z : ℤ) : wordLength z = z.natAbs := by
  obtain ⟨w, hw, hs, hl⟩ := shortest_signed_word z
  unfold wordLength
  apply IsLeast.csInf_eq
  refine ⟨⟨w, hw, hs, hl⟩, ?_⟩
  rintro n ⟨u, hu, rfl, rfl⟩
  exact signed_word_bound u hu

noncomputable def wordDistance (x y : ℤ) : ℕ := wordLength (y-x)

theorem wordDistance_eq (x y : ℤ) : wordDistance x y = (y-x).natAbs :=
  wordLength_eq _

theorem cayley_adj_iff (x y : ℤ) :
    (SimpleGraph.addCayley ({1} : Set ℤ)).Adj x y ↔ y-x = 1 ∨ y-x = -1 := by
  rw [SimpleGraph.addCayley_adj]
  simp only [Set.mem_singleton_iff]
  omega

theorem generating_set_finite : ({1} : Set ℤ).Finite := Set.finite_singleton _

theorem signed_generators_generate (z : ℤ) :
    ∃ w : List ℤ, (∀ a ∈ w, a ∈ ({1,-1} : Set ℤ)) ∧ w.sum = z := by
  obtain ⟨w, hw, hs, _⟩ := shortest_signed_word z
  exact ⟨w, by simpa [SignedWord] using hw, hs⟩

/-- The usual real metric on integers is exactly the true signed-word distance. -/
theorem wordDistance_real (x y : ℤ) : (wordDistance x y : ℝ) = dist x y := by
  rw [wordDistance_eq, Int.dist_eq]
  simp [abs_sub_comm]

/-- Gromov's standard four-point inequality with constant zero. -/
def ZeroHyperbolic (d : ℤ → ℤ → ℕ) : Prop :=
  ∀ x y z t, d x y + d z t ≤ max (d x z + d y t) (d z y + d x t)

theorem integer_word_metric_zero_hyperbolic : ZeroHyperbolic wordDistance := by
  intro x y z t
  simp only [wordDistance_eq]
  omega

theorem integer_real_metric_zero_hyperbolic (x y z t : ℤ) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist z y + dist x t) := by
  simpa only [← wordDistance_real, ← Nat.cast_add, ← Nat.cast_max, Nat.cast_le] using
    integer_word_metric_zero_hyperbolic x y z t

theorem integer_torsion_free (z : ℤ) (n : ℕ) (hn : n ≠ 0) (hz : n • z = 0) : z = 0 := by
  simpa only [nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, hn, false_or] using hz

theorem free_generators_do_not_commute :
    FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 ≠
      FreeGroup.of 1 * FreeGroup.of 0 := by
  intro h
  have h' := congrArg FreeGroup.toWord h
  norm_num [FreeGroup.toWord_mul, FreeGroup.toWord_of, FreeGroup.reduce] at h'

theorem no_injective_free_hom (f : FreeGroup (Fin 2) →* Multiplicative ℤ) :
    ¬ Function.Injective f := by
  intro hf
  apply free_generators_do_not_commute
  apply hf
  simp only [map_mul]
  exact mul_comm _ _

theorem no_free_rank_two_subgroup (H : Subgroup (Multiplicative ℤ)) :
    ¬ Nonempty (FreeGroup (Fin 2) ≃* H) := by
  rintro ⟨e⟩
  have hinj : Function.Injective (H.subtype.comp e.toMonoidHom) :=
    H.subtype_injective.comp e.injective
  exact no_injective_free_hom _ hinj

/-- A necessary universal existence conclusion fails on the actual integer group. -/
theorem universal_free_subgroup_claim_false :
    ¬ (∃ H : Subgroup (Multiplicative ℤ), Nonempty (FreeGroup (Fin 2) ≃* H)) := by
  rintro ⟨H, hH⟩
  exact no_free_rank_two_subgroup H hH

/-- The geometric and algebraic properties of the same actual group are closed together. -/
theorem cyclic_counterexample :
    ({1} : Set ℤ).Finite ∧
    (∀ z : ℤ, ∃ w : List ℤ, SignedWord w ∧ w.sum = z) ∧
    ZeroHyperbolic wordDistance ∧
    (∀ z : ℤ, ∀ n : ℕ, n ≠ 0 → n • z = 0 → z = 0) ∧
    ¬ (∃ H : Subgroup (Multiplicative ℤ), Nonempty (FreeGroup (Fin 2) ≃* H)) := by
  refine ⟨generating_set_finite, ?_, integer_word_metric_zero_hyperbolic,
    integer_torsion_free, universal_free_subgroup_claim_false⟩
  intro z
  obtain ⟨w, hw, hs, _⟩ := shortest_signed_word z
  exact ⟨w, hw, hs⟩

end TLMC4858
