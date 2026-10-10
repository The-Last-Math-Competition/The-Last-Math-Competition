import Mechanical
import CFRealization
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Real.Cardinality

noncomputable section

namespace SturmianCF

instance slope_uncountable : Uncountable Slope := by
  rw [← not_countable_iff]
  intro hc
  have hs : Set.Countable {t : ℝ | 0 < t ∧ t < 1 ∧ Irrational t} :=
    Set.countable_coe_iff.mp hc
  have hi : (Set.Ioo (0:ℝ) 1).Countable :=
    (hs.union (Set.countable_range (fun q : ℚ => (q:ℝ)))).mono (by
      intro x hx
      by_cases h : Irrational x
      · exact Or.inl ⟨hx.1,hx.2,h⟩
      · exact Or.inr (not_not.mp h))
  have hb := Cardinal.le_aleph0_iff_set_countable.2 hi
  rw [Cardinal.mk_Ioo_real (by norm_num : (0:ℝ)<1)] at hb
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hb

/-- Distinct slopes give distinct continued-fraction reals. -/
theorem real_of_slope_injective :
    Function.Injective (fun t : Slope => CFRealization.realOfWord (mechanical t)) :=
  CFRealization.realOfWord_injective.comp mechanical_injective

theorem exists_transcendental_slope :
    ∃ t : Slope, Transcendental ℚ (CFRealization.realOfWord (mechanical t)) := by
  by_contra! h
  have hc : Countable {x : ℝ // IsAlgebraic ℚ x} :=
    Set.countable_coe_iff.mpr (Algebraic.countable ℚ ℝ)
  let f : Slope → {x : ℝ // IsAlgebraic ℚ x} :=
    fun t => ⟨CFRealization.realOfWord (mechanical t), not_not.mp (h t)⟩
  have hinj : Function.Injective f := fun _ _ hf =>
    real_of_slope_injective (congrArg (fun x : {x : ℝ // IsAlgebraic ℚ x} => x.val) hf)
  exact (not_countable_iff.mpr slope_uncountable) hinj.countable

/-- Actual contiguous factors of the fractional partial-quotient word a₁a₂....
The integer part a₀ is deliberately not a letter of this word. -/
def quotientFactors (x : ℝ) (n : ℕ) : Set (Fin n → ℤ) :=
  Set.range (fun j : ℕ => fun i : Fin n => CFRealization.partialQuotient x (j+i.val+1))

def encodeBlock {n : ℕ} (u : Fin n → Fin 2) : Fin n → ℤ := fun i => (u i).val+1

theorem encodeBlock_injective (n : ℕ) : Function.Injective (@encodeBlock n) := by
  intro u v h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp [encodeBlock] at hi
  exact_mod_cast (add_right_cancel hi)

theorem quotientFactors_eq_image (w : ℕ → Fin 2) (n : ℕ) :
    quotientFactors (CFRealization.realOfWord w) n =
      encodeBlock '' (Set.range (block w n)) := by
  ext u
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨block w n j, ⟨j,rfl⟩, ?_⟩
    funext i
    simp [encodeBlock, block, CFRealization.partialQuotient_succ, CFRealization.digit]
  · rintro ⟨u, ⟨j,rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    funext i
    simp [encodeBlock, block, CFRealization.partialQuotient_succ, CFRealization.digit]

theorem quotientFactors_finite (w : ℕ → Fin 2) (n : ℕ) :
    (quotientFactors (CFRealization.realOfWord w) n).Finite := by
  rw [quotientFactors_eq_image]
  exact (Set.toFinite _).image _

theorem quotientFactors_ncard (w : ℕ → Fin 2) (n : ℕ) :
    (quotientFactors (CFRealization.realOfWord w) n).ncard = complexity w n := by
  rw [quotientFactors_eq_image, Set.ncard_image_of_injective _ (encodeBlock_injective n),
    ← Set.Nat.card_coe_set_eq]
  change Nat.card (Factor w n) = Fintype.card (Factor w n)
  exact Nat.card_eq_fintype_card

/-- The original existence statement, with every ordinary-continued-fraction
and factor-count condition stated directly for the same real `α`. -/
theorem conjecture00000000347 : ∃ α : ℝ,
    Transcendental ℚ α ∧
    CFRealization.partialQuotient α 0 = 0 ∧
    (∀ j : ℕ, 0 < Int.fract (CFRealization.completeQuotient α j)) ∧
    (∀ j : ℕ, CFRealization.partialQuotient α (j+1) = 1 ∨
      CFRealization.partialQuotient α (j+1) = 2) ∧
    (∀ n : ℕ, 0 < n → (quotientFactors α n).Finite ∧
      (quotientFactors α n).ncard = n+1) := by
  obtain ⟨t,ht⟩ := exists_transcendental_slope
  refine ⟨CFRealization.realOfWord (mechanical t), ht,
    CFRealization.partialQuotient_zero _,
    CFRealization.completeQuotient_fract_pos _, ?_, ?_⟩
  · intro j
    rw [CFRealization.partialQuotient_succ]
    have h := (mechanical t j).isLt
    dsimp [CFRealization.digit]
    omega
  · intro n _hn
    exact ⟨quotientFactors_finite _ _, by rw [quotientFactors_ncard, mechanical_complexity]⟩

/-- Factors of the full partial-quotient sequence, including its integer part. -/
def wholeQuotientFactors (x : ℝ) (n : ℕ) : Set (Fin n → ℤ) :=
  Set.range (fun j : ℕ => fun i : Fin n => CFRealization.partialQuotient x (j+i.val))

theorem wholeQuotientFactors_inverse (w : ℕ → Fin 2) (n : ℕ) :
    wholeQuotientFactors (CFRealization.realOfWord w)⁻¹ n =
      quotientFactors (CFRealization.realOfWord w) n := by
  unfold wholeQuotientFactors quotientFactors
  apply congrArg Set.range
  funext j i
  unfold CFRealization.partialQuotient
  rw [CFRealization.inverse_completeQuotient_shift]

theorem transcendental_inverse {x : ℝ} (hx : Transcendental ℚ x) :
    Transcendental ℚ x⁻¹ := by
  intro hi
  exact hx (by simpa only [inv_inv] using hi.inv)

/-- The alternative convention is also satisfied: this witness's full sequence
`a₀,a₁,...`, including its integer part, has exact complexity `n+1`. -/
theorem conjecture00000000347_including_integer_part : ∃ β : ℝ,
    Transcendental ℚ β ∧
    (∀ j : ℕ, 0 < Int.fract (CFRealization.completeQuotient β j)) ∧
    (∀ j : ℕ, CFRealization.partialQuotient β j = 1 ∨
      CFRealization.partialQuotient β j = 2) ∧
    (∀ n : ℕ, 0 < n → (wholeQuotientFactors β n).Finite ∧
      (wholeQuotientFactors β n).ncard = n+1) := by
  obtain ⟨t,ht⟩ := exists_transcendental_slope
  refine ⟨(CFRealization.realOfWord (mechanical t))⁻¹, transcendental_inverse ht,
    CFRealization.inverse_completeQuotient_fract_pos _, ?_, ?_⟩
  · intro j
    rw [CFRealization.inverse_partialQuotient]
    have h := (mechanical t j).isLt
    dsimp [CFRealization.digit]
    omega
  · intro n _hn
    rw [wholeQuotientFactors_inverse]
    exact ⟨quotientFactors_finite _ _, by rw [quotientFactors_ncard, mechanical_complexity]⟩

end SturmianCF

#print axioms SturmianCF.conjecture00000000347

#print axioms SturmianCF.conjecture00000000347_including_integer_part
