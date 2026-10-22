import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Filter Finset
open scoped Topology
namespace Conjecture9183

def complete (n : ℕ) : SimpleGraph (Fin (n + 2)) := ⊤

def punctured (n : ℕ) : SimpleGraph (Fin (n + 2)) where
  Adj x y := x ≠ y ∧ ¬ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0))
  symm := by intro x y h; tauto
  loopless := by intro x h; exact h.1 rfl

def CompleteSentence {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ x y, x ≠ y → G.Adj x y

theorem sentence_complete (n : ℕ) : CompleteSentence (complete n) := by
  intro x y h; exact h

theorem sentence_punctured (n : ℕ) : ¬ CompleteSentence (punctured n) := by
  intro h
  have e := h 0 1 (by intro e; have := congrArg Fin.val e; simp at this)
  exact e.2 (Or.inl ⟨rfl, rfl⟩)

def kernel {V : Type} (G : SimpleGraph V) (x y : V) : ℝ :=
  @ite ℝ (G.Adj x y) (Classical.propDecidable _) 1 0

def defect (n : ℕ) (x y : Fin (n + 2)) : ℝ :=
  (if x = y then 1 else 0) +
  (if x = 0 ∧ y = 1 then 1 else 0) +
  (if x = 1 ∧ y = 0 then 1 else 0)

theorem punctured_defect (n : ℕ) (x y : Fin (n + 2)) :
    1 - kernel (punctured n) x y = defect n x y := by
  have z : (0 : Fin (n + 2)) ≠ 1 := by
    intro e; have := congrArg Fin.val e; simp at this
  simp only [kernel, punctured, defect]
  split_ifs <;> simp_all

theorem defect_nonneg (n : ℕ) (x y : Fin (n + 2)) : 0 ≤ defect n x y := by
  unfold defect; positivity

theorem total_defect (n : ℕ) :
    (∑ x : Fin (n + 2), ∑ y : Fin (n + 2), defect n x y) = (n : ℝ) + 4 := by
  simp [defect, sum_add_distrib, ite_and, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- A measurable rectangle occupies a fraction a(x), respectively b(y),
of each equal interval in the step graphon. This is its exact normalized
bilinear deficit from the constant-one graphon. -/
def rectangleDeficit (n : ℕ) (G : SimpleGraph (Fin (n + 2)))
    (a b : Fin (n + 2) → ℝ) : ℝ :=
  (∑ x, ∑ y, a x * b y * (1 - kernel G x y)) / ((n : ℝ) + 2)^2

theorem weighted_bound (n : ℕ) (a b : Fin (n + 2) → ℝ)
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) :
    0 ≤ rectangleDeficit n (punctured n) a b ∧
    rectangleDeficit n (punctured n) a b ≤ ((n : ℝ) + 4) / ((n : ℝ) + 2)^2 := by
  have hterm (x y : Fin (n + 2)) :
      0 ≤ a x * b y * (1 - kernel (punctured n) x y) ∧
      a x * b y * (1 - kernel (punctured n) x y) ≤ defect n x y := by
    rw [punctured_defect]
    have hab : a x * b y ≤ 1 := by nlinarith [(ha x).1, (ha x).2, (hb y).1, (hb y).2]
    constructor
    · exact mul_nonneg (mul_nonneg (ha x).1 (hb y).1) (defect_nonneg n x y)
    · nlinarith [defect_nonneg n x y]
  constructor
  · apply div_nonneg _ (sq_nonneg _)
    exact sum_nonneg fun x _ => sum_nonneg fun y _ => (hterm x y).1
  · unfold rectangleDeficit
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    rw [← total_defect n]
    exact sum_le_sum fun x _ => sum_le_sum fun y _ => (hterm x y).2

theorem complete_weighted_bound (n : ℕ) (a b : Fin (n + 2) → ℝ)
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) :
    0 ≤ rectangleDeficit n (complete n) a b ∧
    rectangleDeficit n (complete n) a b ≤ ((n : ℝ) + 4) / ((n : ℝ) + 2)^2 := by
  have hk (x y : Fin (n + 2)) :
      0 ≤ 1 - kernel (complete n) x y ∧
      1 - kernel (complete n) x y ≤ 1 - kernel (punctured n) x y := by
    classical
    simp only [kernel, complete, SimpleGraph.top_adj, punctured]
    split_ifs <;> simp_all
  constructor
  · apply div_nonneg _ (sq_nonneg _)
    exact sum_nonneg fun x _ => sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (ha x).1 (hb y).1) (hk x y).1
  · apply le_trans _ (weighted_bound n a b ha hb).2
    unfold rectangleDeficit
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hk x y).2 (mul_nonneg (ha x).1 (hb y).1)

def errorBound (n : ℕ) : ℝ := ((n : ℝ) + 4) / ((n : ℝ) + 2)^2

theorem error_tendsto : Tendsto errorBound atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2))
  have h := hi.add ((hi.mul hi).const_mul 2)
  simp only [zero_mul, mul_zero, add_zero] at h
  convert h using 1
  ext n
  unfold errorBound
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Uniform control of all fractional rectangles in the equal-part step kernel.
For the target kernel 1 this is precisely convergence in cut norm. -/
def CutConvergesToOne (A : (n : ℕ) → SimpleGraph (Fin (n + 2))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∀ a b : Fin (n + 2) → ℝ,
      (∀ x, 0 ≤ a x ∧ a x ≤ 1) → (∀ y, 0 ≤ b y ∧ b y ≤ 1) →
      0 ≤ rectangleDeficit n (A n) a b ∧ rectangleDeficit n (A n) a b < ε

theorem convergence_of_bound (A : (n : ℕ) → SimpleGraph (Fin (n + 2)))
    (hA : ∀ n a b, (∀ x, 0 ≤ a x ∧ a x ≤ 1) →
      (∀ y, 0 ≤ b y ∧ b y ≤ 1) →
      0 ≤ rectangleDeficit n (A n) a b ∧ rectangleDeficit n (A n) a b ≤ errorBound n) :
    CutConvergesToOne A := by
  intro ε hε
  have he : ∀ᶠ n in atTop, errorBound n < ε := error_tendsto.eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨N, fun n hn a b ha hb => ⟨(hA n a b ha hb).1,
    lt_of_le_of_lt (hA n a b ha hb).2 (hN n hn)⟩⟩

theorem complete_cut_limit : CutConvergesToOne complete :=
  convergence_of_bound complete complete_weighted_bound

theorem punctured_cut_limit : CutConvergesToOne punctured :=
  convergence_of_bound punctured weighted_bound

/-- A necessary consequence of graphons characterizing first-order limits,
specialized to one explicitly stated first-order sentence and the target 1. -/
def GraphonDeterminesCompleteness : Prop :=
  ∀ A B : (n : ℕ) → SimpleGraph (Fin (n + 2)),
    CutConvergesToOne A → CutConvergesToOne B →
    ((∀ᶠ n in atTop, CompleteSentence (A n)) ↔
     (∀ᶠ n in atTop, CompleteSentence (B n)))

theorem conjecture9183_false : ¬ GraphonDeterminesCompleteness := by
  intro h
  have hp := (h complete punctured complete_cut_limit punctured_cut_limit).mp
    (Eventually.of_forall sentence_complete)
  have hf : ∀ᶠ n : ℕ in atTop, False := hp.mono fun n hn => sentence_punctured n hn
  obtain ⟨n, hn⟩ := hf.exists
  exact hn

#print axioms complete_cut_limit
#print axioms punctured_cut_limit
#print axioms conjecture9183_false
end Conjecture9183
