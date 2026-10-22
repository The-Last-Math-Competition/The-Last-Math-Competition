import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.List.Chain
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Matrix
open scoped BigOperators
noncomputable section
namespace Conjecture9634
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

abbrev Alphabet := Fin 4
abbrev Word := List Alphabet

/-- General finite hidden Markov model in transition-emission matrix form. -/
structure HMM (n : ℕ) where
  initial : Fin n → ℝ
  transition : Alphabet → Matrix (Fin n) (Fin n) ℝ
  initial_nonneg : ∀ i, 0 ≤ initial i
  initial_sum : ∑ i, initial i = 1
  transition_nonneg : ∀ a i j, 0 ≤ transition a i j
  transition_sum : ∀ i, ∑ a, ∑ j, transition a i j = 1

/-- Every conventional current-state-emission HMM, with an arbitrary
initial distribution, is in our class: emit at state i, then transition.
The symbol kernel is E_i(a) Q_ij, not Q_ij E_j(a). -/
def fromStateEmission {n : ℕ} (μ : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (E : Fin n → Alphabet → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQsum : ∀ i, ∑ j, Q i j = 1)
    (hE : ∀ i a, 0 ≤ E i a) (hEsum : ∀ i, ∑ a, E i a = 1) : HMM n where
  initial := μ
  transition := fun a i j => E i a * Q i j
  initial_nonneg := hμ
  initial_sum := hμsum
  transition_nonneg := fun a i j => mul_nonneg (hE i a) (hQ i j)
  transition_sum := by
    intro i
    simp_rw [← Finset.mul_sum, hQsum, mul_one]
    exact hEsum i

def wordMatrix {n : ℕ} (M : HMM n) (w : Word) : Matrix (Fin n) (Fin n) ℝ :=
  (w.map M.transition).prod

def future {n : ℕ} (M : HMM n) (w : Word) : Fin n → ℝ :=
  wordMatrix M w *ᵥ (fun _ => 1)

def reach {n : ℕ} (M : HMM n) (w : Word) : Fin n → ℝ :=
  M.initial ᵥ* wordMatrix M w

def probability {n : ℕ} (M : HMM n) (w : Word) : ℝ :=
  dotProduct M.initial (future M w)

def hankel {n : ℕ} (M : HMM n) : Matrix Word Word ℝ :=
  fun u v => probability M (u ++ v)

theorem wordMatrix_append {n : ℕ} (M : HMM n) (u v : Word) :
    wordMatrix M (u ++ v) = wordMatrix M u * wordMatrix M v := by
  simp [wordMatrix]

theorem future_nil {n : ℕ} (M : HMM n) : future M [] = fun _ => 1 := by
  simp [future, wordMatrix]

theorem future_cons {n : ℕ} (M : HMM n) (a : Alphabet) (w : Word) :
    future M (a :: w) = M.transition a *ᵥ future M w := by
  simp [future, wordMatrix, Matrix.mulVec_mulVec]

theorem hankel_factor {n : ℕ} (M : HMM n) (u v : Word) :
    hankel M u v = dotProduct (reach M u) (future M v) := by
  simp only [hankel, probability, future, wordMatrix_append, reach,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

theorem future_nonneg {n : ℕ} (M : HMM n) (w : Word) (i : Fin n) :
    0 ≤ future M w i := by
  induction w generalizing i with
  | nil => simp [future_nil]
  | cons a w ih =>
    rw [future_cons]
    exact Finset.sum_nonneg (s := Finset.univ) fun j _ => mul_nonneg (M.transition_nonneg a i j) (ih j)

theorem wordMatrix_nonneg {n : ℕ} (M : HMM n) (w : Word) (i j : Fin n) :
    0 ≤ wordMatrix M w i j := by
  induction w generalizing i j with
  | nil => simp [wordMatrix, Matrix.one_apply]; split_ifs <;> norm_num
  | cons a w ih =>
    simp only [wordMatrix, List.map_cons, List.prod_cons, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (M.transition_nonneg a i k) (ih k j)

theorem reach_nonneg {n : ℕ} (M : HMM n) (w : Word) (i : Fin n) :
    0 ≤ reach M w i := by
  exact Finset.sum_nonneg (s := Finset.univ) fun j _ => mul_nonneg (M.initial_nonneg j) (wordMatrix_nonneg M w j i)

theorem probability_nonneg {n : ℕ} (M : HMM n) (w : Word) :
    0 ≤ probability M w := by
  exact Finset.sum_nonneg (s := Finset.univ) fun i _ => mul_nonneg (M.initial_nonneg i) (future_nonneg M w i)

def P : Matrix Alphabet Alphabet ℝ :=
  !![1/2,1/2,0,0; 0,1/2,1/2,0; 0,0,1/2,1/2; 1/2,0,0,1/2]

theorem P_nonneg (i j : Alphabet) : 0 ≤ P i j := by
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem P_row_sum (i : Alphabet) : ∑ j, P i j = 1 := by
  fin_cases i <;> norm_num [P, Fin.sum_univ_succ]

theorem P_col_sum (j : Alphabet) : ∑ i, P i j = 1 := by
  fin_cases j <;> norm_num [P, Fin.sum_univ_succ]

def model : HMM 4 where
  initial := fun _ => 1/4
  transition := fun a i j => if j = a then P i a else 0
  initial_nonneg := by intro i; norm_num
  initial_sum := by norm_num [Fin.sum_univ_succ]
  transition_nonneg := by intro a i j; split_ifs; exact P_nonneg i a; norm_num
  transition_sum := by intro i; simpa using P_row_sum i

theorem model_future_cons (a : Alphabet) (w : Word) (i : Alphabet) :
    future model (a :: w) i = P i a * future model w a := by
  rw [future_cons]
  simp [model, Matrix.mulVec, dotProduct, ite_mul]

theorem model_future_single (a i : Alphabet) : future model [a] i = P i a := by
  simp [model_future_cons, future_nil]

theorem model_probability_cons (a : Alphabet) (w : Word) :
    probability model (a :: w) = (1/4 : ℝ) * future model w a := by
  change (∑ i, (1/4 : ℝ) * future model (a :: w) i) = _
  simp_rw [model_future_cons]
  rw [← Finset.mul_sum, ← Finset.sum_mul, P_col_sum]
  ring

theorem model_probability_nil : probability model [] = 1 := by
  norm_num [probability, model, future_nil, dotProduct, Fin.sum_univ_succ]

theorem model_hankel_letters (a b : Alphabet) :
    hankel model [a] [b] = (1/4 : ℝ) * P a b := by
  simp [hankel, model_probability_cons, model_future_single]

theorem future_relation (w : Word) :
    future model w 3 = future model w 0 - future model w 1 + future model w 2 := by
  cases w with
  | nil => norm_num [future_nil]
  | cons a w =>
    simp_rw [model_future_cons]
    fin_cases a <;> norm_num [P, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail]

def leftFactor : Matrix Word (Fin 3) ℝ :=
  fun u => ![reach model u 0 + reach model u 3,
    reach model u 1 - reach model u 3, reach model u 2 + reach model u 3]

def rightFactor : Matrix (Fin 3) Word ℝ :=
  fun i v => future model v i.castSucc

theorem whole_hankel_factorization : hankel model = leftFactor * rightFactor := by
  ext u v
  rw [hankel_factor]
  simp [dotProduct, Matrix.mul_apply, leftFactor, rightFactor, Fin.sum_univ_succ]
  rw [future_relation]
  ring

theorem whole_hankel_rank_upper : (hankel model).cRank ≤ (3 : Cardinal) := by
  have hspan : Submodule.span ℝ (Set.range (hankel model)ᵀ) ≤
      Submodule.span ℝ (Set.range leftFactorᵀ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have heq : (hankel model)ᵀ v = ∑ i : Fin 3, rightFactor i v • leftFactorᵀ i := by
      ext u
      simp [whole_hankel_factorization, Matrix.mul_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  exact (Submodule.rank_mono hspan).trans (by simpa using leftFactor.cRank_le_card_width)

def minor : Matrix (Fin 3) (Fin 3) ℝ :=
  (hankel model).submatrix (fun i => [i.castSucc]) (fun i => [i.castSucc])

theorem minor_eq : minor = !![1/8,1/8,0; 0,1/8,1/8; 0,0,1/8] := by
  have hc0 : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
  have hc1 : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
  have hc2 : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [minor, Matrix.submatrix_apply, model_hankel_letters, hc0, hc1, hc2,
      P, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem minor_det : minor.det = 1/512 := by
  rw [minor_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem minor_rank : minor.rank = 3 := by
  have hu : IsUnit minor.det := isUnit_iff_ne_zero.mpr (by rw [minor_det]; norm_num)
  simpa using Matrix.rank_of_isUnit minor (minor.isUnit_iff_isUnit_det.mpr hu)

theorem minor_cRank : minor.cRank = (3 : Cardinal) := by
  have hf : minor.cRank < Cardinal.aleph0 :=
    lt_of_le_of_lt minor.cRank_le_card_width (Cardinal.nat_lt_aleph0 _)
  rw [← Cardinal.cast_toNat_of_lt_aleph0 hf, Matrix.cRank_toNat_eq_rank, minor_rank]
  norm_num

theorem whole_hankel_rank : (hankel model).cRank = (3 : Cardinal) := by
  apply le_antisymm whole_hankel_rank_upper
  have h := (hankel model).cRank_submatrix_le (fun i : Fin 3 => [i.castSucc])
    (fun i : Fin 3 => [i.castSucc])
  change minor.cRank ≤ _ at h
  simpa [minor_cRank] using h

theorem diagonal_positive (a : Alphabet) : 0 < hankel model [a] [a] := by
  fin_cases a <;> norm_num [model_hankel_letters, P]

theorem crossing_zero (a b : Alphabet) (h : a ≠ b) :
    hankel model [a] [b] = 0 ∨ hankel model [b] [a] = 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [model_hankel_letters, P] at *

/-- The four positive diagonal entries form a nonnegative-rank fooling set. -/
theorem nonnegative_factor_lower {n : ℕ}
    (A : Matrix Alphabet (Fin n) ℝ) (B : Matrix (Fin n) Alphabet ℝ)
    (hA : ∀ i s, 0 ≤ A i s) (hB : ∀ s j, 0 ≤ B s j)
    (heq : ∀ i j, ∑ s, A i s * B s j = hankel model [i] [j]) : 4 ≤ n := by
  classical
  have hex : ∀ i : Alphabet, ∃ s : Fin n, 0 < A i s * B s i := by
    intro i
    by_contra! h
    have hn := Finset.sum_nonpos (s := Finset.univ) (fun s _ => h s)
    rw [heq] at hn
    exact (not_le_of_gt (diagonal_positive i)) hn
  let f : Alphabet → Fin n := fun i => Classical.choose (hex i)
  have hf (i : Alphabet) : 0 < A i (f i) * B (f i) i := Classical.choose_spec (hex i)
  have hterm (i j : Alphabet) (s : Fin n) :
      A i s * B s j ≤ hankel model [i] [j] := by
    rw [← heq]
    exact Finset.single_le_sum (fun t _ => mul_nonneg (hA i t) (hB t j)) (Finset.mem_univ s)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hai : 0 < A i (f i) := by
      by_contra! hn
      exact (not_le_of_gt (hf i)) (mul_nonpos_of_nonpos_of_nonneg hn (hB _ _))
    have hbi : 0 < B (f i) i := by
      by_contra! hn
      exact (not_le_of_gt (hf i)) (mul_nonpos_of_nonneg_of_nonpos (hA _ _) hn)
    have haj : 0 < A j (f j) := by
      by_contra! hn
      exact (not_le_of_gt (hf j)) (mul_nonpos_of_nonpos_of_nonneg hn (hB _ _))
    have hbj : 0 < B (f j) j := by
      by_contra! hn
      exact (not_le_of_gt (hf j)) (mul_nonpos_of_nonneg_of_nonpos (hA _ _) hn)
    rcases crossing_zero i j hne with hz | hz
    · have hp := mul_pos hai hbj
      rw [← hij] at hp
      have hh := hterm i j (f i)
      rw [hz] at hh
      exact (not_le_of_gt hp) hh
    · have hp := mul_pos haj hbi
      rw [hij] at hp
      have hh := hterm j i (f j)
      rw [hz] at hh
      exact (not_le_of_gt hp) hh
  simpa using Fintype.card_le_of_injective f hinj

def Realizes {n : ℕ} (M : HMM n) : Prop :=
  ∀ w : Word, probability M w = probability model w

theorem any_HMM_needs_four_states {n : ℕ} (M : HMM n) (hM : Realizes M) : 4 ≤ n := by
  apply nonnegative_factor_lower
    (fun i s => reach M [i] s) (fun s j => future M [j] s)
    (fun i s => reach_nonneg M [i] s) (fun s j => future_nonneg M [j] s)
  intro i j
  change dotProduct (reach M [i]) (future M [j]) = _
  rw [← hankel_factor]
  exact hM ([i] ++ [j])

theorem minimal_hidden_state_count :
    IsLeast {n : ℕ | ∃ M : HMM n, Realizes M} 4 := by
  refine ⟨⟨model, fun _ => rfl⟩, ?_⟩
  rintro n ⟨M,hM⟩
  exact any_HMM_needs_four_states M hM

def emission (state symbol : Alphabet) : ℝ := if state = symbol then 1 else 0

theorem emission_nonneg (i a : Alphabet) : 0 ≤ emission i a := by
  simp [emission]; split_ifs <;> norm_num

theorem emission_sum (i : Alphabet) : ∑ a, emission i a = 1 := by
  simp [emission]

/-- This specific model is also an ordinary state-emission HMM: the observation
is the hidden state itself, after a transition with matrix P. -/
theorem transition_emission (a i j : Alphabet) :
    model.transition a i j = P i j * emission j a := by
  by_cases h : j = a <;> simp [model, emission, h]

theorem initial_stationary : model.initial ᵥ* P = model.initial := by
  ext j
  change (∑ i, (1/4 : ℝ) * P i j) = 1/4
  rw [← Finset.mul_sum, P_col_sum]
  ring

theorem stationary_left_consistency (w : Word) :
    (∑ a, probability model (a :: w)) = probability model w := by
  change (∑ a, probability model (a :: w)) = ∑ i, (1/4 : ℝ) * future model w i
  simp_rw [model_probability_cons]

theorem probability_reach (w : Word) :
    probability model w = ∑ i, reach model w i := by
  have h := hankel_factor model w []
  simpa [hankel, future_nil, dotProduct] using h

theorem stationary_right_consistency (w : Word) :
    (∑ a, probability model (w ++ [a])) = probability model w := by
  change (∑ a, hankel model w [a]) = _
  simp_rw [hankel_factor]
  simp only [dotProduct]
  simp_rw [model_future_single]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, P_row_sum, mul_one]
  exact (probability_reach w).symm

def allowedEdge (i j : Alphabet) : Prop := 0 < P i j

theorem allowedEdge_self (i : Alphabet) : allowedEdge i i := by
  fin_cases i <;> norm_num [allowedEdge, P]

theorem allowedEdge_iff (i j : Alphabet) :
    allowedEdge i j ↔ j = i ∨ j = i + 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [allowedEdge, P] <;> decide

theorem future_positive_iff_path (i : Alphabet) (w : Word) :
    0 < future model w i ↔ List.Chain allowedEdge i w := by
  induction w generalizing i with
  | nil => simp [future_nil]
  | cons a w ih =>
    rw [model_future_cons, List.chain_cons, ← ih]
    constructor
    · intro h
      rcases mul_pos_iff.mp h with h | h
      · exact h
      · exact False.elim ((not_lt_of_ge (P_nonneg i a)) h.1)
    · rintro ⟨h₁,h₂⟩
      exact mul_pos h₁ h₂

theorem positive_probability_iff_path (w : Word) :
    0 < probability model w ↔ List.Chain' allowedEdge w := by
  cases w with
  | nil => simp [model_probability_nil]
  | cons a w =>
    rw [model_probability_cons]
    have h : 0 < (1/4 : ℝ) * future model w a ↔ 0 < future model w a := by
      constructor <;> intro h <;> linarith
    rw [h, future_positive_iff_path]
    rfl

/-- The usual finite vertex-labelled graph presentation of a word language. -/
def HasFiniteLabelledPresentation (L : Set Word) : Prop :=
  ∃ n : ℕ, ∃ E : Fin n → Fin n → Prop, ∃ label : Fin n → Alphabet,
    ∀ w : Word, w ∈ L ↔ ∃ path : List (Fin n), List.Chain' E path ∧ path.map label = w

theorem support_finite_labelled_presentation :
    HasFiniteLabelledPresentation {w : Word | 0 < probability model w} := by
  refine ⟨4, allowedEdge, id, ?_⟩
  intro w
  rw [Set.mem_setOf_eq, positive_probability_iff_path]
  constructor
  · intro h
    exact ⟨w,h,by simp⟩
  · rintro ⟨path,hp,hw⟩
    have heq : path = w := by simpa using hw
    simpa [heq] using hp

theorem counterexample :
    (hankel model).cRank = (3 : Cardinal) ∧
    IsLeast {n : ℕ | ∃ M : HMM n, Realizes M} 4 ∧
    HasFiniteLabelledPresentation {w : Word | 0 < probability model w} :=
  ⟨whole_hankel_rank, minimal_hidden_state_count, support_finite_labelled_presentation⟩

theorem no_realization_with_hankel_rank_states :
    ¬∃ M : HMM (hankel model).cRank.toNat, Realizes M := by
  rintro ⟨M,hM⟩
  have h := any_HMM_needs_four_states M hM
  have hr : (hankel model).cRank.toNat = 3 := by
    rw [whole_hankel_rank]
    norm_num
  omega

#print axioms whole_hankel_rank
#print axioms any_HMM_needs_four_states
#print axioms stationary_left_consistency
#print axioms stationary_right_consistency
#print axioms support_finite_labelled_presentation
#print axioms counterexample
#print axioms no_realization_with_hankel_rank_states

end Conjecture9634
