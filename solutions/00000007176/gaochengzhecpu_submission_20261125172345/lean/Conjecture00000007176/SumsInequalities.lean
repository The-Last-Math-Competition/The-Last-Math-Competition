/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Generic finite summation, real & complex Lagrange identities, Cauchy-Schwarz with
equality rigidity, saturation of finite sums, and Muirhead power-sum inequalities
in Core Lean 4.19.0.
-/
import Conjecture00000007176.Algebra

namespace Conjecture00000007176

/-! ### Generic Finite Summation over `List α` -/

/-- Sum of `f` over a finite list `l : List α` in any `CommRing R`. -/
def sumList {α : Type u} {R : Type v} [CommRing R] : List α → (α → R) → R
  | [], _ => 0
  | a :: l, f => f a + sumList l f

section SumListRing

variable {α : Type u} {β : Type w} {R : Type v} [CommRing R]

@[simp] theorem sumList_nil (f : α → R) : sumList [] f = 0 := rfl
@[simp] theorem sumList_cons (a : α) (l : List α) (f : α → R) :
    sumList (a :: l) f = f a + sumList l f := rfl

theorem sumList_congr {l : List α} {f g : α → R} (h : ∀ a, a ∈ l → f a = g a) :
    sumList l f = sumList l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [sumList_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem sumList_append (l₁ l₂ : List α) (f : α → R) :
    sumList (l₁ ++ l₂) f = sumList l₁ f + sumList l₂ f := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, sumList_nil]
    exact (zero_add_eq _).symm
  | cons a l₁ ih =>
    simp only [List.cons_append, sumList_cons]
    rw [ih, CommRing.add_assoc]

theorem sumList_map (l : List α) (h : α → β) (f : β → R) :
    sumList (l.map h) f = sumList l (fun a => f (h a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, sumList_cons]
    rw [ih]

theorem sumList_zero (l : List α) : sumList l (fun _ => (0 : R)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih =>
    simp only [sumList_cons]
    rw [ih, zero_add_eq]

theorem sumList_const (l : List α) (c : R) :
    sumList l (fun _ => c) = natCastR l.length * c := by
  induction l with
  | nil =>
    simp only [sumList_nil, List.length_nil, natCastR_zero]
    exact (zero_mul_eq c).symm
  | cons _ l ih =>
    simp only [sumList_cons, List.length_cons]
    rw [ih, natCastR_succ, CommRing.right_distrib, one_mul_eq, CommRing.add_comm]

theorem sumList_add (l : List α) (f g : α → R) :
    sumList l (fun a => f a + g a) = sumList l f + sumList l g := by
  induction l with
  | nil => exact (add_zero_eq 0).symm
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ih, CommRing.add_assoc, CommRing.add_assoc, add_left_comm_eq (g a) (sumList l f)]

theorem sumList_neg (l : List α) (f : α → R) :
    sumList l (fun a => -f a) = -(sumList l f) := by
  induction l with
  | nil => exact neg_zero_eq.symm
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ih, neg_add_distrib]

theorem sumList_sub (l : List α) (f g : α → R) :
    sumList l (fun a => f a - g a) = sumList l f - sumList l g := by
  have h : (fun a => f a - g a) = (fun a => f a + (-g a)) := by
    funext a
    exact CommRing.sub_eq_add_neg (f a) (g a)
  rw [h, sumList_add, sumList_neg, ← CommRing.sub_eq_add_neg]

theorem sumList_mul_left (l : List α) (c : R) (f : α → R) :
    sumList l (fun a => c * f a) = c * sumList l f := by
  induction l with
  | nil => exact (mul_zero_eq c).symm
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ih, CommRing.left_distrib]

theorem sumList_mul_right (l : List α) (f : α → R) (c : R) :
    sumList l (fun a => f a * c) = sumList l f * c := by
  induction l with
  | nil => exact (zero_mul_eq c).symm
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ih, CommRing.right_distrib]

theorem sumList_product (l₁ : List α) (l₂ : List β) (f : α → R) (g : β → R) :
    sumList l₁ f * sumList l₂ g =
      sumList l₁ (fun a => sumList l₂ (fun b => f a * g b)) := by
  calc
    sumList l₁ f * sumList l₂ g = sumList l₁ (fun a => f a * sumList l₂ g) :=
      (sumList_mul_right l₁ f (sumList l₂ g)).symm
    _ = sumList l₁ (fun a => sumList l₂ (fun b => f a * g b)) := by
      apply sumList_congr
      intro a _
      exact (sumList_mul_left l₂ (f a) g).symm

theorem sumList_comm (l₁ : List α) (l₂ : List β) (h : α → β → R) :
    sumList l₁ (fun a => sumList l₂ (fun b => h a b)) =
      sumList l₂ (fun b => sumList l₁ (fun a => h a b)) := by
  induction l₁ with
  | nil =>
    simp only [sumList_nil]
    exact (sumList_zero l₂).symm
  | cons a l₁ ih =>
    simp only [sumList_cons]
    rw [ih, ← sumList_add]

theorem ofReal_sumList (l : List α) (f : α → R) :
    ComplexOver.ofReal (sumList l f) = sumList l (fun a => ComplexOver.ofReal (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ComplexOver.ofReal_add, ih]

theorem conj_sumList (l : List α) (f : α → ComplexOver R) :
    ComplexOver.conj (sumList l f) = sumList l (fun a => ComplexOver.conj (f a)) := by
  induction l with
  | nil =>
    apply ComplexOver.ext
    · rfl
    · exact neg_zero_eq
  | cons a l ih =>
    simp only [sumList_cons]
    rw [ComplexOver.conj_add, ih]

theorem re_sumList (l : List α) (f : α → ComplexOver R) :
    (sumList l f).re = sumList l (fun a => (f a).re) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [sumList_cons, ComplexOver.add_re]
    rw [ih]

end SumListRing

/-! ### Order, Saturation, and Maximum Attainment on Finite Lists -/

section SumListOrder

variable {α : Type u} {R : Type v} [OrderedDomain R]

theorem sumList_nonneg {l : List α} {f : α → R} (h : ∀ a, a ∈ l → leR 0 (f a)) :
    leR 0 (sumList l f) := by
  induction l with
  | nil => exact leR_refl 0
  | cons a l ih =>
    simp only [sumList_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have hsum := add_leR_add h1 h2
    rw [zero_add_eq] at hsum
    exact hsum

theorem sumList_eq_zero_iff_of_nonneg {l : List α} {f : α → R}
    (h : ∀ a, a ∈ l → leR 0 (f a)) :
    sumList l f = 0 ↔ ∀ a, a ∈ l → f a = 0 := by
  induction l with
  | nil =>
    constructor
    · intro _ a ha; cases ha
    · intro _; rfl
  | cons a l ih =>
    simp only [sumList_cons]
    have ha := h a List.mem_cons_self
    have hl : ∀ x, x ∈ l → leR 0 (f x) := fun x hx => h x (List.mem_cons_of_mem a hx)
    constructor
    · intro hsum
      have ⟨ha0, hl0⟩ := eq_zero_of_add_nonneg_eq_zero ha (sumList_nonneg hl) hsum
      have hall := (ih hl).mp hl0
      intro x hx
      cases List.mem_cons.mp hx with
      | inl hxa => rw [hxa]; exact ha0
      | inr hxl => exact hall x hxl
    · intro hall
      rw [hall a List.mem_cons_self,
          (ih hl).mpr (fun x hx => hall x (List.mem_cons_of_mem a hx)), add_zero_eq]

theorem sumList_leR {l : List α} {f g : α → R} (h : ∀ a, a ∈ l → leR (f a) (g a)) :
    leR (sumList l f) (sumList l g) := by
  unfold leR
  rw [nonneg_iff_leR, ← sumList_sub]
  apply sumList_nonneg
  intro a ha
  have hle := h a ha
  unfold leR at hle ⊢
  rw [sub_zero_eq]
  exact hle

/-- Saturation lemma: if `f a ≤ g a` for every `a ∈ l` and the sums match, then `f a = g a`
    for every `a ∈ l`. -/
theorem eq_of_sumList_eq_of_leR {l : List α} {f g : α → R}
    (hle : ∀ a, a ∈ l → leR (f a) (g a)) (heq : sumList l f = sumList l g) :
    ∀ a, a ∈ l → f a = g a := by
  have hnn : ∀ a, a ∈ l → leR 0 (g a - f a) := by
    intro a ha
    have h1 := hle a ha
    unfold leR at h1 ⊢
    rw [sub_zero_eq]
    exact h1
  have hsum0 : sumList l (fun a => g a - f a) = 0 := by
    rw [sumList_sub, heq, sub_self_eq_zero]
  have hall := (sumList_eq_zero_iff_of_nonneg hnn).mp hsum0
  intro a ha
  exact (sub_eq_zero_iff.mp (hall a ha)).symm

theorem sumList_absR_leR (l : List α) (f : α → R) :
    leR (absR (sumList l f)) (sumList l (fun a => absR (f a))) := by
  induction l with
  | nil =>
    simp only [sumList_nil]
    rw [absR_of_nonneg (leR_refl 0)]
    exact leR_refl 0
  | cons a l ih =>
    simp only [sumList_cons]
    exact leR_trans (absR_add_leR (f a) (sumList l f))
      (add_leR_add (leR_refl (absR (f a))) ih)

/-- Every non-empty list attains a maximum of `f : α → R`. -/
theorem exists_max_mem_list : ∀ {l : List α}, l ≠ [] → (f : α → R) →
    ∃ a₀, a₀ ∈ l ∧ ∀ a, a ∈ l → leR (f a) (f a₀)
  | [], hne, _ => False.elim (hne rfl)
  | [a], _, f => ⟨a, List.mem_cons_self, fun x hx => by
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact leR_refl _
      | inr h => cases h⟩
  | a :: b :: l, _, f => by
    have ⟨m, hm_mem, hm_max⟩ := exists_max_mem_list (l := b :: l) (by intro h; cases h) f
    cases leR_total (f m) (f a) with
    | inl hma =>
      refine ⟨a, List.mem_cons_self, fun x hx => ?_⟩
      cases List.mem_cons.mp hx with
      | inl hxa => rw [hxa]; exact leR_refl _
      | inr hxl => exact leR_trans (hm_max x hxl) hma
    | inr ham =>
      refine ⟨m, List.mem_cons_of_mem a hm_mem, fun x hx => ?_⟩
      cases List.mem_cons.mp hx with
      | inl hxa => rw [hxa]; exact ham
      | inr hxl => exact hm_max x hxl

/-! ### Real Lagrange Identity & Polynomial Cauchy-Schwarz with Rigidity -/

/-- Real Lagrange identity over any `CommRing`:
    `∑_{a,b} (f(a)g(b) - f(b)g(a))^2 = 2 * ((∑ f^2)(∑ g^2) - (∑ f g)^2)`. -/
theorem real_lagrange_identity (l : List α) (f g : α → R) :
    sumList l (fun a => sumList l (fun b =>
      (f a * g b - f b * g a) * (f a * g b - f b * g a))) =
    natCastR 2 *
      (sumList l (fun a => f a * f a) * sumList l (fun b => g b * g b) -
       sumList l (fun a => f a * g a) * sumList l (fun b => f b * g b)) := by
  let Sff := sumList l (fun a => f a * f a)
  let Sgg := sumList l (fun b => g b * g b)
  let Sfg := sumList l (fun a => f a * g a)
  have hexpand : ∀ a b,
      (f a * g b - f b * g a) * (f a * g b - f b * g a) =
      ((f a * f a) * (g b * g b) + (f b * f b) * (g a * g a)) -
      ((f a * g a) * (f b * g b) + (f a * g a) * (f b * g b)) := by
    intro a b
    rw [sub_sq_eq]
    have h1 : (f a * g b) * (f a * g b) = (f a * f a) * (g b * g b) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq (g b) (f a) (g b), ← CommRing.mul_assoc]
    have h2 : (f b * g a) * (f b * g a) = (f b * f b) * (g a * g a) := by
      rw [CommRing.mul_assoc, mul_left_comm_eq (g a) (f b) (g a), ← CommRing.mul_assoc]
    have h3 : (f a * g b) * (f b * g a) = (f a * g a) * (f b * g b) := by
      rw [CommRing.mul_assoc, CommRing.mul_comm (g b) (f b * g a),
          CommRing.mul_assoc (f b) (g a) (g b), mul_left_comm_eq (f a) (f b) (g a * g b),
          CommRing.mul_comm (f b) (f a * (g a * g b)),
          ← CommRing.mul_assoc (f a) (g a) (g b), CommRing.mul_assoc (f a * g a),
          CommRing.mul_comm (g b) (f b)]
    rw [h1, h2, h3]
  have hcongr : sumList l (fun a => sumList l (fun b =>
      (f a * g b - f b * g a) * (f a * g b - f b * g a))) =
    sumList l (fun a =>
      sumList l (fun b => (f a * f a) * (g b * g b) + (f b * f b) * (g a * g a)) -
      sumList l (fun b => (f a * g a) * (f b * g b) + (f a * g a) * (f b * g b))) := by
    apply sumList_congr; intro a _
    rw [← sumList_sub]
    apply sumList_congr; intro b _
    exact hexpand a b
  rw [hcongr, sumList_sub]
  have hA : sumList l (fun a =>
      sumList l (fun b => (f a * f a) * (g b * g b) + (f b * f b) * (g a * g a))) =
      Sff * Sgg + Sff * Sgg := by
    have hA1 : sumList l (fun a =>
        sumList l (fun b => (f a * f a) * (g b * g b) + (f b * f b) * (g a * g a))) =
        sumList l (fun a => sumList l (fun b => (f a * f a) * (g b * g b))) +
        sumList l (fun a => sumList l (fun b => (f b * f b) * (g a * g a))) := by
      rw [← sumList_add]
      apply sumList_congr; intro a _
      exact sumList_add l _ _
    rw [hA1, ← sumList_product l l (fun a => f a * f a) (fun b => g b * g b)]
    have hA2 : sumList l (fun a => sumList l (fun b => (f b * f b) * (g a * g a))) =
        Sff * Sgg := by
      rw [sumList_comm, ← sumList_product l l (fun b => f b * f b) (fun a => g a * g a)]
    rw [hA2]
  have hB : sumList l (fun a =>
      sumList l (fun b => (f a * g a) * (f b * g b) + (f a * g a) * (f b * g b))) =
      Sfg * Sfg + Sfg * Sfg := by
    have hB1 : sumList l (fun a =>
        sumList l (fun b => (f a * g a) * (f b * g b) + (f a * g a) * (f b * g b))) =
        sumList l (fun a => sumList l (fun b => (f a * g a) * (f b * g b))) +
        sumList l (fun a => sumList l (fun b => (f a * g a) * (f b * g b))) := by
      rw [← sumList_add]
      apply sumList_congr; intro a _
      exact sumList_add l _ _
    rw [hB1, ← sumList_product l l (fun a => f a * g a) (fun b => f b * g b)]
  rw [hA, hB, natCastR_two, CommRing.right_distrib, one_mul_eq]
  change (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) =
         (Sff * Sgg - Sfg * Sfg) + (Sff * Sgg - Sfg * Sfg)
  rw [CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, neg_add_distrib]
  calc
    (Sff * Sgg + Sff * Sgg) + (-(Sfg * Sfg) + -(Sfg * Sfg)) =
        Sff * Sgg + (Sff * Sgg + (-(Sfg * Sfg) + -(Sfg * Sfg))) := CommRing.add_assoc _ _ _
    _ = Sff * Sgg + (-(Sfg * Sfg) + (Sff * Sgg + -(Sfg * Sfg))) := by
        rw [add_left_comm_eq (Sff * Sgg) (-(Sfg * Sfg))]
    _ = (Sff * Sgg + -(Sfg * Sfg)) + (Sff * Sgg + -(Sfg * Sfg)) := by
        rw [← CommRing.add_assoc]

private theorem nonneg_of_two_mul_nonneg {x : R} (h : leR 0 (natCastR 2 * x)) : leR 0 x := by
  have h0 : leR (natCastR 2 * 0) (natCastR 2 * x) := by
    rw [mul_zero_eq]
    exact h
  exact leR_of_mul_leR_mul_pos_left (two_pos (R := R)) h0

/-- Polynomial Cauchy-Schwarz inequality `(∑ f g)^2 ≤ (∑ f^2)(∑ g^2)`. -/
theorem cauchy_schwarz_list (l : List α) (f g : α → R) :
    leR (sumList l (fun a => f a * g a) * sumList l (fun b => f b * g b))
        (sumList l (fun a => f a * f a) * sumList l (fun b => g b * g b)) := by
  have hlag := real_lagrange_identity l f g
  have hnn : leR 0 (sumList l (fun a => sumList l (fun b =>
      (f a * g b - f b * g a) * (f a * g b - f b * g a)))) := by
    apply sumList_nonneg; intro a _
    apply sumList_nonneg; intro b _
    exact sq_nonneg _
  rw [hlag] at hnn
  have h2 := nonneg_of_two_mul_nonneg hnn
  unfold leR
  rw [← nonneg_iff_leR] at h2
  exact h2

/-- Equality rigidity in Cauchy-Schwarz: if `(∑ f g)^2 = (∑ f^2)(∑ g^2)`, then
    `f a * g b = f b * g a` for all `a, b ∈ l`, and `(∑ g^2) * f a = (∑ f g) * g a`. -/
theorem cauchy_schwarz_eq_cross {l : List α} {f g : α → R}
    (heq : sumList l (fun a => f a * g a) * sumList l (fun b => f b * g b) =
           sumList l (fun a => f a * f a) * sumList l (fun b => g b * g b)) :
    (∀ a, a ∈ l → ∀ b, b ∈ l → f a * g b = f b * g a) ∧
    (∀ a, a ∈ l →
      sumList l (fun b => g b * g b) * f a = sumList l (fun b => f b * g b) * g a) := by
  have hlag := real_lagrange_identity l f g
  rw [← heq, sub_self_eq_zero, mul_zero_eq] at hlag
  have houter_nn : ∀ a, a ∈ l → leR 0 (sumList l (fun b =>
      (f a * g b - f b * g a) * (f a * g b - f b * g a))) := by
    intro a _
    apply sumList_nonneg; intro b _; exact sq_nonneg _
  have houter0 := (sumList_eq_zero_iff_of_nonneg houter_nn).mp hlag
  have hcross : ∀ a, a ∈ l → ∀ b, b ∈ l → f a * g b = f b * g a := by
    intro a ha b hb
    have hinner0 := (sumList_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)).mp (houter0 a ha) b hb
    exact sub_eq_zero_iff.mp ((sq_eq_zero_iff _).mp hinner0)
  refine ⟨hcross, ?_⟩
  intro a ha
  calc
    sumList l (fun b => g b * g b) * f a =
        sumList l (fun b => (f a * g b) * g b) := by
      rw [← sumList_mul_right]
      apply sumList_congr; intro b _
      rw [CommRing.mul_comm (g b * g b) (f a), CommRing.mul_assoc]
    _ = sumList l (fun b => (f b * g b) * g a) := by
      apply sumList_congr; intro b hb
      rw [hcross a ha b hb, CommRing.mul_assoc, CommRing.mul_comm (g a) (g b),
          ← CommRing.mul_assoc]
    _ = sumList l (fun b => f b * g b) * g a := sumList_mul_right l _ (g a)

/-! ### Complex Lagrange Identity & Modulus-Squared Sum Bound -/

/-- Complex Lagrange identity over `ComplexOver R`:
    `∑_{a,b} |w(a) - w(b)|^2 = 2 * (N * ∑ |w|^2 - |∑ w|^2)`. -/
theorem complex_lagrange_identity (l : List α) (w : α → ComplexOver R) :
    sumList l (fun a => sumList l (fun b => ComplexOver.normSq (w a - w b))) =
    natCastR 2 *
      (natCastR l.length * sumList l (fun a => ComplexOver.normSq (w a)) -
       ComplexOver.normSq (sumList l w)) := by
  let N := (natCastR l.length : R)
  let Qw := sumList l (fun a => ComplexOver.normSq (w a))
  let Sw := sumList l w
  have hcongr : sumList l (fun a => sumList l (fun b => ComplexOver.normSq (w a - w b))) =
      sumList l (fun a =>
        sumList l (fun b => ComplexOver.normSq (w a) + ComplexOver.normSq (w b)) -
        sumList l (fun b => (w a * ComplexOver.conj (w b)).re + (w a * ComplexOver.conj (w b)).re)) := by
    apply sumList_congr; intro a _
    rw [← sumList_sub]
    apply sumList_congr; intro b _
    exact ComplexOver.normSq_sub_eq (w a) (w b)
  rw [hcongr, sumList_sub]
  have hA : sumList l (fun a =>
      sumList l (fun b => ComplexOver.normSq (w a) + ComplexOver.normSq (w b))) =
      N * Qw + N * Qw := by
    have hA1 : sumList l (fun a =>
        sumList l (fun b => ComplexOver.normSq (w a) + ComplexOver.normSq (w b))) =
        sumList l (fun a => sumList l (fun _ => ComplexOver.normSq (w a))) +
        sumList l (fun _ => Qw) := by
      rw [← sumList_add]
      apply sumList_congr; intro a _
      exact sumList_add l _ _
    rw [hA1, sumList_const l Qw]
    have hA2 : sumList l (fun a => sumList l (fun _ => ComplexOver.normSq (w a))) = N * Qw := by
      calc
        sumList l (fun a => sumList l (fun _ => ComplexOver.normSq (w a))) =
            sumList l (fun a => N * ComplexOver.normSq (w a)) := by
          apply sumList_congr; intro a _
          exact sumList_const l (ComplexOver.normSq (w a))
        _ = N * Qw := sumList_mul_left l N _
    rw [hA2]
  have hCross : sumList l (fun a => sumList l (fun b => (w a * ComplexOver.conj (w b)).re)) =
      ComplexOver.normSq Sw := by
    have h1 : sumList l (fun a => sumList l (fun b => (w a * ComplexOver.conj (w b)).re)) =
        (sumList l (fun a => sumList l (fun b => w a * ComplexOver.conj (w b)))).re := by
      rw [re_sumList]
      apply sumList_congr; intro a _
      exact (re_sumList l _).symm
    rw [h1, ← sumList_product l l w (fun b => ComplexOver.conj (w b)),
        ← conj_sumList l w, ComplexOver.mul_conj_eq]
    rfl
  have hB : sumList l (fun a =>
      sumList l (fun b => (w a * ComplexOver.conj (w b)).re + (w a * ComplexOver.conj (w b)).re)) =
      ComplexOver.normSq Sw + ComplexOver.normSq Sw := by
    have hB1 : sumList l (fun a =>
        sumList l (fun b => (w a * ComplexOver.conj (w b)).re + (w a * ComplexOver.conj (w b)).re)) =
        sumList l (fun a => sumList l (fun b => (w a * ComplexOver.conj (w b)).re)) +
        sumList l (fun a => sumList l (fun b => (w a * ComplexOver.conj (w b)).re)) := by
      rw [← sumList_add]
      apply sumList_congr; intro a _
      exact sumList_add l _ _
    rw [hB1, hCross]
  rw [hA, hB, natCastR_two, CommRing.right_distrib, one_mul_eq]
  change (N * Qw + N * Qw) - (ComplexOver.normSq Sw + ComplexOver.normSq Sw) =
         (N * Qw - ComplexOver.normSq Sw) + (N * Qw - ComplexOver.normSq Sw)
  rw [CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, neg_add_distrib]
  calc
    (N * Qw + N * Qw) + (-(ComplexOver.normSq Sw) + -(ComplexOver.normSq Sw)) =
        N * Qw + (N * Qw + (-(ComplexOver.normSq Sw) + -(ComplexOver.normSq Sw))) :=
      CommRing.add_assoc _ _ _
    _ = N * Qw + (-(ComplexOver.normSq Sw) + (N * Qw + -(ComplexOver.normSq Sw))) := by
      rw [add_left_comm_eq (N * Qw) (-(ComplexOver.normSq Sw))]
    _ = (N * Qw + -(ComplexOver.normSq Sw)) + (N * Qw + -(ComplexOver.normSq Sw)) := by
      rw [← CommRing.add_assoc]

/-- Complex Cauchy-Schwarz sum bound `|∑_{a∈l} w(a)|^2 ≤ length(l) * ∑_{a∈l} |w(a)|^2`. -/
theorem complex_normSq_sum_le (l : List α) (w : α → ComplexOver R) :
    leR (ComplexOver.normSq (sumList l w))
        (natCastR l.length * sumList l (fun a => ComplexOver.normSq (w a))) := by
  have hlag := complex_lagrange_identity l w
  have hnn : leR 0 (sumList l (fun a => sumList l (fun b => ComplexOver.normSq (w a - w b)))) := by
    apply sumList_nonneg; intro a _
    apply sumList_nonneg; intro b _
    exact ComplexOver.normSq_nonneg _
  rw [hlag] at hnn
  have h2 := nonneg_of_two_mul_nonneg hnn
  unfold leR
  rw [← nonneg_iff_leR] at h2
  exact h2

/-- Equality rigidity in the complex sum bound: if `|∑ w|^2 = length(l) * ∑ |w|^2`, then
    all terms `w(a)` are pairwise equal, hence `length(l) * w(a) = ∑ w`. -/
theorem complex_normSq_sum_eq_const {l : List α} {w : α → ComplexOver R}
    (heq : ComplexOver.normSq (sumList l w) =
           natCastR l.length * sumList l (fun a => ComplexOver.normSq (w a))) :
    (∀ a, a ∈ l → ∀ b, b ∈ l → w a = w b) ∧
    (∀ a, a ∈ l → natCastR l.length * w a = sumList l w) := by
  have hlag := complex_lagrange_identity l w
  rw [← heq, sub_self_eq_zero, mul_zero_eq] at hlag
  have houter_nn : ∀ a, a ∈ l → leR 0 (sumList l (fun b => ComplexOver.normSq (w a - w b))) := by
    intro a _
    apply sumList_nonneg; intro b _; exact ComplexOver.normSq_nonneg _
  have houter0 := (sumList_eq_zero_iff_of_nonneg houter_nn).mp hlag
  have hpairs : ∀ a, a ∈ l → ∀ b, b ∈ l → w a = w b := by
    intro a ha b hb
    have hinner0 := (sumList_eq_zero_iff_of_nonneg (fun c _ => ComplexOver.normSq_nonneg _)).mp
      (houter0 a ha) b hb
    exact sub_eq_zero_iff.mp ((ComplexOver.normSq_eq_zero_iff _).mp hinner0)
  refine ⟨hpairs, ?_⟩
  intro a ha
  calc
    natCastR l.length * w a = sumList l (fun _ => w a) := (sumList_const l (w a)).symm
    _ = sumList l w := by
      apply sumList_congr
      intro b hb
      exact hpairs a ha b hb

/-! ### Muirhead / Power-Sum Inequality `(∑ r^2)^m ≤ N^{m-2} (∑ r^m)^2` -/

/-- Pairwise monotone product `(x - y) * (x^k - y^k) ≥ 0` for `x, y ≥ 0`. -/
theorem diff_mul_rpow_diff_nonneg {x y : R} (hx : leR 0 x) (hy : leR 0 y) (k : Nat) :
    leR 0 ((x - y) * (rpow x k - rpow y k)) := by
  cases leR_total y x with
  | inl hyx =>
    have h1 : leR 0 (x - y) := by
      unfold leR at hyx ⊢; rw [sub_zero_eq]; exact hyx
    have hpow : leR (rpow y k) (rpow x k) := rpow_leR_rpow_of_nonneg hy hyx k
    have h2 : leR 0 (rpow x k - rpow y k) := by
      unfold leR at hpow ⊢; rw [sub_zero_eq]; exact hpow
    exact mul_nonneg_leR h1 h2
  | inr hxy =>
    have h1 : leR 0 (y - x) := by
      unfold leR at hxy ⊢; rw [sub_zero_eq]; exact hxy
    have hpow : leR (rpow x k) (rpow y k) := rpow_leR_rpow_of_nonneg hx hxy k
    have h2 : leR 0 (rpow y k - rpow x k) := by
      unfold leR at hpow ⊢; rw [sub_zero_eq]; exact hpow
    have heq : (x - y) * (rpow x k - rpow y k) = (y - x) * (rpow y k - rpow x k) := by
      rw [← neg_sub_eq y x, ← neg_sub_eq (rpow y k) (rpow x k), neg_mul_neg]
    rw [heq]
    exact mul_nonneg_leR h1 h2

/-- Fundamental power-sum shift inequality: for `r(a) ≥ 0`, let `P(k) = ∑_{a∈l} r(a)^k`.
    Then `P(q + δ + 1) * P(q + 1) ≤ P(q + δ + 2) * P(q)` for all `q, δ : Nat`. -/
theorem powSum_shift_le {l : List α} {r : α → R} (hr : ∀ a, a ∈ l → leR 0 (r a))
    (q δ : Nat) :
    leR (sumList l (fun a => rpow (r a) (q + δ + 1)) * sumList l (fun b => rpow (r b) (q + 1)))
        (sumList l (fun a => rpow (r a) (q + δ + 2)) * sumList l (fun b => rpow (r b) q)) := by
  let P := fun k => sumList l (fun a => rpow (r a) k)
  have hterm : ∀ x y : R,
      (rpow x q * rpow y q) * ((x - y) * (rpow x (δ + 1) - rpow y (δ + 1))) =
      (rpow x (q + δ + 2) * rpow y q + rpow x q * rpow y (q + δ + 2)) -
      (rpow x (q + δ + 1) * rpow y (q + 1) + rpow x (q + 1) * rpow y (q + δ + 1)) := by
    intro x y
    have hexp1 : (x - y) * (rpow x (δ + 1) - rpow y (δ + 1)) =
        (x * rpow x (δ + 1) + y * rpow y (δ + 1)) -
        (x * rpow y (δ + 1) + y * rpow x (δ + 1)) := by
      rw [mul_sub_distrib, sub_mul_distrib, sub_mul_distrib,
          CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg,
          CommRing.sub_eq_add_neg, neg_add_distrib, neg_add_distrib, neg_neg_eq]
      calc
        (x * rpow x (δ + 1) + -(y * rpow x (δ + 1))) + (-(x * rpow y (δ + 1)) + y * rpow y (δ + 1)) =
            x * rpow x (δ + 1) + (-(y * rpow x (δ + 1)) + (y * rpow y (δ + 1) + -(x * rpow y (δ + 1)))) := by
          rw [CommRing.add_comm (-(x * rpow y (δ + 1))), CommRing.add_assoc]
        _ = x * rpow x (δ + 1) + (y * rpow y (δ + 1) + (-(y * rpow x (δ + 1)) + -(x * rpow y (δ + 1)))) := by
          rw [add_left_comm_eq (-(y * rpow x (δ + 1))) (y * rpow y (δ + 1))]
        _ = (x * rpow x (δ + 1) + y * rpow y (δ + 1)) + (-(x * rpow y (δ + 1)) + -(y * rpow x (δ + 1))) := by
          rw [CommRing.add_comm (-(y * rpow x (δ + 1))), ← CommRing.add_assoc]
    rw [hexp1, mul_sub_distrib, CommRing.left_distrib, CommRing.left_distrib]
    have ht1 : (rpow x q * rpow y q) * (x * rpow x (δ + 1)) = rpow x (q + δ + 2) * rpow y q := by
      calc
        (rpow x q * rpow y q) * (x * rpow x (δ + 1)) =
            (rpow x q * (rpow x (δ + 1) * x)) * rpow y q := by
          rw [CommRing.mul_comm x (rpow x (δ + 1)), CommRing.mul_assoc (rpow x q),
              CommRing.mul_comm (rpow y q), ← CommRing.mul_assoc]
        _ = rpow x (q + δ + 2) * rpow y q := by
          rw [← rpow_succ, ← rpow_add]
          have hq : q + (δ + 2) = q + δ + 2 := by omega
          rw [hq]
    have ht2 : (rpow x q * rpow y q) * (y * rpow y (δ + 1)) = rpow x q * rpow y (q + δ + 2) := by
      calc
        (rpow x q * rpow y q) * (y * rpow y (δ + 1)) =
            rpow x q * (rpow y q * (rpow y (δ + 1) * y)) := by
          rw [CommRing.mul_comm y (rpow y (δ + 1)), CommRing.mul_assoc]
        _ = rpow x q * rpow y (q + δ + 2) := by
          rw [← rpow_succ, ← rpow_add]
          have hq : q + (δ + 2) = q + δ + 2 := by omega
          rw [hq]
    have ht3 : (rpow x q * rpow y q) * (x * rpow y (δ + 1)) =
        rpow x (q + 1) * rpow y (q + δ + 1) := by
      calc
        (rpow x q * rpow y q) * (x * rpow y (δ + 1)) =
            (rpow x q * x) * (rpow y q * rpow y (δ + 1)) := by
          rw [CommRing.mul_assoc, mul_left_comm_eq (rpow y q) x, ← CommRing.mul_assoc]
        _ = rpow x (q + 1) * rpow y (q + δ + 1) := by
          rw [← rpow_succ, ← rpow_add]
          have hq : q + (δ + 1) = q + δ + 1 := by omega
          rw [hq]
    have ht4 : (rpow x q * rpow y q) * (y * rpow x (δ + 1)) =
        rpow x (q + δ + 1) * rpow y (q + 1) := by
      calc
        (rpow x q * rpow y q) * (y * rpow x (δ + 1)) =
            (rpow x q * rpow x (δ + 1)) * (rpow y q * y) := by
          rw [CommRing.mul_comm y (rpow x (δ + 1)), CommRing.mul_assoc,
              mul_left_comm_eq (rpow y q) (rpow x (δ + 1)), ← CommRing.mul_assoc]
        _ = rpow x (q + δ + 1) * rpow y (q + 1) := by
          rw [← rpow_succ, ← rpow_add]
          have hq : q + (δ + 1) = q + δ + 1 := by omega
          rw [hq]
    rw [ht1, ht2, ht3, ht4,
        CommRing.add_comm (rpow x (q + 1) * rpow y (q + δ + 1))]
  have hsum : sumList l (fun a => sumList l (fun b =>
      (rpow (r a) q * rpow (r b) q) *
      ((r a - r b) * (rpow (r a) (δ + 1) - rpow (r b) (δ + 1))))) =
      natCastR 2 * (P (q + δ + 2) * P q - P (q + δ + 1) * P (q + 1)) := by
    have hc : sumList l (fun a => sumList l (fun b =>
        (rpow (r a) q * rpow (r b) q) *
        ((r a - r b) * (rpow (r a) (δ + 1) - rpow (r b) (δ + 1))))) =
      sumList l (fun a =>
        sumList l (fun b => rpow (r a) (q + δ + 2) * rpow (r b) q + rpow (r a) q * rpow (r b) (q + δ + 2)) -
        sumList l (fun b => rpow (r a) (q + δ + 1) * rpow (r b) (q + 1) + rpow (r a) (q + 1) * rpow (r b) (q + δ + 1))) := by
      apply sumList_congr; intro a _
      rw [← sumList_sub]
      apply sumList_congr; intro b _
      exact hterm (r a) (r b)
    rw [hc, sumList_sub]
    have hA : sumList l (fun a =>
        sumList l (fun b => rpow (r a) (q + δ + 2) * rpow (r b) q + rpow (r a) q * rpow (r b) (q + δ + 2))) =
        P (q + δ + 2) * P q + P (q + δ + 2) * P q := by
      have hA1 : sumList l (fun a =>
          sumList l (fun b => rpow (r a) (q + δ + 2) * rpow (r b) q + rpow (r a) q * rpow (r b) (q + δ + 2))) =
          sumList l (fun a => sumList l (fun b => rpow (r a) (q + δ + 2) * rpow (r b) q)) +
          sumList l (fun a => sumList l (fun b => rpow (r a) q * rpow (r b) (q + δ + 2))) := by
        rw [← sumList_add]; apply sumList_congr; intro a _; exact sumList_add l _ _
      rw [hA1, ← sumList_product]
      have hA2 : sumList l (fun a => sumList l (fun b => rpow (r a) q * rpow (r b) (q + δ + 2))) =
          P (q + δ + 2) * P q := by
        rw [← sumList_product, CommRing.mul_comm]
      rw [hA2]
    have hB : sumList l (fun a =>
        sumList l (fun b => rpow (r a) (q + δ + 1) * rpow (r b) (q + 1) + rpow (r a) (q + 1) * rpow (r b) (q + δ + 1))) =
        P (q + δ + 1) * P (q + 1) + P (q + δ + 1) * P (q + 1) := by
      have hB1 : sumList l (fun a =>
          sumList l (fun b => rpow (r a) (q + δ + 1) * rpow (r b) (q + 1) + rpow (r a) (q + 1) * rpow (r b) (q + δ + 1))) =
          sumList l (fun a => sumList l (fun b => rpow (r a) (q + δ + 1) * rpow (r b) (q + 1))) +
          sumList l (fun a => sumList l (fun b => rpow (r a) (q + 1) * rpow (r b) (q + δ + 1))) := by
        rw [← sumList_add]; apply sumList_congr; intro a _; exact sumList_add l _ _
      rw [hB1, ← sumList_product]
      have hB2 : sumList l (fun a => sumList l (fun b => rpow (r a) (q + 1) * rpow (r b) (q + δ + 1))) =
          P (q + δ + 1) * P (q + 1) := by
        rw [← sumList_product, CommRing.mul_comm]
      rw [hB2]
    rw [hA, hB, natCastR_two, CommRing.right_distrib, one_mul_eq]
    let X := P (q + δ + 2) * P q
    let Y := P (q + δ + 1) * P (q + 1)
    change (X + X) - (Y + Y) = (X - Y) + (X - Y)
    rw [CommRing.sub_eq_add_neg, CommRing.sub_eq_add_neg, neg_add_distrib]
    calc
      (X + X) + (-Y + -Y) = X + (X + (-Y + -Y)) := CommRing.add_assoc _ _ _
      _ = X + (-Y + (X + -Y)) := by rw [add_left_comm_eq X (-Y)]
      _ = (X + -Y) + (X + -Y) := by rw [← CommRing.add_assoc]
  have hnn : leR 0 (sumList l (fun a => sumList l (fun b =>
      (rpow (r a) q * rpow (r b) q) *
      ((r a - r b) * (rpow (r a) (δ + 1) - rpow (r b) (δ + 1)))))) := by
    apply sumList_nonneg; intro a ha
    apply sumList_nonneg; intro b hb
    exact mul_nonneg_leR
      (mul_nonneg_leR (rpow_nonneg (hr a ha) q) (rpow_nonneg (hr b hb) q))
      (diff_mul_rpow_diff_nonneg (hr a ha) (hr b hb) (δ + 1))
  rw [hsum] at hnn
  have h2 := nonneg_of_two_mul_nonneg hnn
  unfold leR
  rw [← nonneg_iff_leR] at h2
  exact h2

/-- Key polynomial `ℓ_2`–`ℓ_m` inequality: for `r(a) ≥ 0` on `l : List α` (`N = l.length`) and
    every `d : Nat` (`m = d + 2 ≥ 2`),
    `(∑_{a∈l} r(a)^2)^{d+2} ≤ N^d * (∑_{a∈l} r(a)^{d+2})^2`. -/
theorem powSum_two_m_le {l : List α} {r : α → R} (hr : ∀ a, a ∈ l → leR 0 (r a)) :
    ∀ d : Nat,
      leR (rpow (sumList l (fun a => rpow (r a) 2)) (d + 2))
          (rpow (natCastR l.length) d *
           (sumList l (fun a => rpow (r a) (d + 2)) *
            sumList l (fun a => rpow (r a) (d + 2))))
  | 0 => by
    simp only [Nat.zero_add, rpow_zero, rpow_two, one_mul_eq]
    exact leR_refl _
  | d + 1 => by
    let P := fun k => sumList l (fun a => rpow (r a) k)
    let N := (natCastR l.length : R)
    have hP_nn : ∀ k, leR 0 (P k) := fun k =>
      sumList_nonneg (fun a ha => rpow_nonneg (hr a ha) k)
    have hP0 : P 0 = N := by
      change sumList l (fun _ => (1 : R)) = N
      rw [sumList_const, mul_one_eq]
    have ih := powSum_two_m_le hr d
    change leR (rpow (P 2) (d + 3)) (rpow N (d + 1) * (P (d + 3) * P (d + 3)))
    have hstep1 : leR (P (d + 2) * P 2) (P (d + 3) * P 1) := by
      have hs := powSum_shift_le hr 1 d
      have e1 : 1 + d + 1 = d + 2 := by omega
      have e2 : 1 + d + 2 = d + 3 := by omega
      rw [e1, e2] at hs
      exact hs
    have hstep2 : leR (P (d + 2) * P 1) (N * P (d + 3)) := by
      have hs := powSum_shift_le hr 0 (d + 1)
      have e1 : 0 + (d + 1) + 1 = d + 2 := by omega
      have e2 : 0 + (d + 1) + 2 = d + 3 := by omega
      have e3 : 0 + 1 = 1 := rfl
      rw [e1, e2, e3] at hs
      change leR (P (d + 2) * P 1) (P (d + 3) * P 0) at hs
      rw [hP0, CommRing.mul_comm (P (d + 3)) N] at hs
      exact hs
    have hcomb : leR ((P (d + 2) * P (d + 2)) * P 2) (N * (P (d + 3) * P (d + 3))) := by
      have hc1 : leR ((P (d + 2) * P (d + 2)) * P 2) (P (d + 2) * (P (d + 3) * P 1)) := by
        rw [CommRing.mul_assoc]
        exact mul_leR_mul_of_nonneg_left (hP_nn _) hstep1
      have hc2 : leR (P (d + 2) * (P (d + 3) * P 1)) (N * (P (d + 3) * P (d + 3))) := by
        rw [mul_left_comm_eq (P (d + 2)) (P (d + 3)),
            mul_left_comm_eq N (P (d + 3))]
        exact mul_leR_mul_of_nonneg_left (hP_nn _) hstep2
      exact leR_trans hc1 hc2
    have hm1 : leR (rpow (P 2) (d + 3)) ((rpow N d * (P (d + 2) * P (d + 2))) * P 2) :=
      mul_leR_mul_of_nonneg_right (hP_nn 2) ih
    have hm2 : leR ((rpow N d * (P (d + 2) * P (d + 2))) * P 2)
        (rpow N (d + 1) * (P (d + 3) * P (d + 3))) := by
      rw [CommRing.mul_assoc (rpow N d), rpow_succ, CommRing.mul_assoc (rpow N d)]
      exact mul_leR_mul_of_nonneg_left (rpow_nonneg (natCastR_nonneg _) d) hcomb
    exact leR_trans hm1 hm2

end SumListOrder

end Conjecture00000007176
