import Std

namespace FacialBound

/-- The remaining vertices of a walk follow `f`, and the last step returns to `start`. -/
def Closes (f : α → α) (start : α) : α → List α → Prop
  | current, [] => f current = start
  | current, next :: rest => f current = next ∧ Closes f start next rest

/-- A nonempty closed walk following the successor function `f`. -/
def ClosedWalk (f : α → α) : List α → Prop
  | [] => False
  | start :: rest => Closes f start start rest

theorem closedWalk_length_ge_three (f : α → α)
    (h₁ : ∀ a, f a ≠ a) (h₂ : ∀ a, f (f a) ≠ a)
    (xs : List α) (hx : ClosedWalk f xs) : 3 ≤ xs.length := by
  cases xs with
  | nil => exact False.elim hx
  | cons a tail =>
    cases tail with
    | nil => exact False.elim (h₁ a hx)
    | cons b tail =>
      cases tail with
      | nil =>
        have h : f a = b ∧ f b = a := hx
        exact False.elim (h₂ a (by rw [h.1, h.2]))
      | cons c tail => simp only [List.length_cons]; omega

theorem three_mul_length_le_flatten_length (faces : List (List α))
    (h : ∀ xs ∈ faces, 3 ≤ xs.length) :
    3 * faces.length ≤ faces.flatten.length := by
  induction faces with
  | nil => simp
  | cons xs rest ih =>
    have hx := h xs (by simp)
    have hr := ih (by intro ys hy; exact h ys (by simp [hy]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- A partition of all darts into nonempty closed successor walks. -/
structure Decomposition (f : Fin n → Fin n) where
  faces : List (List (Fin n))
  closed : ∀ xs ∈ faces, ClosedWalk f xs
  partition : faces.flatten.Perm (List.finRange n)

theorem decomposition_bound (f : Fin n → Fin n)
    (h₁ : ∀ a, f a ≠ a) (h₂ : ∀ a, f (f a) ≠ a)
    (D : Decomposition f) : 3 * D.faces.length ≤ n := by
  have h := three_mul_length_le_flatten_length D.faces
    (by intro xs hx; exact closedWalk_length_ge_three f h₁ h₂ xs (D.closed xs hx))
  have hlen := D.partition.length_eq
  rw [hlen, List.length_finRange] at h
  exact h

theorem twenty_dart_bound (f : Fin 20 → Fin 20)
    (h₁ : ∀ a, f a ≠ a) (h₂ : ∀ a, f (f a) ≠ a)
    (D : Decomposition f) : D.faces.length ≤ 6 := by
  have := decomposition_bound f h₁ h₂ D
  omega

end FacialBound
