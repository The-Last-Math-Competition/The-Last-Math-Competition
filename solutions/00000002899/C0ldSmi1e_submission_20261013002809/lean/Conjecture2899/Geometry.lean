import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Conjecture2899

abbrev Ambient (F : Type*) (d : ℕ) := Fin d → F

def IsKakeya {F : Type*} [Field F] {d : ℕ}
    (K : Finset (Ambient F d)) : Prop :=
  ∀ v : Ambient F d, v ≠ 0 → ∃ a : Ambient F d,
    ∀ t : F, (fun i => a i + t * v i) ∈ K

theorem line_injective {F : Type*} [Field F] {d : ℕ}
    (a v : Ambient F d) (hv : v ≠ 0) :
    Function.Injective (fun t : F => fun i => a i + t * v i) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  intro s t h
  have hh := congrFun h i
  exact mul_right_cancel₀ hi (add_left_cancel hh)

theorem line_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (a v : Ambient F d) (hv : v ≠ 0) :
    (Finset.univ.image (fun t : F => fun i => a i + t * v i)).card = Fintype.card F := by
  classical
  rw [Finset.card_image_of_injective _ (line_injective a v hv), Finset.card_univ]

noncomputable def family (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Finset (Ambient F (n + 2)) := by
  classical
  exact Finset.univ.filter (fun w => w 0 = 0 ∨ ∃ z : F, w 1 + (w 0)^2 = z^2)

theorem mem_family {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (w : Ambient F (n + 2)) :
    w ∈ family F n ↔ w 0 = 0 ∨ ∃ z : F, w 1 + (w 0)^2 = z^2 := by
  classical
  simp [family]

theorem family_isKakeya (F : Type*) [Field F] [Fintype F]
    (htwo : (2 : F) ≠ 0) (n : ℕ) : IsKakeya (family F n) := by
  intro v _hv
  by_cases h0 : v 0 = 0
  · refine ⟨0, ?_⟩
    intro t
    exact (mem_family _).2 (Or.inl (by simp [h0]))
  · let b : F := v 1 / (2 * v 0)
    let a : Ambient F (n + 2) := fun i => if i = 1 then b^2 else 0
    refine ⟨a, ?_⟩
    intro t
    apply (mem_family _).2
    right
    refine ⟨b + t * v 0, ?_⟩
    have hb : 2 * b * v 0 = v 1 := by
      dsimp [b]
      field_simp
      ring
    have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
    simp only [a, h01, if_false, if_true, zero_add]
    calc
      b^2 + t * v 1 + (t * v 0)^2 = b^2 + t * (2*b*v 0) + (t*v 0)^2 := by rw [hb]
      _ = (b + t * v 0)^2 := by ring

end Conjecture2899
