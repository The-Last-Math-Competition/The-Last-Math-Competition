import Std
open Lean.Grind
namespace TLMC8207
abbrev M := Fin 6
/-- The actual product of the six-element chain semilattice. -/
def meet (a b : M) : M :=
  ⟨min a.val b.val, Nat.lt_of_le_of_lt (Nat.min_le_left _ _) a.isLt⟩
def unit : M := 5

theorem meet_comm (a b : M) : meet a b = meet b a := by
  apply Fin.ext; simp [meet, Nat.min_comm]
theorem meet_assoc (a b c : M) : meet (meet a b) c = meet a (meet b c) := by
  apply Fin.ext; simp [meet, Nat.min_assoc]
theorem meet_self (a : M) : meet a a = a := by apply Fin.ext; simp [meet]
theorem meet_unit (a : M) : meet a unit = a := by
  apply Fin.ext; simp [meet, unit]; omega
theorem unit_meet (a : M) : meet unit a = a := by rw [meet_comm, meet_unit]
theorem zero_meet (a : M) : meet 0 a = 0 := by apply Fin.ext; simp [meet]
theorem meet_of_le {a b : M} (h : a.val ≤ b.val) : meet a b = a := by
  apply Fin.ext; simp [meet, Nat.min_eq_left h]
/-- In an inverse monoid an element has a unique inverse in this sense. -/
def IsInverse (a b : M) : Prop := meet (meet a b) a = a ∧ meet (meet b a) b = b
theorem unique_inverse (a : M) : IsInverse a a ∧ ∀ b, IsInverse a b → b = a := by
  constructor
  · simp [IsInverse, meet_self]
  · intro b h
    have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    apply Fin.ext
    simp [meet] at h₁ h₂
    omega
def IsUnit (a : M) : Prop := ∃ b, meet a b = unit ∧ meet b a = unit
theorem units_exact (a : M) : IsUnit a ↔ a = unit := by
  constructor
  · rintro ⟨b,h,_⟩
    have hh := congrArg Fin.val h
    apply Fin.ext
    simp [meet,unit] at hh ⊢
    omega
  · rintro rfl
    exact ⟨unit,meet_unit unit,meet_unit unit⟩

def Character (K : Type) [Field K] :=
  { f : M → K // f unit = 1 ∧ ∀ a b, f (meet a b) = f a * f b }
def threshold {K : Type} [Field K] (t a : M) : K :=
  if t.val ≤ a.val then 1 else 0

def thresholdCharacter {K : Type} [Field K] (t : M) : Character K := by
  refine ⟨threshold t, ?_, ?_⟩
  · simp only [threshold,unit]; split <;> grind
  · intro a b
    simp only [threshold,meet]
    split <;> split <;> split <;> grind

section Characters
variable {K : Type} [Field K]
theorem character_binary (f : Character K) (a : M) : f.val a = 0 ∨ f.val a = 1 := by
  have h := f.property.2 a a
  rw [meet_self] at h
  grind
theorem character_upward (f : Character K) (a b : M)
    (h : a.val ≤ b.val) (ha : f.val a = 1) : f.val b = 1 := by
  have hh := f.property.2 a b
  rw [meet_of_le h] at hh
  grind

theorem character_classification (f : Character K) :
    ∃ t : M, ∀ a, f.val a = threshold t a := by
  have top : f.val 5 = 1 := f.property.1
  have allcases : ∀ a : M, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
    intro a; simp only [Fin.ext_iff]; omega
  by_cases h0 : f.val 0 = 1
  · refine ⟨0,?_⟩; intro a
    change f.val a = if 0 ≤ a.val then 1 else 0
    by_cases ha : 0 ≤ a.val
    · have hu := character_upward f 0 a ha h0
      simp only [if_pos ha]; exact hu
    · omega
  have z0 : f.val 0 = 0 := (character_binary f 0).resolve_right h0
  by_cases h1 : f.val 1 = 1
  · refine ⟨1,?_⟩; intro a
    change f.val a = if 1 ≤ a.val then 1 else 0
    by_cases ha : 1 ≤ a.val
    · have hu := character_upward f 1 a ha h1
      simp only [if_pos ha]; exact hu
    · have e : a = 0 := by simp only [Fin.ext_iff]; omega
      subst a
      exact z0
  have z1 : f.val 1 = 0 := (character_binary f 1).resolve_right h1
  by_cases h2 : f.val 2 = 1
  · refine ⟨2,?_⟩; intro a
    change f.val a = if 2 ≤ a.val then 1 else 0
    by_cases ha : 2 ≤ a.val
    · have hu := character_upward f 2 a ha h2
      simp only [if_pos ha]; exact hu
    · have e : a = 0 ∨ a = 1 := by simp only [Fin.ext_iff]; omega
      rcases e with e0 | e1
      · subst a; exact z0
      · subst a; exact z1
  have z2 : f.val 2 = 0 := (character_binary f 2).resolve_right h2
  by_cases h3 : f.val 3 = 1
  · refine ⟨3,?_⟩; intro a
    change f.val a = if 3 ≤ a.val then 1 else 0
    by_cases ha : 3 ≤ a.val
    · have hu := character_upward f 3 a ha h3
      simp only [if_pos ha]; exact hu
    · have e : a = 0 ∨ a = 1 ∨ a = 2 := by simp only [Fin.ext_iff]; omega
      rcases e with e0 | e1 | e2
      · subst a; exact z0
      · subst a; exact z1
      · subst a; exact z2
  have z3 : f.val 3 = 0 := (character_binary f 3).resolve_right h3
  by_cases h4 : f.val 4 = 1
  · refine ⟨4,?_⟩; intro a
    change f.val a = if 4 ≤ a.val then 1 else 0
    by_cases ha : 4 ≤ a.val
    · have hu := character_upward f 4 a ha h4
      simp only [if_pos ha]; exact hu
    · have e : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by simp only [Fin.ext_iff]; omega
      rcases e with e0 | e1 | e2 | e3
      · subst a; exact z0
      · subst a; exact z1
      · subst a; exact z2
      · subst a; exact z3
  have z4 : f.val 4 = 0 := (character_binary f 4).resolve_right h4
  refine ⟨5,?_⟩; intro a
  rcases allcases a with e0 | e1 | e2 | e3 | e4 | e5
  · subst a; exact z0
  · subst a; exact z1
  · subst a; exact z2
  · subst a; exact z3
  · subst a; exact z4
  · subst a; exact top

theorem threshold_injective {s t : M}
    (h : ∀ a, (threshold s a : K) = threshold t a) : s = t := by
  have hs := h s
  have ht := h t
  simp only [threshold] at hs ht
  apply Fin.ext
  split at hs <;> split at hs <;> split at ht <;> split at ht <;> grind
end Characters
end TLMC8207
