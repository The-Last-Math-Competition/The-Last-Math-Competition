import Std

namespace CyclicActions

abbrev Coordinate := Fin 6
/-- Parameter `t` encodes `t.val + 1` transposed coordinate pairs. -/
abbrev Action := Fin 3

def mate (i : Coordinate) : Coordinate := match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | _ => 4

def sigma (t : Action) (i : Coordinate) : Coordinate :=
  if i.val / 2 ≤ t.val then mate i else i

def act (t : Action) (a : Bool) (i : Coordinate) : Coordinate :=
  if a then sigma t i else i

theorem involutions : ∀ (t : Action) (i : Coordinate), sigma t (sigma t i) = i := by decide

theorem cyclic_action : ∀ (t : Action) (a b : Bool) (i : Coordinate),
    act t a (act t b i) = act t (a ^^ b) i := by decide

theorem faithful (t : Action) {a b : Bool} (he : act t a = act t b) : a = b := by
  have h0 := congrFun he 0
  have hz : ∀ t : Action, sigma t 0 = 1 := by decide
  cases a <;> cases b <;> simp [act, hz] at h0 ⊢

def rep (t : Action) (i : Coordinate) : Coordinate :=
  if (sigma t i).val < i.val then sigma t i else i

theorem orbit_exact : ∀ (t : Action) (i j : Coordinate),
    rep t i = rep t j ↔ i = j ∨ i = sigma t j := by decide

def fixedCoordinates (t : Action) : List Coordinate :=
  (List.finRange 6).filter fun i => sigma t i == i

def pairRepresentatives (t : Action) : List Coordinate :=
  (List.finRange 6).filter fun i => i.val < (sigma t i).val

theorem orbit_counts : ∀ t : Action,
    (fixedCoordinates t).length = 6-2*(t.val+1) ∧
    (pairRepresentatives t).length = t.val+1 := by decide

/-- Basis unit `(i,a)` is the skew group basis element `eᵢ[sᵃ]`. -/
abbrev BasisUnit := Coordinate × Bool

def skewProduct (t : Action) (u v : BasisUnit) : Option BasisUnit :=
  if u.1 = act t u.2 v.1 then some (u.1, u.2 ^^ v.2) else none

theorem cross_orbit_zero : ∀ (t : Action) (i j : Coordinate) (a b : Bool),
    rep t i ≠ rep t j → skewProduct t (i,a) (j,b) = none := by decide

theorem fixed_coordinate_product : ∀ (t : Action) (i : Coordinate) (a b : Bool),
    sigma t i = i → skewProduct t (i,a) (i,b) = some (i,a ^^ b) := by decide

def matrixPosition (t : Action) (u : BasisUnit) : Coordinate × Coordinate :=
  (u.1, act t u.2 u.1)

def matrixUnitProduct (u v : Coordinate × Coordinate) : Option (Coordinate × Coordinate) :=
  if u.2 = v.1 then some (u.1, v.2) else none

set_option maxHeartbeats 0 in
theorem matrix_unit_rule : ∀ (t : Action) (i j : Coordinate) (a b : Bool),
    (skewProduct t (i,a) (j,b)).map (matrixPosition t) =
      matrixUnitProduct (matrixPosition t (i,a)) (matrixPosition t (j,b)) := by decide

set_option maxHeartbeats 0 in
/-- Every position in a two-point orbit is attained by precisely one basis unit. -/
theorem pair_units_bijective : ∀ (t : Action) (i j : Coordinate),
    sigma t i ≠ i → rep t i = rep t j →
      ∃ a : Bool, act t a i = j ∧ ∀ b : Bool, act t b i = j → b = a := by decide

/-- Evaluations of the two group basis elements at the signs +1 and -1. -/
def fixedBasisImage (a : Bool) : Int × Int := (1, if a then -1 else 1)

def componentProduct (x y : Int × Int) : Int × Int := (x.1*y.1,x.2*y.2)

theorem fixed_basis_rule : ∀ a b : Bool,
    fixedBasisImage (a ^^ b) = componentProduct (fixedBasisImage a) (fixedBasisImage b) := by
  decide

def fixedSplit (a b : Int) : Int × Int := (a+b,a-b)
def unscaledInverse (x y : Int) : Int × Int := (x+y,x-y)

theorem fixed_inverse_formulas (a b x y : Int) :
    unscaledInverse (fixedSplit a b).1 (fixedSplit a b).2 = (2*a,2*b) ∧
    fixedSplit (unscaledInverse x y).1 (unscaledInverse x y).2 = (2*x,2*y) := by
  simp only [fixedSplit, unscaledInverse, Prod.mk.injEq]
  omega

/-- Two simple labels per fixed block and one per two-point block. -/
def simpleCount (t : Action) : Nat :=
  2*(fixedCoordinates t).length + (pairRepresentatives t).length

theorem exact_simple_counts : simpleCount 0 = 9 ∧ simpleCount 1 = 6 ∧ simpleCount 2 = 3 := by
  decide

theorem simple_counts_injective : ∀ s t : Action, simpleCount s = simpleCount t → s = t := by
  decide

private theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · rintro h
      obtain ⟨i,_,he⟩ := List.mem_map.mp h
      exact Fin.succ_ne_zero i he
    · apply List.pairwise_map.mpr
      exact ih.imp (fun notEq eq => notEq (Fin.succ_inj.mp eq))

private theorem subset_length {xs ys : List Nat} (hxs : xs.Nodup) (h : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hxs
    have aIn : a ∈ ys := h (List.mem_cons_self ..)
    have hs : xs ⊆ ys.erase a := by
      intro x hx
      apply (List.mem_erase_of_ne (show x ≠ a from fun he => ha (he ▸ hx))).mpr
      exact h (List.mem_cons_of_mem a hx)
    have hl := ih hn hs
    rw [List.length_erase_of_mem aIn] at hl
    have hp : 0 < ys.length := List.length_pos_of_mem aIn
    simp only [List.length_cons]
    omega

private theorem injection_size {m n : Nat} (f : Fin m → Fin n)
    (injective : ∀ ⦃i j⦄, f i = f j → i = j) : m ≤ n := by
  let v := (List.finRange m).map fun i => (f i).val
  have hn : v.Nodup := List.pairwise_map.mpr
    ((nodup_finRange m).imp (fun ne he => ne (injective (Fin.ext he))))
  have hs : v ⊆ List.range n := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (f i).isLt
  have h := subset_length hn hs
  simpa [v] using h

structure LabelBijection (m n : Nat) where
  forward : Fin m → Fin n
  backward : Fin n → Fin m
  leftInverse : ∀ i, backward (forward i) = i
  rightInverse : ∀ i, forward (backward i) = i

theorem bijection_preserves_count {m n : Nat} (e : LabelBijection m n) : m = n := by
  have hf : m ≤ n := injection_size e.forward (by
    intro i j h
    have h' := congrArg e.backward h
    simpa only [e.leftInverse] using h')
  have hb : n ≤ m := injection_size e.backward (by
    intro i j h
    have h' := congrArg e.forward h
    simpa only [e.rightInverse] using h')
  exact Nat.le_antisymm hf hb

/-- Three pairwise distinct sets of derived suspension-orbit labels. -/
theorem three_derived_label_types :
    (simpleCount 0 = 9 ∧ simpleCount 1 = 6 ∧ simpleCount 2 = 3) ∧
    ∀ s t : Action, s ≠ t → ¬ Nonempty (LabelBijection (simpleCount s) (simpleCount t)) := by
  refine ⟨exact_simple_counts, ?_⟩
  rintro s t hne ⟨e⟩
  exact hne (simple_counts_injective _ _ (bijection_preserves_count e))

#print axioms faithful
#print axioms orbit_counts
#print axioms matrix_unit_rule
#print axioms pair_units_bijective
#print axioms fixed_basis_rule
#print axioms three_derived_label_types

end CyclicActions
