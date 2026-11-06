import Syzygy

namespace TLMC506

/-- Standard total-degree grading on the polynomial ring. -/
def Homogeneous (p : Poly) (d : Nat) : Prop :=
  ∀ i j, p.coeff i j = true → i + j = d

/-- Degree in the shifted free module R(-s). -/
def ShiftHomogeneous (p : Poly) (s d : Nat) : Prop :=
  ∀ i j, p.coeff i j = true → i + j + s = d

/-- The domain of the minimal presentation is R(-1) ⊕ R(-1). -/
def PresentationHomogeneous (v : FreeTwo) (d : Nat) : Prop :=
  ShiftHomogeneous v.1 1 d ∧ ShiftHomogeneous v.2 1 d

theorem koszul_homogeneous_iff (h : Poly) (d : Nat) :
    PresentationHomogeneous (koszul h) d ↔ ShiftHomogeneous h 2 d := by
  constructor
  · intro hh i j hij
    have hd := hh.1 i (j+1) hij
    omega
  · intro hh
    constructor
    · intro i j hij
      cases j with
      | zero => cases hij
      | succ j => have hd := hh i j hij; omega
    · intro i j hij
      cases i with
      | zero => cases hij
      | succ i => have hd := hh i j hij; omega

theorem constant_shift_homogeneous (c : Bool) (s : Nat) :
    ShiftHomogeneous (constant c) s s := by
  intro i j hij
  have hi : i = 0 ∧ j = 0 := by
    by_cases h : i = 0 ∧ j = 0
    · exact h
    · simp [h] at hij
  omega

theorem one_shift_homogeneous (s : Nat) : ShiftHomogeneous one s s := by
  simpa only [constant_true] using constant_shift_homogeneous true s

theorem augmentation_homogeneous {v : FreeTwo} {d : Nat}
    (hv : PresentationHomogeneous v d) : Homogeneous (augmentation v) d := by
  intro i j hij
  have hab : (xMul v.1).coeff i j = true ∨ (yMul v.2).coeff i j = true := by
    have h := hij
    unfold augmentation at h
    simp only [add_coeff] at h
    cases ha : (xMul v.1).coeff i j <;>
      cases hb : (yMul v.2).coeff i j <;> simp_all
  rcases hab with ha | hb
  · cases i with
    | zero => cases ha
    | succ i => have hd := hv.1 i j ha; omega
  · cases j with
    | zero => cases hb
    | succ j => have hd := hv.2 i j hb; omega

/-- β₁,d is nonzero precisely when the degree-d piece of K/mK is nonzero.
Here K is the actual kernel of the minimal presentation, not an assigned table. -/
def FirstBettiSupport (d : Nat) : Prop :=
  ∃ v : FreeTwo, IsSyzygy v ∧ PresentationHomogeneous v d ∧
    ¬ InMaximalTimesSyzygy v

theorem first_betti_support_iff (d : Nat) : FirstBettiSupport d ↔ d = 2 := by
  constructor
  · rintro ⟨v, hv, hd, hnonzero⟩
    have heq := syzygy_parametrization hv
    rw [heq] at hd hnonzero
    have hc : (dropY v.1).coeff 0 0 = true := by
      cases h : (dropY v.1).coeff 0 0 with
      | false => exact False.elim (hnonzero ((koszul_in_maximal_iff _).mpr h))
      | true => rfl
    have hdeg := ((koszul_homogeneous_iff _ _).mp hd) 0 0 hc
    omega
  · intro hd
    subst d
    refine ⟨koszul one, koszul_syzygy one, ?_, ?_⟩
    · exact (koszul_homogeneous_iff one 2).mpr (one_shift_homogeneous 2)
    · rw [koszul_in_maximal_iff]
      decide

theorem support_contains_two : FirstBettiSupport 2 := (first_betti_support_iff 2).mpr rfl

theorem support_has_no_other_point :
    ∀ j, FirstBettiSupport j → j = 2 := by
  intro j hj; exact (first_betti_support_iff j).mp hj

/-- Topological isolation uses an ambient open neighborhood whose intersection
with the support is just the point. The theorem below works for EVERY topology:
the only required topology axiom is that the whole ambient set is open. -/
def IsolatedInSubset {α : Type} (isOpen : (α → Prop) → Prop) (S : α → Prop) (j : α) : Prop :=
  S j ∧ ∃ U : α → Prop, isOpen U ∧ U j ∧ ∀ k, U k → S k → k = j

theorem first_betti_support_has_isolated_point
    (isOpen : (Nat → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    IsolatedInSubset isOpen FirstBettiSupport 2 := by
  refine ⟨support_contains_two, (fun _ => True), open_univ, trivial, ?_⟩
  intro k _ hk
  exact support_has_no_other_point k hk

def NoIsolatedPoints {α : Type} (isOpen : (α → Prop) → Prop) (S : α → Prop) : Prop :=
  ¬ ∃ j, IsolatedInSubset isOpen S j

theorem first_betti_no_isolated_clause_false
    (isOpen : (Nat → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    ¬ NoIsolatedPoints isOpen FirstBettiSupport := by
  intro h
  exact h ⟨2, first_betti_support_has_isolated_point isOpen open_univ⟩

/-- The same singleton also has an isolated vertex under any irreflexive
adjacency relation, including adjacency of consecutive integer degrees. -/
theorem first_betti_support_graph_isolated
    (adjacent : Nat → Nat → Prop) (irreflexive : ∀ n, ¬ adjacent n n) :
    FirstBettiSupport 2 ∧ ¬ ∃ j, FirstBettiSupport j ∧ adjacent 2 j := by
  refine ⟨support_contains_two, ?_⟩
  rintro ⟨j, hj, ha⟩
  have heq := support_has_no_other_point j hj
  subst j
  exact irreflexive 2 ha

/-- Integer-indexed grading, including all negative degrees. -/
def ShiftHomogeneousZ (p : Poly) (s : Nat) (d : Int) : Prop :=
  ∀ i j, p.coeff i j = true → (i : Int) + (j : Int) + (s : Int) = d

def PresentationHomogeneousZ (v : FreeTwo) (d : Int) : Prop :=
  ShiftHomogeneousZ v.1 1 d ∧ ShiftHomogeneousZ v.2 1 d

def FirstBettiSupportZ (d : Int) : Prop :=
  ∃ v : FreeTwo, IsSyzygy v ∧ PresentationHomogeneousZ v d ∧
    ¬ InMaximalTimesSyzygy v

theorem presentation_homogeneousZ_nat (v : FreeTwo) (d : Nat) :
    PresentationHomogeneousZ v (d : Int) ↔ PresentationHomogeneous v d := by
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · intro i j h; have he := ha i j h; omega
    · intro i j h; have he := hb i j h; omega
  · rintro ⟨ha,hb⟩
    constructor
    · intro i j h; have he := ha i j h; omega
    · intro i j h; have he := hb i j h; omega

theorem first_betti_supportZ_iff (d : Int) : FirstBettiSupportZ d ↔ d = 2 := by
  constructor
  · rintro ⟨v,hv,hd,hn⟩
    have heq := syzygy_parametrization hv
    rw [heq] at hd hn
    have hc : (dropY v.1).coeff 0 0 = true := by
      cases h : (dropY v.1).coeff 0 0 with
      | false => exact False.elim (hn ((koszul_in_maximal_iff _).mpr h))
      | true => rfl
    have hdeg := hd.1 0 1 hc
    omega
  · intro hd
    subst d
    obtain ⟨v,hv,hd,hn⟩ := support_contains_two
    exact ⟨v,hv,(presentation_homogeneousZ_nat v 2).mpr hd,hn⟩

theorem first_betti_supportZ_has_isolated_point
    (isOpen : (Int → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    IsolatedInSubset isOpen FirstBettiSupportZ 2 := by
  refine ⟨(first_betti_supportZ_iff 2).mpr rfl, (fun _ => True), open_univ, trivial, ?_⟩
  intro k _ hk
  exact (first_betti_supportZ_iff k).mp hk

theorem first_betti_no_isolatedZ_clause_false
    (isOpen : (Int → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    ¬ NoIsolatedPoints isOpen FirstBettiSupportZ := by
  intro h
  exact h ⟨2, first_betti_supportZ_has_isolated_point isOpen open_univ⟩

theorem first_betti_supportZ_graph_isolated
    (adjacent : Int → Int → Prop) (irreflexive : ∀ n, ¬ adjacent n n) :
    FirstBettiSupportZ 2 ∧ ¬ ∃ j, FirstBettiSupportZ j ∧ adjacent 2 j := by
  refine ⟨(first_betti_supportZ_iff 2).mpr rfl, ?_⟩
  rintro ⟨j, hj, ha⟩
  have heq := (first_betti_supportZ_iff j).mp hj
  subst j
  exact irreflexive 2 ha

end TLMC506
