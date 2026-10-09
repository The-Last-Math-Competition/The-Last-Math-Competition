import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Set.Image
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
Source 00000003849: actual finite-type A2 Kashiwara crystals, their duals,
weight-preserving crystal isomorphisms, and a centrally symmetric support
that does not imply self-duality. No connectedness restriction is imposed.
-/
namespace CrystalCounterexample

namespace A2
abbrev Weight := ℤ × ℤ
abbrev Color := Fin 2

/-- Fundamental-weight coordinates. -/
def simpleRoot (i : Color) : Weight := if i = 0 then (2, -1) else (-1, 2)
/-- Pairing with the simple coroots. -/
def coroot (i : Color) (w : Weight) : ℤ := if i = 0 then w.1 else w.2
def reflect (i : Color) (w : Weight) : Weight :=
  if i = 0 then (-w.1, w.1 + w.2) else (w.1 + w.2, -w.2)

def rootVector (j : Fin 6) : Weight :=
  if j = 0 then (2, -1) else if j = 1 then (-1, 2)
  else if j = 2 then (1, 1) else if j = 3 then (-2, 1)
  else if j = 4 then (1, -2) else (-1, -1)

def roots : Set Weight := Set.range rootVector

def corootVector (j : Fin 6) : Weight :=
  if j = 0 then (1, 0) else if j = 1 then (0, 1)
  else if j = 2 then (1, 1) else if j = 3 then (-1, 0)
  else if j = 4 then (0, -1) else (-1, -1)

/-- The standard perfect pairing of the weight and coweight lattices Z^2. -/
def pairing (w h : Weight) : ℤ := w.1 * h.1 + w.2 * h.2
def rootReflect (j : Fin 6) (w : Weight) : Weight :=
  w - pairing w (corootVector j) • rootVector j
def corootReflect (j : Fin 6) (h : Weight) : Weight :=
  h - pairing (rootVector j) h • corootVector j

theorem root_coroot_pair_two : ∀ j : Fin 6, pairing (rootVector j) (corootVector j) = 2 := by decide
theorem root_vectors_distinct : Function.Injective rootVector := by decide
theorem coroot_vectors_distinct : Function.Injective corootVector := by decide
theorem all_root_reflections_closed : ∀ (j k : Fin 6),
    ∃ l : Fin 6, rootReflect j (rootVector k) = rootVector l := by decide
theorem all_coroot_reflections_closed : ∀ (j k : Fin 6),
    ∃ l : Fin 6, corootReflect j (corootVector k) = corootVector l := by decide
theorem paired_reflections_closed : ∀ (j k : Fin 6), ∃ l : Fin 6,
    rootReflect j (rootVector k) = rootVector l ∧
    corootReflect j (corootVector k) = corootVector l := by decide

theorem pairing_fundamental_basis (w : Weight) :
    pairing w (1,0) = w.1 ∧ pairing w (0,1) = w.2 := by simp [pairing]

/-- Standard GL3 weights restrict to fundamental coordinates for SL3/A2. -/
abbrev GL3Weight := Fin 3 → ℤ
def restrictWeight (w : GL3Weight) : Weight := (w 0 - w 1, w 1 - w 2)
def gl3Basis (j : Fin 3) : GL3Weight := fun k => if k = j then 1 else 0
def gl3SimpleRoot (i : Color) : GL3Weight :=
  if i = 0 then gl3Basis 0 - gl3Basis 1 else gl3Basis 1 - gl3Basis 2
theorem gl3_roots_restrict : ∀ i : Color,
    restrictWeight (gl3SimpleRoot i) = simpleRoot i := by decide
theorem central_direction_killed (n : ℤ) : restrictWeight (fun _ => n) = 0 := by
  simp [restrictWeight]

theorem cartan_entries :
    coroot 0 (simpleRoot 0) = 2 ∧ coroot 1 (simpleRoot 1) = 2 ∧
    coroot 0 (simpleRoot 1) = -1 ∧ coroot 1 (simpleRoot 0) = -1 := by decide

theorem simple_roots_nonzero : ∀ i : Color, simpleRoot i ≠ 0 := by decide

theorem coroot_neg (i : Color) (w : Weight) : coroot i (-w) = -coroot i w := by
  by_cases h : i = 0 <;> simp [coroot, h]

theorem coroot_add (i : Color) (x y : Weight) :
    coroot i (x + y) = coroot i x + coroot i y := by
  by_cases h : i = 0 <;> simp [coroot, h]

theorem reflection_formula (i : Color) (w : Weight) :
    reflect i w = w - coroot i w • simpleRoot i := by
  fin_cases i <;> ext <;> simp [reflect, coroot, simpleRoot] <;> omega

theorem reflection_involutive (i : Color) (w : Weight) :
    reflect i (reflect i w) = w := by
  fin_cases i <;> ext <;> simp [reflect]

theorem finite_root_reflection : ∀ (i : Color) (j : Fin 6),
    ∃ k : Fin 6, reflect i (rootVector j) = rootVector k := by decide

theorem roots_reflection_closed (i : Color) {w : Weight} (hw : w ∈ roots) :
    reflect i w ∈ roots := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨k, hk⟩ := finite_root_reflection i j
  exact ⟨k, hk.symm⟩

theorem positive_root_sum : rootVector 2 = simpleRoot 0 + simpleRoot 1 := by decide

end A2

open A2

/-- The finite-type specialization of Kashiwara's abstract crystal axioms.
Integer epsilon/phi exclude -infinity. No connectedness or multiplicity assumption.
The distinguished nonvertex is represented by Option.none. -/
structure Crystal (V : Type) where
  wt : V → Weight
  e : Color → V → Option V
  f : Color → V → Option V
  epsilon : Color → V → ℤ
  phi : Color → V → ℤ
  inverse : ∀ i x y, f i x = some y ↔ e i y = some x
  raising : ∀ i x y, e i x = some y →
    wt y = wt x + simpleRoot i ∧
    epsilon i y = epsilon i x - 1 ∧ phi i y = phi i x + 1
  lowering : ∀ i x y, f i x = some y →
    wt y = wt x - simpleRoot i ∧
    epsilon i y = epsilon i x + 1 ∧ phi i y = phi i x - 1
  string_weight : ∀ i v, phi i v = epsilon i v + coroot i (wt v)

namespace Crystal
variable {V U : Type}

/-- The actual contragredient crystal: negate wt, reverse all arrows,
and exchange the two string lengths. Every crystal axiom is derived. -/
def dual (C : Crystal V) : Crystal V where
  wt v := -C.wt v
  e := C.f
  f := C.e
  epsilon := C.phi
  phi := C.epsilon
  inverse i x y := (C.inverse i y x).symm
  raising i x y h := by
    obtain ⟨hw, he, hf⟩ := C.lowering i x y h
    exact ⟨by rw [hw]; abel, hf, he⟩
  lowering i x y h := by
    obtain ⟨hw, he, hf⟩ := C.raising i x y h
    exact ⟨by rw [hw]; abel, hf, he⟩
  string_weight i v := by
    rw [A2.coroot_neg]
    have h := C.string_weight i v
    omega

@[simp] theorem dual_wt (C : Crystal V) (v : V) : C.dual.wt v = -C.wt v := rfl

/-- Actual crystal isomorphisms preserve weights, both operators and both
string lengths. Underlying bijections alone are not crystal isomorphisms. -/
structure Iso (C : Crystal V) (D : Crystal U) extends V ≃ U where
  wt_preserving : ∀ v, D.wt (toEquiv v) = C.wt v
  e_preserving : ∀ i v, D.e i (toEquiv v) = (C.e i v).map toEquiv
  f_preserving : ∀ i v, D.f i (toEquiv v) = (C.f i v).map toEquiv
  epsilon_preserving : ∀ i v, D.epsilon i (toEquiv v) = C.epsilon i v
  phi_preserving : ∀ i v, D.phi i (toEquiv v) = C.phi i v

theorem Iso.from_dual_weight_negation {C : Crystal V} (g : Iso C.dual C) :
    ∀ v, C.wt (g.toEquiv v) = -C.wt v := g.wt_preserving

theorem Iso.to_dual_weight_negation {C : Crystal V} (g : Iso C C.dual) :
    ∀ v, C.wt (g.toEquiv v) = -C.wt v := by
  intro v
  have h := g.wt_preserving v
  change -C.wt (g.toEquiv v) = C.wt v at h
  calc
    C.wt (g.toEquiv v) = -(-C.wt (g.toEquiv v)) := (neg_neg _).symm
    _ = -C.wt v := congrArg Neg.neg h

end Crystal

/-- Iteration of actual partial crystal operators with none absorbing. -/
def iteratePartial {V : Type} (op : V → Option V) : ℕ → V → Option V
  | 0, v => some v
  | n+1, v => (op v).bind (iteratePartial op n)

/-- Seminormality: epsilon/phi are the exact maxima of nonzero operator strings. -/
def Seminormal {V : Type} (C : Crystal V) : Prop :=
  ∀ (i : Color) (v : V) (n : ℕ),
    (iteratePartial (C.e i) n v ≠ none ↔ (n : ℤ) ≤ C.epsilon i v) ∧
    (iteratePartial (C.f i) n v ≠ none ↔ (n : ℤ) ≤ C.phi i v)

theorem iterate_two_then_none {V : Type} (op : V → Option V)
    (h : ∀ v, (op v).bind op = none) (n : ℕ) (v : V) :
    iteratePartial op (n+2) v = none := by
  change (op v).bind (fun u => (op u).bind (iteratePartial op n)) = none
  rw [← Option.bind_assoc, h v]
  rfl

namespace Standard
abbrev Vertex := Fin 3

def wt (p : Vertex) : Weight :=
  if p = 0 then (1, 0) else if p = 1 then (-1, 1) else (0, -1)
def f (i : Color) (p : Vertex) : Option Vertex :=
  if i = 0 ∧ p = 0 then some 1
  else if i = 1 ∧ p = 1 then some 2 else none
def e (i : Color) (p : Vertex) : Option Vertex :=
  if i = 0 ∧ p = 1 then some 0
  else if i = 1 ∧ p = 2 then some 1 else none
def epsilon (i : Color) (p : Vertex) : ℤ := if e i p = none then 0 else 1
def phi (i : Color) (p : Vertex) : ℤ := if f i p = none then 0 else 1

/-- The explicit type-A2 standard fundamental crystal B(omega1). -/
def crystal : Crystal Vertex where
  wt := wt
  e := e
  f := f
  epsilon := epsilon
  phi := phi
  inverse := by decide
  raising := by decide
  lowering := by decide
  string_weight := by decide

theorem standard_edges : f 0 0 = some 1 ∧ f 1 1 = some 2 := by decide
theorem standard_weights : wt 0 = (1,0) ∧ wt 1 = (-1,1) ∧ wt 2 = (0,-1) := by decide
theorem highest_weight : e 0 0 = none ∧ e 1 0 = none ∧ wt 0 = (1,0) := by decide
theorem dual_highest_weight : crystal.dual.e 0 2 = none ∧
    crystal.dual.e 1 2 = none ∧ crystal.dual.wt 2 = (0,1) := by decide

theorem standard_weight_correspondence : ∀ p : Fin 3,
    A2.restrictWeight (A2.gl3Basis p) = crystal.wt p := by decide

end Standard

namespace Witness
abbrev Vertex := Fin 3 × Fin 3

/-- Two standard components and one actual dual component. -/
def component (c : Fin 3) : Crystal (Fin 3) :=
  if c = 2 then Standard.crystal.dual else Standard.crystal

def wt (v : Vertex) : Weight := (component v.1).wt v.2
def e (i : Color) (v : Vertex) : Option Vertex :=
  ((component v.1).e i v.2).map (fun p => (v.1, p))
def f (i : Color) (v : Vertex) : Option Vertex :=
  ((component v.1).f i v.2).map (fun p => (v.1, p))
def epsilon (i : Color) (v : Vertex) : ℤ := (component v.1).epsilon i v.2
def phi (i : Color) (v : Vertex) : ℤ := (component v.1).phi i v.2

/-- The nine-vertex crystal is instantiated with every required axiom proved. -/
def crystal : Crystal Vertex where
  wt := wt
  e := e
  f := f
  epsilon := epsilon
  phi := phi
  inverse := by decide
  raising := by decide
  lowering := by decide
  string_weight := by decide

theorem component_weight : ∀ (c p : Fin 3), crystal.wt (c,p) = (component c).wt p := by decide
theorem component_operators : ∀ (c p : Fin 3) (i : Color),
    crystal.e i (c,p) = ((component c).e i p).map (fun q => (c,q)) ∧
    crystal.f i (c,p) = ((component c).f i p).map (fun q => (c,q)) ∧
    crystal.epsilon i (c,p) = (component c).epsilon i p ∧
    crystal.phi i (c,p) = (component c).phi i p := by decide

theorem first_two_standard : component 0 = Standard.crystal ∧
    component 1 = Standard.crystal := by simp [component]
theorem third_is_actual_dual : component 2 = Standard.crystal.dual := by simp [component]

theorem short_strings : ∀ (i : Color) (v : Vertex),
    (crystal.e i v).bind (crystal.e i) = none ∧
    (crystal.f i v).bind (crystal.f i) = none := by decide

theorem nonnegative_strings : ∀ (i : Color) (v : Vertex),
    0 ≤ crystal.epsilon i v ∧ 0 ≤ crystal.phi i v := by decide

theorem strings_at_most_one : ∀ (i : Color) (v : Vertex),
    crystal.epsilon i v ≤ 1 ∧ crystal.phi i v ≤ 1 := by decide

theorem one_step_exact : ∀ (i : Color) (v : Vertex),
    (crystal.e i v ≠ none ↔ (1 : ℤ) ≤ crystal.epsilon i v) ∧
    (crystal.f i v ≠ none ↔ (1 : ℤ) ≤ crystal.phi i v) := by decide

theorem seminormal : Seminormal crystal := by
  intro i v n
  cases n with
  | zero => simpa [iteratePartial] using nonnegative_strings i v
  | succ n =>
    cases n with
    | zero => simpa [iteratePartial] using one_step_exact i v
    | succ n =>
      have he := iterate_two_then_none (crystal.e i) (fun v => (short_strings i v).1) n v
      have hf := iterate_two_then_none (crystal.f i) (fun v => (short_strings i v).2) n v
      have hb := strings_at_most_one i v
      simp only [Nat.add_assoc] at *
      rw [he, hf]
      simp only [ne_eq, not_true_eq_false, false_iff]
      constructor <;> omega

theorem support_negation : ∀ v : Vertex, ∃ u : Vertex, crystal.wt u = -crystal.wt v := by decide

def firstPositive : Vertex := (0, 0)
def secondPositive : Vertex := (1, 0)
def soleNegative : Vertex := (2, 0)

theorem negative_weight_unique : ∀ v : Vertex,
    crystal.wt v = -(1, 0) ↔ v = soleNegative := by decide

theorem no_weight_negating_equiv : ¬∃ g : Vertex ≃ Vertex,
    ∀ v, crystal.wt (g v) = -crystal.wt v := by
  rintro ⟨g, hg⟩
  have hfirst : g firstPositive = soleNegative :=
    (negative_weight_unique _).mp (by simpa [firstPositive, crystal, wt, component,
      Standard.crystal, Standard.wt] using hg firstPositive)
  have hsecond : g secondPositive = soleNegative :=
    (negative_weight_unique _).mp (by simpa [secondPositive, crystal, wt, component,
      Standard.crystal, Standard.wt] using hg secondPositive)
  have hdistinct : firstPositive ≠ secondPositive := by decide
  exact hdistinct (g.injective (hfirst.trans hsecond.symm))

theorem not_selfDual : ¬ Nonempty (Crystal.Iso crystal.dual crystal) := by
  rintro ⟨g⟩
  exact no_weight_negating_equiv ⟨g.toEquiv, g.from_dual_weight_negation⟩

theorem not_selfDual_reverse : ¬ Nonempty (Crystal.Iso crystal crystal.dual) := by
  rintro ⟨g⟩
  exact no_weight_negating_equiv ⟨g.toEquiv, g.to_dual_weight_negation⟩

end Witness

/-- Central symmetry in the actual weight lattice, allowing any lattice centre. -/
def CentrallySymmetric (s : Set Weight) : Prop :=
  ∃ c : Weight, ∀ w : Weight, w ∈ s ↔ c + c - w ∈ s

theorem witness_centrallySymmetric : CentrallySymmetric (Set.range Witness.crystal.wt) := by
  refine ⟨0, ?_⟩
  intro w
  simp only [zero_add, zero_sub]
  constructor
  · rintro ⟨v, rfl⟩
    exact Witness.support_negation v
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := Witness.support_negation v
    refine ⟨u, ?_⟩
    rw [hu, hv, neg_neg]

/-- The sufficient direction claimed for all nonempty A2 crystals.
A counterexample in this finite-type subclass refutes the unqualified source. -/
def SufficientDirection : Prop :=
  ∀ (V : Type) [Nonempty V] [Fintype V] (C : Crystal V),
    CentrallySymmetric (Set.range C.wt) → Nonempty (Crystal.Iso C.dual C)

def DualityCriterion : Prop :=
  ∀ (V : Type) [Nonempty V] [Fintype V] (C : Crystal V),
    Nonempty (Crystal.Iso C.dual C) ↔ CentrallySymmetric (Set.range C.wt)

theorem original_sufficient_direction_false : ¬ SufficientDirection := by
  intro h
  exact Witness.not_selfDual (h Witness.Vertex Witness.crystal witness_centrallySymmetric)

theorem original_iff_false : ¬ DualityCriterion := by
  intro h
  exact Witness.not_selfDual ((h Witness.Vertex Witness.crystal).mpr witness_centrallySymmetric)

end CrystalCounterexample
