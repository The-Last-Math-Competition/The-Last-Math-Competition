import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.DualNumber
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
The standard integral, unreduced, normalized Khovanov cube for two actual
closed three-crossing two-braids.  Diagram false is sigma_1^3; diagram true
changes only its last crossing.  Component representatives below are finite
certificates: every edge preserves them and every vertex has a genuine path
to its representative in the actual smoothing graph.
-/

namespace TLMC620

open scoped BigOperators TensorProduct

set_option maxRecDepth 2000
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

abbrev Port := Fin 12
abbrev Crossing := Fin 3
abbrev State := Fin 8
abbrev Entry := Crossing × Bool
abbrev Label := Fin 2


def stateBit (s : State) (j : Crossing) : Bool := (s.val / 2 ^ (2 - j.val)) % 2 == 1
instance stateCoeFun : CoeFun State (fun _ => Crossing → Bool) := ⟨stateBit⟩
def stateOf (bits : Crossing → Bool) : State :=
  ⟨4 * (bits 0).toNat + 2 * (bits 1).toNat + (bits 2).toNat, by
    have hb : ∀ b : Bool, b.toNat < 2 := by decide
    have h0 := hb (bits 0); have h1 := hb (bits 1); have h2 := hb (bits 2)
    omega⟩
theorem state_roundtrip : ∀ s : State, stateOf (stateBit s) = s := by decide
theorem all_bit_vectors : ∀ bits : Crossing → Bool, ∀ j : Crossing,
    stateBit (stateOf bits) j = bits j := by decide
def cubeStateEquiv : State ≃ (Crossing → Bool) where
  toFun := stateBit
  invFun := stateOf
  left_inv := state_roundtrip
  right_inv bits := funext (all_bit_vectors bits)

def port (i : Crossing) (p : Fin 4) : Port := ⟨4 * i.val + p.val, by omega⟩
def crossing (v : Port) : Crossing := ⟨v.val / 4, by omega⟩
def corner (v : Port) : Fin 4 := ⟨v.val % 4, Nat.mod_lt _ (by decide)⟩

/-- Actual closure arcs: bottom left/right go to the next top left/right. -/
def external (v : Port) : Port :=
  if h : (corner v).val < 2 then
    port (crossing v + 2) ⟨(corner v).val + 2, by omega⟩
  else port (crossing v + 1) ⟨(corner v).val - 2, by omega⟩

/-- The two strands of a braid crossing, with the same connectivity for both signs. -/
def strand (v : Port) : Port := port (crossing v) ⟨3 - (corner v).val, by omega⟩

def negative (flipped : Bool) (j : Crossing) : Bool := flipped && (j == 2)
def over (flipped : Bool) (e : Entry) : Bool := e.2 == negative flipped e.1
def successor (e : Entry) : Entry := (e.1 + 1, !e.2)
def entryPort (e : Entry) : Port := port e.1 (if e.2 then 1 else 0)
def overPort (d : Bool) (v : Port) : Bool :=
  if negative d (crossing v) then corner v == 1 || corner v == 2
  else corner v == 0 || corner v == 3

theorem external_involutive : Function.Involutive external := by
  change ∀ v, external (external v) = v
  decide
theorem strand_involutive : Function.Involutive strand := by
  change ∀ v, strand (strand v) = v
  decide
theorem external_no_fixed : ∀ v, external v ≠ v := by decide
theorem strand_no_fixed : ∀ v, strand v ≠ v := by decide

theorem actual_oriented_traversal : ∀ e : Entry,
    external (strand (entryPort e)) = entryPort (successor e) := by decide
theorem actual_over_under_on_strands : ∀ d v,
    overPort d (strand v) = overPort d v := by decide
theorem actual_entry_over_under : ∀ d e, overPort d (entryPort e) = over d e := by decide

theorem knot_single_oriented_component :
    ∀ e : Entry, ∃ n : Fin 6, successor^[n.val] (0, false) = e := by decide

theorem positive_braid_alternating :
    ∀ e : Entry, over false (successor e) = !(over false e) := by decide

theorem exactly_one_crossing_change :
    (∀ j : Crossing, negative true j ≠ negative false j ↔ j = 2) ∧
    (∀ e : Entry, e.1 = 2 → over true e = !(over false e)) := by decide

theorem actual_port_crossing_change : ∀ v : Port,
    overPort true v ≠ overPort false v ↔ crossing v = 2 := by decide

/-- The oriented vertical smoothing is 0 at a positive crossing and 1 at a negative one. -/
def horizontal (flipped : Bool) (s : State) (j : Crossing) : Bool :=
  s j != negative flipped j

def smoothing (flipped : Bool) (s : State) (v : Port) : Port :=
  port (crossing v)
    ((if horizontal flipped s (crossing v) then ![1, 0, 3, 2]
      else ![2, 3, 0, 1]) (corner v))

theorem smoothing_involutive : ∀ d s, Function.Involutive (smoothing d s) := by
  change ∀ d s v, smoothing d s (smoothing d s v) = v
  decide
theorem smoothing_no_fixed : ∀ d s v, smoothing d s v ≠ v := by decide

def matchingGraph (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) : SimpleGraph Port where
  Adj u v := v = external u ∨ v = m u
  symm := by
    constructor
    intro u v h
    rcases h with rfl | rfl
    · exact Or.inl (external_involutive u).symm
    · exact Or.inr (hi u).symm
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact external_no_fixed v h.symm
    · exact hn v h.symm

abbrev smoothingGraph (d : Bool) (s : State) :=
  matchingGraph (smoothing d s) (smoothing_involutive d s) (smoothing_no_fixed d s)
abbrev knotGraph := matchingGraph strand strand_involutive strand_no_fixed

def route (m : Port → Port) (n : ℕ) (v : Port) : Port := (m ∘ external)^[n] v
def pathSupport (m : Port → Port) (v : Port) : Finset Port :=
  (Finset.range 12).image (fun n => route m n v) ∪
  (Finset.range 12).image (fun n => m (route m n v))

theorem route_reachable (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) (v : Port) (n : ℕ) :
    (matchingGraph m hi hn).Reachable v (route m n v) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ n ih =>
    rw [route, Function.iterate_succ_apply']
    exact ih.trans ((SimpleGraph.Adj.reachable (Or.inl rfl)).trans
      (SimpleGraph.Adj.reachable (Or.inr rfl)))

theorem pathSupport_reachable (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) (u v : Port) (h : v ∈ pathSupport m u) :
    (matchingGraph m hi hn).Reachable u v := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp h
    exact route_reachable m hi hn u n
  · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp h
    exact (route_reachable m hi hn u n).trans
      (SimpleGraph.Adj.reachable (Or.inr rfl))

theorem actual_knot_connected : knotGraph.Connected := by
  have h : ∀ v : Port, v ∈ pathSupport strand 0 := by decide
  refine ⟨fun u v => ?_⟩
  exact (pathSupport_reachable strand strand_involutive strand_no_fixed 0 u (h u)).symm.trans
    (pathSupport_reachable strand strand_involutive strand_no_fixed 0 v (h v))

def smoothingMask (d : Bool) (s : State) : Fin 8 :=
  ⟨4 * (horizontal d s 0).toNat + 2 * (horizontal d s 1).toNat +
    (horizontal d s 2).toNat, by
      have hb : ∀ b : Bool, b.toNat < 2 := by decide
      have h0 := hb (horizontal d s 0)
      have h1 := hb (horizontal d s 1)
      have h2 := hb (horizontal d s 2)
      omega⟩

/-- Computed representative certificate, verified against actual graph paths below. -/
def componentRep (d : Bool) (s : State) : Port → Port :=
  (![![0,1,0,1,0,1,0,1,0,1,0,1],
     ![0,0,0,0,0,0,0,0,0,0,0,0],
     ![0,0,0,0,0,0,0,0,0,0,0,0],
     ![0,0,0,0,0,0,6,6,6,6,0,0],
     ![0,0,0,0,0,0,0,0,0,0,0,0],
     ![0,0,2,2,2,2,2,2,2,2,0,0],
     ![0,0,2,2,2,2,0,0,0,0,0,0],
     ![0,0,2,2,2,2,6,6,6,6,0,0]] : Fin 8 → Port → Port) (smoothingMask d s)


theorem representative_idempotent :
    ∀ d s v, componentRep d s (componentRep d s v) = componentRep d s v := by decide
theorem representative_external :
    ∀ d s v, componentRep d s (external v) = componentRep d s v := by decide
theorem representative_smoothing :
    ∀ d s v, componentRep d s (smoothing d s v) = componentRep d s v := by decide
theorem representative_le : ∀ d s v, componentRep d s v ≤ v := by decide
set_option maxHeartbeats 250000 in
theorem representative_actual_path :
    ∀ d s v, componentRep d s v ∈ pathSupport (smoothing d s) v := by decide

theorem representative_reachable (d : Bool) (s : State) (v : Port) :
    (smoothingGraph d s).Reachable v (componentRep d s v) :=
  pathSupport_reachable _ _ _ _ _ (representative_actual_path d s v)

theorem representative_eq_of_reachable (d : Bool) (s : State) {u v : Port}
    (h : (smoothingGraph d s).Reachable u v) : componentRep d s u = componentRep d s v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    have he : componentRep d s u = componentRep d s v := by
      rcases h with rfl | rfl
      · exact (representative_external d s u).symm
      · exact (representative_smoothing d s u).symm
    exact he.trans ih

theorem actual_component_iff (d : Bool) (s : State) (u v : Port) :
    (smoothingGraph d s).Reachable u v ↔ componentRep d s u = componentRep d s v := by
  constructor
  · exact representative_eq_of_reachable d s
  · intro h
    apply (representative_reachable d s u).trans
    rw [h]
    exact (representative_reachable d s v).symm

theorem representative_is_least (d : Bool) (s : State) (u v : Port)
    (h : (smoothingGraph d s).Reachable u v) : componentRep d s u ≤ v := by
  rw [representative_eq_of_reachable d s h]
  exact representative_le d s v

def Circle (d : Bool) (s : State) := {v : Port // componentRep d s v = v}
instance circleDecidableEq (d : Bool) (s : State) : DecidableEq (Circle d s) := by
  unfold Circle
  infer_instance
instance circleFintype (d : Bool) (s : State) : Fintype (Circle d s) := by
  unfold Circle
  infer_instance

def circleAt (d : Bool) (s : State) (v : Port) : Circle d s :=
  ⟨componentRep d s v, representative_idempotent d s v⟩

noncomputable def nativeCircleEquiv (d : Bool) (s : State) :
    (smoothingGraph d s).ConnectedComponent ≃ Circle d s where
  toFun := Quot.lift (circleAt d s) (by
    intro u v h
    exact Subtype.ext (representative_eq_of_reachable d s h))
  invFun c := (smoothingGraph d s).connectedComponentMk c.val
  left_inv := by
    intro c
    refine Quot.inductionOn c fun v => ?_
    exact Quot.sound (representative_reachable d s v).symm
  right_inv c := Subtype.ext c.property

def changeState (s : State) (j : Crossing) : State :=
  stateOf (Function.update (stateBit s) j true)
def firstCircle (d : Bool) (s : State) (j : Crossing) := circleAt d s (port j 0)
def secondCircle (d : Bool) (s : State) (j : Crossing) :=
  circleAt d s (port j (if horizontal d s j then 2 else 1))

/-- Verified local saddle: two inputs/one output or one input/two outputs. -/
theorem saddle_merge_or_split : ∀ d s j, s j = false →
    (firstCircle d s j = secondCircle d s j ∧
      firstCircle d (changeState s j) j ≠ secondCircle d (changeState s j) j) ∨
    (firstCircle d s j ≠ secondCircle d s j ∧
      firstCircle d (changeState s j) j = secondCircle d (changeState s j) j) := by decide

theorem unaffected_components_identical : ∀ d s j, s j = false → ∀ v : Port,
    (circleAt d s v ≠ firstCircle d s j ∧ circleAt d s v ≠ secondCircle d s j) ↔
    (circleAt d (changeState s j) v ≠ firstCircle d (changeState s j) j ∧
      circleAt d (changeState s j) v ≠ secondCircle d (changeState s j) j) := by decide

theorem unaffected_representatives_identical : ∀ d s j, s j = false → ∀ v : Port,
    circleAt d s v ≠ firstCircle d s j → circleAt d s v ≠ secondCircle d s j →
    componentRep d (changeState s j) v = componentRep d s v := by decide


def UnchangedCircle (d : Bool) (s : State) (j : Crossing) :=
  {r : Port // componentRep d s r = r ∧ r ≠ (firstCircle d s j).val ∧
    r ≠ (secondCircle d s j).val}

theorem unchanged_circle_certificate : ∀ d s j, s j = false → ∀ r : Port,
    (componentRep d s r = r ∧ r ≠ (firstCircle d s j).val ∧
      r ≠ (secondCircle d s j).val) ↔
    (componentRep d (changeState s j) r = r ∧
      r ≠ (firstCircle d (changeState s j) j).val ∧
      r ≠ (secondCircle d (changeState s j) j).val) := by decide

/-- The actual permutation of unaffected tensor factors, with its actual inverse. -/
def unchangedCircleEquiv (d : Bool) (s : State) (j : Crossing) (hj : s j = false) :
    UnchangedCircle d s j ≃ UnchangedCircle d (changeState s j) j where
  toFun c := ⟨c.val, (unchanged_circle_certificate d s j hj c.val).mp c.property⟩
  invFun c := ⟨c.val, (unchanged_circle_certificate d s j hj c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Frobenius := DualNumber ℤ
noncomputable def frobeniusBasis : Module.Basis Label ℤ Frobenius := Module.Basis.finTwoProd ℤ

@[simp] theorem frobeniusBasis_zero : frobeniusBasis 0 = 1 := Module.Basis.finTwoProd_zero ℤ
@[simp] theorem frobeniusBasis_one : frobeniusBasis 1 = DualNumber.eps := Module.Basis.finTwoProd_one ℤ

def mulCoefficient (a b c : Label) : ℤ :=
  if a = 1 ∧ b = 1 then 0 else if c.val = a.val + b.val then 1 else 0
def deltaCoefficient (a b c : Label) : ℤ :=
  if a = 0 then if b ≠ c then 1 else 0 else if b = 1 ∧ c = 1 then 1 else 0

theorem multiplication_on_basis (a b : Label) :
    frobeniusBasis a * frobeniusBasis b =
      ∑ c : Label, mulCoefficient a b c • frobeniusBasis c := by
  fin_cases a <;> fin_cases b <;>
    simp [mulCoefficient, Fin.sum_univ_succ, DualNumber.eps_pow_two, ← pow_two]

noncomputable def comultiplication : Frobenius →ₗ[ℤ] (Frobenius ⊗[ℤ] Frobenius) where
  toFun x := x.fst • ((1 : Frobenius) ⊗ₜ[ℤ] DualNumber.eps +
      DualNumber.eps ⊗ₜ[ℤ] (1 : Frobenius)) +
    x.snd • (DualNumber.eps ⊗ₜ[ℤ] DualNumber.eps)
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul]; abel
  map_smul' a x := by simp [mul_smul, smul_add]

theorem comultiplication_on_basis (a : Label) :
    comultiplication (frobeniusBasis a) =
      ∑ b : Label, ∑ c : Label,
        deltaCoefficient a b c • (frobeniusBasis b ⊗ₜ[ℤ] frobeniusBasis c) := by
  fin_cases a <;>
    simp [comultiplication, deltaCoefficient, Fin.sum_univ_succ]

abbrev CircleTensor (d : Bool) (s : State) :=
  PiTensorProduct ℤ (fun _ : Circle d s => Frobenius)
noncomputable def stateTensorBasis (d : Bool) (s : State) :
    Module.Basis (Circle d s → Label) ℤ (CircleTensor d s) :=
  Basis.piTensorProduct (fun _ => frobeniusBasis)
noncomputable def stateTensorCoordinates (d : Bool) (s : State) :
    CircleTensor d s ≃ₗ[ℤ] ((Circle d s → Label) → ℤ) := (stateTensorBasis d s).equivFun

noncomputable def unaffectedTensorReindex (d : Bool) (s : State) (j : Crossing)
    (hj : s j = false) :
    PiTensorProduct ℤ (fun _ : UnchangedCircle d s j => Frobenius) ≃ₗ[ℤ]
      PiTensorProduct ℤ (fun _ : UnchangedCircle d (changeState s j) j => Frobenius) :=
  PiTensorProduct.reindex ℤ (fun _ => Frobenius) (unchangedCircleEquiv d s j hj)

theorem tensor_basis_is_actual_tensor (d : Bool) (s : State) (lab : Circle d s → Label) :
    stateTensorBasis d s lab = PiTensorProduct.tprod ℤ (fun c => frobeniusBasis (lab c)) :=
  Basis.piTensorProduct_apply _ lab


abbrev Enhanced (d : Bool) := Σ s : State, Circle d s → Label
abbrev CubeModule (d : Bool) := Enhanced d → ℤ

/-- All actual circle representatives, certified from the complete smoothing partition. -/
theorem circle_representative_cases : ∀ d s (c : Circle d s),
    c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 6 := by decide

/-- A non-dependent, lossless key for the actual enhanced state. -/
def enhancedKey (d : Bool) (a : Enhanced d) : State × Label × Label × Label × Label :=
  (a.1, a.2 (circleAt d a.1 0), a.2 (circleAt d a.1 1),
    a.2 (circleAt d a.1 2), a.2 (circleAt d a.1 6))

theorem enhancedKey_injective (d : Bool) : Function.Injective (enhancedKey d) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  have hs : s = t := congrArg Prod.fst h
  subst t
  have hk := congrArg Prod.snd h
  have hf : a = b := by
    funext c
    rcases circle_representative_cases d s c with hc | hc | hc | hc
    · have he : circleAt d s 0 = c := Subtype.ext (by simpa [hc, circleAt] using c.property)
      rw [← he]
      exact congrArg Prod.fst hk
    · have he : circleAt d s 1 = c := Subtype.ext (by simpa [hc, circleAt] using c.property)
      rw [← he]
      exact congrArg (fun x => x.2.1) hk
    · have he : circleAt d s 2 = c := Subtype.ext (by simpa [hc, circleAt] using c.property)
      rw [← he]
      exact congrArg (fun x => x.2.2.1) hk
    · have he : circleAt d s 6 = c := Subtype.ext (by simpa [hc, circleAt] using c.property)
      rw [← he]
      exact congrArg (fun x => x.2.2.2) hk
  subst b
  rfl

instance (priority := 2000) enhancedDecidableEq (d : Bool) : DecidableEq (Enhanced d) :=
  fun a b => decidable_of_iff (enhancedKey d a = enhancedKey d b)
    ⟨fun h => enhancedKey_injective d h, congrArg (enhancedKey d)⟩

/-- The finite direct sum of all actual circle tensor modules, in basis coordinates. -/
noncomputable def wholeCubeTensorCoordinates (d : Bool) :
    (∀ s : State, CircleTensor d s) ≃ₗ[ℤ] CubeModule d where
  toFun x a := stateTensorCoordinates d a.1 (x a.1) a.2
  invFun v s := (stateTensorCoordinates d s).symm (fun lab => v ⟨s,lab⟩)
  left_inv x := by
    funext s
    exact (stateTensorCoordinates d s).symm_apply_apply (x s)
  right_inv v := by funext a; simp
  map_add' x y := by
    funext a
    exact congrFun ((stateTensorCoordinates d a.1).map_add (x a.1) (y a.1)) a.2
  map_smul' z x := by
    funext a
    exact congrFun ((stateTensorCoordinates d a.1).map_smul z (x a.1)) a.2

def weight (s : State) : ℕ := ∑ j : Crossing, (s j).toNat
def negativeCount (d : Bool) : ℕ := ∑ j : Crossing, (negative d j).toNat
def positiveCount (d : Bool) : ℕ := 3 - negativeCount d
def homologicalDegree (d : Bool) (a : Enhanced d) : ℤ := (weight a.1 : ℤ) - negativeCount d
def quantumDegree (d : Bool) (a : Enhanced d) : ℤ :=
  (∑ c : Circle d a.1, (1 - 2 * (a.2 c).val : ℤ)) +
    (weight a.1 : ℤ) + positiveCount d - 2 * negativeCount d

def horizontalWeight (d : Bool) (s : State) : ℕ :=
  ∑ j : Crossing, (horizontal d s j).toNat

theorem circle_count_certificate : ∀ d s,
    Fintype.card (Circle d s) = if horizontalWeight d s = 0 then 2 else horizontalWeight d s := by
  decide

theorem actual_native_component_count (d : Bool) (s : State) :
    Nat.card (smoothingGraph d s).ConnectedComponent =
      if horizontalWeight d s = 0 then 2 else horizontalWeight d s := by
  calc
    Nat.card (smoothingGraph d s).ConnectedComponent = Nat.card (Circle d s) :=
      Nat.card_congr (nativeCircleEquiv d s)
    _ = Fintype.card (Circle d s) := Nat.card_eq_fintype_card
    _ = _ := circle_count_certificate d s

theorem actual_enhanced_degree_counts :
    (Fintype.card {a : Enhanced false // homologicalDegree false a = 0},
      Fintype.card {a : Enhanced false // homologicalDegree false a = 1},
      Fintype.card {a : Enhanced false // homologicalDegree false a = 2},
      Fintype.card {a : Enhanced false // homologicalDegree false a = 3}) = (4,6,12,8) ∧
    (Fintype.card {a : Enhanced true // homologicalDegree true a = -1},
      Fintype.card {a : Enhanced true // homologicalDegree true a = 0},
      Fintype.card {a : Enhanced true // homologicalDegree true a = 1},
      Fintype.card {a : Enhanced true // homologicalDegree true a = 2}) = (2,12,12,4) := by decide

theorem actual_normalization : negativeCount false = 0 ∧ positiveCount false = 3 ∧
    negativeCount true = 1 ∧ positiveCount true = 2 := by decide

/-- Identity tensors on every unaffected actual circle, with canonical component reordering. -/
def unaffectedLabels (d : Bool) (a b : Enhanced d) (j : Crossing) : Prop :=
  ∀ v : Port, circleAt d a.1 v ≠ firstCircle d a.1 j →
    circleAt d a.1 v ≠ secondCircle d a.1 j →
      a.2 (circleAt d a.1 v) = b.2 (circleAt d b.1 v)

instance unaffectedLabelsDecidable (d : Bool) (a b : Enhanced d) (j : Crossing) :
    Decidable (unaffectedLabels d a b j) := by
  unfold unaffectedLabels
  infer_instance

/-- Genuine local m or Delta matrix, evaluated on actual tensor basis vectors. -/
def saddleCoefficient (d : Bool) (a b : Enhanced d) (j : Crossing) : ℤ :=
  if a.1 j = false ∧ b.1 = changeState a.1 j ∧ unaffectedLabels d a b j then
    if firstCircle d a.1 j = secondCircle d a.1 j then
      deltaCoefficient (a.2 (firstCircle d a.1 j))
        (b.2 (firstCircle d b.1 j)) (b.2 (secondCircle d b.1 j))
    else mulCoefficient (a.2 (firstCircle d a.1 j))
      (a.2 (secondCircle d a.1 j)) (b.2 (firstCircle d b.1 j))
  else 0

/-- Native tensor-space saddle, using exactly m/Delta and the verified circle matching. -/
noncomputable def tensorSaddle (d : Bool) (s : State) (j : Crossing) :
    CircleTensor d s →ₗ[ℤ] CircleTensor d (changeState s j) :=
  (stateTensorBasis d s).constr ℤ (fun a =>
    ∑ b : Circle d (changeState s j) → Label,
      saddleCoefficient d ⟨s,a⟩ ⟨changeState s j,b⟩ j •
        stateTensorBasis d (changeState s j) b)

theorem tensorSaddle_on_basis (d : Bool) (s : State) (j : Crossing)
    (a : Circle d s → Label) :
    tensorSaddle d s j (stateTensorBasis d s a) =
      ∑ b : Circle d (changeState s j) → Label,
        saddleCoefficient d ⟨s,a⟩ ⟨changeState s j,b⟩ j •
          stateTensorBasis d (changeState s j) b :=
  (stateTensorBasis d s).constr_basis ℤ _ a

theorem tensorSaddle_on_actual_tensor (d : Bool) (s : State) (j : Crossing)
    (a : Circle d s → Label) :
    tensorSaddle d s j (PiTensorProduct.tprod ℤ (fun c => frobeniusBasis (a c))) =
      ∑ b : Circle d (changeState s j) → Label,
        saddleCoefficient d ⟨s,a⟩ ⟨changeState s j,b⟩ j •
          PiTensorProduct.tprod ℤ (fun c => frobeniusBasis (b c)) := by
  rw [← tensor_basis_is_actual_tensor, tensorSaddle_on_basis]
  simp_rw [tensor_basis_is_actual_tensor]

theorem tensorSaddle_actual_matrix_entry (d : Bool) (s : State) (j : Crossing)
    (a : Circle d s → Label) (b : Circle d (changeState s j) → Label) :
    stateTensorCoordinates d (changeState s j)
        (tensorSaddle d s j (stateTensorBasis d s a)) b =
      saddleCoefficient d ⟨s,a⟩ ⟨changeState s j,b⟩ j := by
  rw [tensorSaddle_on_basis]
  change ((stateTensorBasis d (changeState s j)).equivFun
    (∑ c, saddleCoefficient d ⟨s,a⟩ ⟨changeState s j,c⟩ j •
      stateTensorBasis d (changeState s j) c)) b = _
  rw [← (stateTensorBasis d (changeState s j)).equivFun_symm_apply]
  exact congrFun ((stateTensorBasis d (changeState s j)).equivFun.apply_symm_apply _) b

def cubeSign (s : State) (j : Crossing) : ℤ := (-1) ^
  (∑ i ∈ Finset.univ.filter (fun i : Crossing => i < j), (s i).toNat)
def differentialCoefficient (d : Bool) (a b : Enhanced d) : ℤ :=
  ∑ j : Crossing, cubeSign a.1 j * saddleCoefficient d a b j

def differential (d : Bool) : CubeModule d →ₗ[ℤ] CubeModule d where
  toFun v b := ∑ a : Enhanced d, differentialCoefficient d a b * v a
  map_add' v w := by ext b; simp [mul_add, Finset.sum_add_distrib]
  map_smul' z v := by ext b; simp [Finset.mul_sum, mul_left_comm]


set_option maxHeartbeats 250000 in
theorem differential_respects_both_gradings : ∀ d (a b : Enhanced d),
    differentialCoefficient d a b ≠ 0 →
    homologicalDegree d b = homologicalDegree d a + 1 ∧ quantumDegree d b = quantumDegree d a := by
  decide +kernel


set_option maxHeartbeats 250000 in
theorem square_zero_matrix : ∀ d (a b : Enhanced d),
    (∑ c : Enhanced d, differentialCoefficient d c b * differentialCoefficient d a c) = 0 := by
  decide +kernel

theorem differential_squared (d : Bool) (v : CubeModule d) :
    differential d (differential d v) = 0 := by
  ext b
  simp only [differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, square_zero_matrix, zero_mul, Finset.sum_const_zero]

/-- Actual homogeneous summand of the finite direct sum of circle tensor modules. -/

def chainPiece (d : Bool) (i j : ℤ) : Submodule ℤ (CubeModule d) where
  carrier := {v | ∀ a, homologicalDegree d a ≠ i ∨ quantumDegree d a ≠ j → v a = 0}
  zero_mem' := by intro a h; rfl
  add_mem' hv hw := by intro a h; simp [hv a h, hw a h]
  smul_mem' z v hv := by intro a h; simp [hv a h]

theorem differential_mem_piece (d : Bool) (i j : ℤ) (v : CubeModule d)
    (hv : v ∈ chainPiece d i j) : differential d v ∈ chainPiece d (i + 1) j := by
  intro b hb
  apply Finset.sum_eq_zero
  intro a _
  by_cases hc : differentialCoefficient d a b = 0
  · simp [hc]
  · have hg := differential_respects_both_gradings d a b hc
    by_cases ha : homologicalDegree d a = i ∧ quantumDegree d a = j
    · exfalso
      rcases hb with hb | hb
      · exact hb (by simpa [ha.1] using hg.1)
      · exact hb (hg.2.trans ha.2)
    · simp [hv a (not_and_or.mp ha)]

def cyclePiece (d : Bool) (i j : ℤ) : Submodule ℤ (CubeModule d) :=
  chainPiece d i j ⊓ LinearMap.ker (differential d)

/-- The full actual incoming differential, with its image in the actual kernel. -/
def boundaryMap (d : Bool) (i j : ℤ) : chainPiece d (i - 1) j →ₗ[ℤ] cyclePiece d i j where
  toFun v := ⟨differential d v.val,
    ⟨by simpa using differential_mem_piece d (i - 1) j v.val v.property,
      differential_squared d v.val⟩⟩
  map_add' v w := Subtype.ext (map_add (differential d) v.val w.val)
  map_smul' z v := Subtype.ext (map_smul (differential d) z v.val)

/-- Standard integral unreduced normalized bigraded Khovanov group: ker d / im d. -/
abbrev Kh (d : Bool) (i j : ℤ) :=
  cyclePiece d i j ⧸ LinearMap.range (boundaryMap d i j)

def basisVector (d : Bool) (a : Enhanced d) : CubeModule d := fun b => if b = a then 1 else 0

theorem differential_basis_apply (d : Bool) (a b : Enhanced d) :
    differential d (basisVector d a) b = differentialCoefficient d a b := by
  simp [differential, basisVector, mul_ite]

theorem basisVector_mem_piece (d : Bool) (a : Enhanced d) (i j : ℤ)
    (hi : homologicalDegree d a = i) (hj : quantumDegree d a = j) :
    basisVector d a ∈ chainPiece d i j := by
  intro b hb
  by_cases h : b = a
  · subst b
    exact False.elim (hb.elim (fun h => h hi) (fun h => h hj))
  · simp [basisVector, h]

def enhanced (d : Bool) (s : State) (minus : Finset Port) : Enhanced d :=
  ⟨s, fun c => if c.val ∈ minus then 1 else 0⟩


def h2a : Enhanced false := enhanced false (stateOf ![false,true,true]) {0}
def h2p : Enhanced false := enhanced false (stateOf ![false,true,true]) {6}
def h2b : Enhanced false := enhanced false (stateOf ![true,false,true]) {2}
def h2c : Enhanced false := enhanced false (stateOf ![true,true,false]) {2}
def h3a : Enhanced false := enhanced false (stateOf ![true,true,true]) ∅

theorem actual_witness_gradings :
    (homologicalDegree false h2a, quantumDegree false h2a) = (2,5) ∧
    (homologicalDegree false h2p, quantumDegree false h2p) = (2,5) ∧
    (homologicalDegree false h2b, quantumDegree false h2b) = (2,5) ∧
    (homologicalDegree false h2c, quantumDegree false h2c) = (2,5) ∧
    (homologicalDegree false h3a, quantumDegree false h3a) = (3,9) := by decide

def cycle2 : CubeModule false :=
  -basisVector false h2a + basisVector false h2b + basisVector false h2c
def cycle3 : CubeModule false := basisVector false h3a
def probe2 (v : CubeModule false) : ℤ := v h2a - v h2p
def probe3 (v : CubeModule false) : ℤ := v h3a

set_option maxHeartbeats 250000 in
theorem cycle2_matrix_certificate : ∀ b : Enhanced false,
    -differentialCoefficient false h2a b + differentialCoefficient false h2b b +
      differentialCoefficient false h2c b = 0 := by decide +kernel
set_option maxHeartbeats 250000 in
theorem cycle3_matrix_certificate : ∀ b : Enhanced false,
    differentialCoefficient false h3a b = 0 := by decide +kernel
set_option maxHeartbeats 250000 in
theorem probe2_matrix_certificate : ∀ a : Enhanced false,
    differentialCoefficient false a h2a - differentialCoefficient false a h2p = 0 := by decide +kernel
theorem probe3_matrix_certificate : ∀ a : Enhanced false,
    differentialCoefficient false a h3a = 0 := by decide +kernel

theorem cycle2_closed : differential false cycle2 = 0 := by
  ext b
  simp only [cycle2, map_add, map_neg, Pi.add_apply, Pi.neg_apply,
    differential_basis_apply, Pi.zero_apply]
  exact cycle2_matrix_certificate b
theorem cycle3_closed : differential false cycle3 = 0 := by
  ext b
  simpa [cycle3, differential_basis_apply] using cycle3_matrix_certificate b

theorem probe2_vanishes_on_boundaries (v : CubeModule false) : probe2 (differential false v) = 0 := by
  change (∑ a, differentialCoefficient false a h2a * v a) -
    (∑ a, differentialCoefficient false a h2p * v a) = 0
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← sub_mul, probe2_matrix_certificate, zero_mul]
theorem probe3_vanishes_on_boundaries (v : CubeModule false) : probe3 (differential false v) = 0 := by
  change (∑ a, differentialCoefficient false a h3a * v a) = 0
  simp [probe3_matrix_certificate]

theorem witness_probe_values : probe2 cycle2 = -1 ∧ probe3 cycle3 = 1 := by decide

def cycle2Element : cyclePiece false 2 5 := ⟨cycle2, by
  constructor
  · have h := actual_witness_gradings
    exact (chainPiece false 2 5).add_mem
      ((chainPiece false 2 5).add_mem
        ((chainPiece false 2 5).neg_mem (basisVector_mem_piece false h2a 2 5
          (Prod.mk.inj h.1).1 (Prod.mk.inj h.1).2))
        (basisVector_mem_piece false h2b 2 5
          (Prod.mk.inj h.2.2.1).1 (Prod.mk.inj h.2.2.1).2))
      (basisVector_mem_piece false h2c 2 5
        (Prod.mk.inj h.2.2.2.1).1 (Prod.mk.inj h.2.2.2.1).2)
  · exact cycle2_closed⟩

def cycle3Element : cyclePiece false 3 9 := ⟨cycle3, by
  constructor
  · exact basisVector_mem_piece false h3a 3 9
      (Prod.mk.inj actual_witness_gradings.2.2.2.2).1
      (Prod.mk.inj actual_witness_gradings.2.2.2.2).2
  · exact cycle3_closed⟩

theorem cycle2_not_boundary : cycle2Element ∉ LinearMap.range (boundaryMap false 2 5) := by
  rintro ⟨v, hv⟩
  have he : differential false v.val = cycle2 := congrArg Subtype.val hv
  have hp := congrArg probe2 he
  rw [probe2_vanishes_on_boundaries, witness_probe_values.1] at hp
  norm_num at hp

theorem cycle3_not_boundary : cycle3Element ∉ LinearMap.range (boundaryMap false 3 9) := by
  rintro ⟨v, hv⟩
  have he : differential false v.val = cycle3 := congrArg Subtype.val hv
  have hp := congrArg probe3 he
  rw [probe3_vanishes_on_boundaries, witness_probe_values.2] at hp
  norm_num at hp

def h2Class : Kh false 2 5 := (LinearMap.range (boundaryMap false 2 5)).mkQ cycle2Element
def h3Class : Kh false 3 9 := (LinearMap.range (boundaryMap false 3 9)).mkQ cycle3Element

theorem h2Class_nonzero : h2Class ≠ 0 := by
  intro h
  exact cycle2_not_boundary ((Submodule.Quotient.mk_eq_zero _).mp h)
theorem h3Class_nonzero : h3Class ≠ 0 := by
  intro h
  exact cycle3_not_boundary ((Submodule.Quotient.mk_eq_zero _).mp h)

/- A genuine integral section of the flipped cube's final differential. -/
def t00 : Enhanced true := enhanced true (stateOf ![true,true,true]) ∅
def t01 : Enhanced true := enhanced true (stateOf ![true,true,true]) {2}
def t10 : Enhanced true := enhanced true (stateOf ![true,true,true]) {0}
def t11 : Enhanced true := enhanced true (stateOf ![true,true,true]) {0,2}
def p000 : Enhanced true := enhanced true (stateOf ![true,true,false]) ∅
def p001 : Enhanced true := enhanced true (stateOf ![true,true,false]) {6}
def pPlus : Enhanced true := enhanced true (stateOf ![false,true,true]) ∅
def pMinus : Enhanced true := enhanced true (stateOf ![false,true,true]) {0}

def sectionCoefficient (a b : Enhanced true) : ℤ :=
  if a = t00 then if b = p000 then 1 else 0
  else if a = t01 then (if b = pPlus then 1 else 0) - (if b = p001 then 1 else 0)
  else if a = t10 then if b = p001 then 1 else 0
  else if a = t11 then if b = pMinus then 1 else 0
  else 0

def topSection (v : CubeModule true) : CubeModule true :=
  fun b => ∑ a : Enhanced true, sectionCoefficient a b * v a

theorem section_grading_certificate : ∀ a b : Enhanced true,
    sectionCoefficient a b ≠ 0 → homologicalDegree true a = 2 ∧
      homologicalDegree true b = 1 ∧ quantumDegree true a = quantumDegree true b := by decide +kernel


set_option maxHeartbeats 250000 in
theorem section_identity_certificate : ∀ a b : Enhanced true,
    (∑ c : Enhanced true, differentialCoefficient true c b * sectionCoefficient a c) =
      if homologicalDegree true a = 2 then if b = a then 1 else 0 else 0 := by decide +kernel

theorem section_mem_piece (j : ℤ) (v : CubeModule true) (hv : v ∈ chainPiece true 2 j) :
    topSection v ∈ chainPiece true 1 j := by
  intro b hb
  apply Finset.sum_eq_zero
  intro a _
  by_cases hc : sectionCoefficient a b = 0
  · simp [hc]
  · have hg := section_grading_certificate a b hc
    by_cases ha : homologicalDegree true a = 2 ∧ quantumDegree true a = j
    · exfalso
      rcases hb with hb | hb
      · exact hb hg.2.1
      · exact hb (hg.2.2.symm.trans ha.2)
    · simp [hv a (not_and_or.mp ha)]

theorem topSection_right_inverse (j : ℤ) (v : CubeModule true)
    (hv : v ∈ chainPiece true 2 j) : differential true (topSection v) = v := by
  ext b
  change (∑ c, differentialCoefficient true c b *
    (∑ a, sectionCoefficient a c * v a)) = v b
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, section_identity_certificate]
  rw [Finset.sum_eq_single b]
  · by_cases hb : homologicalDegree true b = 2
    · simp [hb]
    · have hz := hv b (Or.inl hb)
      simp [hb, hz]
  · intro a _ hab
    simp [Ne.symm hab]
  · simp

theorem flipped_h2_zero (j : ℤ) : Subsingleton (Kh true 2 j) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply LinearMap.range_eq_top.mpr
  intro v
  refine ⟨⟨topSection v.val, by simpa using section_mem_piece j v.val v.property.1⟩, ?_⟩
  exact Subtype.ext (topSection_right_inverse j v.val v.property.1)

theorem flipped_degree_bound : ∀ a : Enhanced true, homologicalDegree true a ≤ 2 := by decide

theorem flipped_h3_zero (j : ℤ) : Subsingleton (Kh true 3 j) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply LinearMap.range_eq_top.mpr
  intro v
  have hv : v = 0 := by
    apply Subtype.ext
    ext a
    exact v.property.1 a (Or.inl (by have := flipped_degree_bound a; omega))
  subst v
  exact ⟨0, map_zero _⟩

theorem two_distinct_bigraded_groups_change :
    ¬Nonempty (Kh false 2 5 ≃ₗ[ℤ] Kh true 2 5) ∧
    ¬Nonempty (Kh false 3 9 ≃ₗ[ℤ] Kh true 3 9) := by
  constructor
  · rintro ⟨e⟩
    let := flipped_h2_zero 5
    exact h2Class_nonzero (e.injective (Subsingleton.elim (e h2Class) (e 0)))
  · rintro ⟨e⟩
    let := flipped_h3_zero 9
    exact h3Class_nonzero (e.injective (Subsingleton.elim (e h3Class) (e 0)))

theorem two_actual_abelian_homology_groups_change :
    ¬Nonempty (Kh false 2 5 ≃+ Kh true 2 5) ∧
    ¬Nonempty (Kh false 3 9 ≃+ Kh true 3 9) := by
  constructor
  · rintro ⟨e⟩
    let := flipped_h2_zero 5
    exact h2Class_nonzero (e.injective (Subsingleton.elim (e h2Class) (e 0)))
  · rintro ⟨e⟩
    let := flipped_h3_zero 9
    exact h3Class_nonzero (e.injective (Subsingleton.elim (e h3Class) (e 0)))

theorem complete_counterexample :
    knotGraph.Connected ∧
    (∀ e : Entry, over false (successor e) = !(over false e)) ∧
    (∀ j : Crossing, negative true j ≠ negative false j ↔ j = 2) ∧
    ¬Nonempty (Kh false 2 5 ≃+ Kh true 2 5) ∧
    ¬Nonempty (Kh false 3 9 ≃+ Kh true 3 9) :=
  ⟨actual_knot_connected, positive_braid_alternating,
    exactly_one_crossing_change.1, two_actual_abelian_homology_groups_change⟩


end TLMC620
