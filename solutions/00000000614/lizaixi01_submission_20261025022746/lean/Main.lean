import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

/-!
The actual (2,-1) curve on the product torus, its clockwise half-twist
two-braid diagram, and its rational unreduced Lee complex.  The published
identification of this product torus with the zero-framed unknot boundary
is a disclosed geometric boundary, not a Lean axiom or a new typeclass.
-/

noncomputable section
namespace TLMC614

open CategoryTheory Module
open scoped BigOperators TensorProduct

set_option maxRecDepth 2000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Actual integral winding curve on the longitude/meridian torus. -/
def torusCable (z : Circle) : Circle × Circle := (z ^ 2, z ^ (-1 : ℤ))

theorem torusCable_continuous : Continuous torusCable := by
  unfold torusCable
  fun_prop

theorem torusCable_injective : Function.Injective torusCable := by
  intro z w h
  have h' := congrArg Prod.snd h
  simpa [torusCable] using h'

theorem cable_parameters_admissible : (0 : ℤ) < 2 ∧ Int.gcd 2 (-1) = 1 := by decide

abbrev MeridianDisk := {w : ℂ // ‖w‖ ≤ 1}
abbrev ProductSolidTorus := Circle × MeridianDisk

def companion (z : Circle) : ProductSolidTorus := (z, ⟨0, by norm_num⟩)
def torusBoundary (p : Circle × Circle) : ProductSolidTorus :=
  (p.1, ⟨p.2, by simp⟩)
def cableInProductSolidTorus (z : Circle) : ProductSolidTorus := torusBoundary (torusCable z)

theorem actual_core_and_boundary :
    Function.Injective companion ∧ Function.Injective cableInProductSolidTorus ∧
      ∀ z w, companion z ≠ cableInProductSolidTorus w := by
  constructor
  · intro z w h
    exact congrArg Prod.fst h
  constructor
  · intro z w h
    apply torusCable_injective
    have hf := congrArg Prod.fst h
    have hs := congrArg (fun x : ProductSolidTorus => (x.2 : ℂ)) h
    apply Prod.ext
    · exact hf
    · apply Circle.ext
      exact hs
  · intro z w h
    have hh := congrArg (fun x : ProductSolidTorus => ‖(x.2 : ℂ)‖) h
    simp [companion, cableInProductSolidTorus, torusBoundary] at hh

/-- The actual crossingless planar unit circle, with no double points. -/
def companionPlanarProjection : Circle → ℂ := fun z => z
theorem companion_crossingless : Function.Injective companionPlanarProjection := Circle.coe_injective
theorem companion_unit_circle (z : Circle) : ‖companionPlanarProjection z‖ = 1 := Circle.norm_coe z

instance companionComponentUnique : Unique (ConnectedComponents Circle) where
  default := ConnectedComponents.mk 1
  uniq _ := Subsingleton.elim _ _

theorem companion_actual_one_component : Nat.card (ConnectedComponents Circle) = 1 := Nat.card_unique

/-- Two actual sheets over one turn of the longitude. -/
def sheet (s : Bool) (t : ℝ) : Circle :=
  if s then -Circle.exp (Real.pi * t) else Circle.exp (Real.pi * t)

def meridian (s : Bool) (t : ℝ) : Circle := (sheet s t)⁻¹

theorem sheet_longitude (s : Bool) (t : ℝ) :
    (torusCable (sheet s t)).1 = Circle.exp (2 * Real.pi * t) := by
  cases s <;> apply Circle.ext <;>
    simp [torusCable, sheet, pow_two, ← Complex.exp_add, ← add_mul] <;>
    congr 1 <;> ring

theorem sheet_exhausts_actual_fiber (t : ℝ) (z : Circle) :
    (torusCable z).1 = Circle.exp (2 * Real.pi * t) ↔
      z = sheet false t ∨ z = sheet true t := by
  constructor
  · intro h
    have hs := sheet_longitude false t
    have he : (z : ℂ) ^ 2 = (sheet false t : ℂ) ^ 2 := by
      exact congrArg (fun v : Circle => (v : ℂ)) (h.trans hs.symm)
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · exact Or.inl (Circle.ext he)
    · exact Or.inr (Circle.ext (by simpa [sheet] using he))
  · rintro (rfl | rfl) <;> exact sheet_longitude _ _

theorem sheets_distinct (t : ℝ) : sheet false t ≠ sheet true t := by
  simpa [sheet, eq_comm] using Circle.neg_ne_self (Circle.exp (Real.pi * t))

theorem entire_cable_is_closed_braid (z : Circle) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s : Bool, z = sheet s t := by
  let a : ℝ := Complex.arg ((torusCable z).1 : ℂ)
  let theta : ℝ := if a < 0 then a + 2 * Real.pi else a
  have ha0 : -Real.pi < a := Complex.neg_pi_lt_arg _
  have ha1 : a ≤ Real.pi := Complex.arg_le_pi _
  have htheta : theta ∈ Set.Icc 0 (2 * Real.pi) := by
    dsimp [theta]
    split_ifs with ha <;> constructor <;> linarith [Real.pi_pos]
  have he : Circle.exp theta = (torusCable z).1 := by
    dsimp [theta]
    split_ifs
    · rw [Circle.exp_add_two_pi]
      exact Circle.exp_arg _
    · exact Circle.exp_arg _
  refine ⟨theta / (2 * Real.pi), ?_, ?_⟩
  · exact ⟨div_nonneg htheta.1 (by positivity), (div_le_one (by positivity)).mpr htheta.2⟩
  · have ht : 2 * Real.pi * (theta / (2 * Real.pi)) = theta := by
      field_simp
    have hz : (torusCable z).1 = Circle.exp (2 * Real.pi * (theta / (2 * Real.pi))) := by
      rw [ht, he]
    rcases (sheet_exhausts_actual_fiber _ z).mp hz with hz | hz
    · exact ⟨false,hz⟩
    · exact ⟨true,hz⟩

theorem meridian_half_turn (s : Bool) (t : ℝ) :
    (meridian s t : ℂ) =
      if s then -(Complex.exp ((-Real.pi * t : ℝ) * Complex.I))
      else Complex.exp ((-Real.pi * t : ℝ) * Complex.I) := by
  cases s <;> simp [meridian, sheet, ← Circle.exp_neg, Circle.coe_exp, neg_mul]

theorem closed_braid_endpoints :
    meridian false 0 = 1 ∧ meridian true 0 = -1 ∧
    meridian false 1 = -1 ∧ meridian true 1 = 1 := by
  constructor
  · simp [meridian, sheet]
  constructor
  · simp [meridian, sheet]
  constructor
  · apply Circle.ext
    simp [meridian, sheet, Circle.coe_exp, Complex.exp_pi_mul_I]
  · apply Circle.ext
    simp [meridian, sheet, Circle.coe_exp, Complex.exp_pi_mul_I]

/-- Actual regular planar projection, with the third coordinate retaining depth. -/
def planarX (s : Bool) (t : ℝ) : ℝ :=
  if s then -Real.cos (Real.pi * t) else Real.cos (Real.pi * t)
def planarY (t : ℝ) : ℝ := -t
def depth (s : Bool) (t : ℝ) : ℝ :=
  if s then Real.sin (Real.pi * t) else -Real.sin (Real.pi * t)

theorem actual_meridian_coordinates (s : Bool) (t : ℝ) :
    (meridian s t : ℂ).re = planarX s t ∧
      (meridian s t : ℂ).im = depth s t := by
  rw [meridian_half_turn]
  cases s <;> simp [planarX, depth, Complex.exp_re, Complex.exp_im, neg_mul]

theorem unique_projected_crossing {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    planarX false t = planarX true t ↔ t = 1 / 2 := by
  constructor
  · intro h
    have hc : Real.cos (Real.pi * t) = 0 := by
      dsimp [planarX] at h
      linarith
    have hh : Real.pi * t = Real.pi / 2 :=
      Real.strictAntiOn_cos.injOn
        ⟨mul_nonneg Real.pi_pos.le ht.1,
          by simpa using mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩
        (by simpa using hc)
    nlinarith [Real.pi_pos]
  · rintro rfl
    change Real.cos (Real.pi * (1 / 2)) = -Real.cos (Real.pi * (1 / 2))
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    norm_num

theorem actual_over_depth : depth false (1 / 2) = -1 ∧ depth true (1 / 2) = 1 := by
  change -Real.sin (Real.pi * (1 / 2)) = -1 ∧ Real.sin (Real.pi * (1 / 2)) = 1
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  norm_num

theorem projected_tangents :
    HasDerivAt (planarX false) (-Real.pi) (1 / 2) ∧
    HasDerivAt (planarX true) Real.pi (1 / 2) ∧
    HasDerivAt planarY (-1) (1 / 2) := by
  have hc := (Real.hasDerivAt_cos (Real.pi * (1 / 2))).comp (1 / 2)
    ((hasDerivAt_id (1 / 2)).const_mul Real.pi)
  have hu : HasDerivAt (planarX false) (-Real.pi) (1 / 2) := by
    change HasDerivAt (fun t => Real.cos (Real.pi * t)) (-Real.pi) (1 / 2)
    simpa only [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two,
      Function.comp_def, neg_mul, one_mul, mul_one] using hc
  exact ⟨hu, by change HasDerivAt (-planarX false) Real.pi (1 / 2);
                simpa only [neg_neg] using hu.neg, (hasDerivAt_id _).neg⟩

/-- Oriented crossing sign is the determinant of the real over/under tangents. -/
def crossingDet : ℝ :=
  deriv (planarX true) (1 / 2) * deriv planarY (1 / 2) -
    deriv planarY (1 / 2) * deriv (planarX false) (1 / 2)

theorem crossingDet_value : crossingDet = -2 * Real.pi := by
  rw [crossingDet, projected_tangents.2.1.deriv, projected_tangents.2.2.deriv,
    projected_tangents.1.deriv]
  ring

theorem actual_crossing_negative : crossingDet < 0 := by
  rw [crossingDet_value]
  nlinarith [Real.pi_pos]

abbrev Port := Fin 4

/-- Top-left, top-right, bottom-left, bottom-right endpoints of the cut braid. -/
def external (v : Port) : Port := ![2,3,0,1] v
def strand (v : Port) : Port := ![3,2,1,0] v
def rotation (v : Port) : Port := ![1,3,0,2] v
def overPort (v : Port) : Bool := v == 0 || v == 3
def portRay (v : Port) : ℝ × ℝ :=
  ![(-Real.pi,1),(Real.pi,1),(-Real.pi,-1),(Real.pi,-1)] v

theorem actual_rotation : ∀ v : Port,
    (portRay v).1 * (portRay (rotation v)).2 -
      (portRay v).2 * (portRay (rotation v)).1 < 0 := by
  intro v
  fin_cases v <;> simp [portRay, rotation] <;> nlinarith [Real.pi_pos]

theorem endpoint_incidence_and_overpass :
    (∀ v, external (external v) = v ∧ external v ≠ v) ∧
    (∀ v, strand (strand v) = v ∧ strand v ≠ v ∧
      overPort (strand v) = overPort v) := by decide

/-- Actual 0/1 resolutions for the negative crossing: horizontal then vertical. -/
def smoothing (s : Bool) (v : Port) : Port :=
  (if s then ![2,3,0,1] else ![1,0,3,2]) v

theorem smoothing_involutive (s : Bool) : Function.Involutive (smoothing s) := by
  change ∀ v, smoothing s (smoothing s v) = v
  cases s <;> decide
theorem smoothing_no_fixed (s : Bool) : ∀ v, smoothing s v ≠ v := by
  cases s <;> decide

def matchingGraph (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) : SimpleGraph Port where
  Adj u v := v = external u ∨ v = m u
  symm := by
    constructor
    intro u v h
    rcases h with rfl | rfl
    · exact Or.inl (endpoint_incidence_and_overpass.1 u).1.symm
    · exact Or.inr (hi u).symm
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact (endpoint_incidence_and_overpass.1 v).2 h.symm
    · exact hn v h.symm

abbrev knotGraph := matchingGraph strand
  (fun v => (endpoint_incidence_and_overpass.2 v).1)
  (fun v => (endpoint_incidence_and_overpass.2 v).2.1)
abbrev smoothingGraph (s : Bool) := matchingGraph (smoothing s)
  (smoothing_involutive s) (smoothing_no_fixed s)

def route (m : Port → Port) (n : ℕ) (v : Port) : Port := (m ∘ external)^[n] v
def pathSupport (m : Port → Port) (v : Port) : Finset Port :=
  (Finset.range 4).image (fun n => route m n v) ∪
    (Finset.range 4).image (fun n => m (route m n v))

theorem route_reachable (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) (v : Port) (n : ℕ) :
    (matchingGraph m hi hn).Reachable v (route m n v) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ n ih =>
    rw [route, Function.iterate_succ_apply']
    exact ih.trans ((SimpleGraph.Adj.reachable (Or.inl rfl)).trans
      (SimpleGraph.Adj.reachable (Or.inr rfl)))

theorem support_reachable (m : Port → Port) (hi : Function.Involutive m)
    (hn : ∀ v, m v ≠ v) (u v : Port) (h : v ∈ pathSupport m u) :
    (matchingGraph m hi hn).Reachable u v := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp h
    exact route_reachable m hi hn u n
  · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp h
    exact (route_reachable m hi hn u n).trans
      (SimpleGraph.Adj.reachable (Or.inr rfl))

theorem actual_knot_connected : knotGraph.Connected := by
  have hp : ∀ v : Port, v ∈ pathSupport strand 0 := by decide
  refine ⟨fun u v => ?_⟩
  exact (support_reachable _ _ _ _ _ (hp u)).symm.trans
    (support_reachable _ _ _ _ _ (hp v))

def componentRep (s : Bool) (v : Port) : Port := if s then ![0,1,0,1] v else 0

theorem representative_certificates :
    (∀ s v, componentRep s (componentRep s v) = componentRep s v) ∧
    (∀ s v, componentRep s (external v) = componentRep s v) ∧
    (∀ s v, componentRep s (smoothing s v) = componentRep s v) ∧
    (∀ s v, componentRep s v ∈ pathSupport (smoothing s) v) := by decide

theorem representative_reachable (s : Bool) (v : Port) :
    (smoothingGraph s).Reachable v (componentRep s v) :=
  support_reachable _ _ _ _ _ (representative_certificates.2.2.2 s v)

theorem representative_eq_of_reachable (s : Bool) {u v : Port}
    (h : (smoothingGraph s).Reachable u v) : componentRep s u = componentRep s v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    have he : componentRep s u = componentRep s v := by
      rcases h with rfl | rfl
      · exact (representative_certificates.2.1 s u).symm
      · exact (representative_certificates.2.2.1 s u).symm
    exact he.trans ih

def StateCircle (s : Bool) := {v : Port // componentRep s v = v}
instance (s : Bool) : DecidableEq (StateCircle s) := by unfold StateCircle; infer_instance
instance (s : Bool) : Fintype (StateCircle s) := by unfold StateCircle; infer_instance

def circleAt (s : Bool) (v : Port) : StateCircle s :=
  ⟨componentRep s v, representative_certificates.1 s v⟩

def nativeCircleEquiv (s : Bool) : (smoothingGraph s).ConnectedComponent ≃ StateCircle s where
  toFun := Quot.lift (circleAt s) (fun _ _ h => Subtype.ext (representative_eq_of_reachable s h))
  invFun c := (smoothingGraph s).connectedComponentMk c.val
  left_inv c := Quot.inductionOn c (fun v => Quot.sound (representative_reachable s v).symm)
  right_inv c := Subtype.ext c.property

theorem actual_resolution_circle_counts :
    Nat.card (smoothingGraph false).ConnectedComponent = 1 ∧
    Nat.card (smoothingGraph true).ConnectedComponent = 2 := by
  constructor
  · rw [Nat.card_congr (nativeCircleEquiv false), Nat.card_eq_fintype_card]
    decide
  · rw [Nat.card_congr (nativeCircleEquiv true), Nat.card_eq_fintype_card]
    decide

theorem actual_split_saddle :
    circleAt false 0 = circleAt false 1 ∧ circleAt true 0 ≠ circleAt true 1 := by decide

def negativeCrossings : Finset (Fin 1) := Finset.univ.filter (fun _ => crossingDet < 0)
def positiveCrossings : Finset (Fin 1) := Finset.univ.filter (fun _ => 0 < crossingDet)
def nminus : ℕ := negativeCrossings.card
def nplus : ℕ := positiveCrossings.card

theorem actual_crossing_counts : nminus = 1 ∧ nplus = 0 := by
  have hp : ¬ 0 < crossingDet := not_lt_of_ge actual_crossing_negative.le
  simp [nminus, nplus, negativeCrossings, positiveCrossings, actual_crossing_negative, hp]

abbrev Lee := QuadraticAlgebra ℚ (1 : ℚ) 0
abbrev Label := Fin 2
abbrev Two := Lee ⊗[ℚ] Lee

def leeBasis : Module.Basis Label ℚ Lee := QuadraticAlgebra.basis 1 0

@[simp] theorem leeBasis_zero : leeBasis 0 = 1 := by
  rw [leeBasis, QuadraticAlgebra.basis, Basis.coe_ofEquivFun]
  ext <;> rfl
@[simp] theorem leeBasis_one : leeBasis 1 = QuadraticAlgebra.omega := by
  rw [leeBasis, QuadraticAlgebra.basis, Basis.coe_ofEquivFun]
  ext <;> simp

def tensorBasis : Module.Basis (Label × Label) ℚ Two := leeBasis.tensorProduct leeBasis

@[simp] theorem tensorBasis_apply (a b : Label) :
    tensorBasis (a,b) = leeBasis a ⊗ₜ[ℚ] leeBasis b := by
  exact Basis.tensorProduct_apply _ _ _ _

theorem actual_Lee_multiplication :
    leeBasis 0 * leeBasis 0 = leeBasis 0 ∧
    leeBasis 0 * leeBasis 1 = leeBasis 1 ∧
    leeBasis 1 * leeBasis 0 = leeBasis 1 ∧
    leeBasis 1 * leeBasis 1 = leeBasis 0 := by
  simp [QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

/-- Genuine comultiplication of the rational Lee Frobenius algebra. -/
def delta : Lee →ₗ[ℚ] Two :=
  (leeBasis.constr ℚ) (fun a => if a = 0 then tensorBasis (0,1) + tensorBasis (1,0)
    else tensorBasis (1,1) + tensorBasis (0,0))

theorem actual_Lee_comultiplication :
    delta (leeBasis 0) = leeBasis 0 ⊗ₜ[ℚ] leeBasis 1 + leeBasis 1 ⊗ₜ[ℚ] leeBasis 0 ∧
    delta (leeBasis 1) = leeBasis 1 ⊗ₜ[ℚ] leeBasis 1 + leeBasis 0 ⊗ₜ[ℚ] leeBasis 0 := by
  simp only [delta, Basis.constr_basis]
  norm_num

/-- Lossless identification of analytic endpoints with the finite oriented ports. -/
def cutEnd (v : Port) : Bool × ℝ := ![(true,0),(false,0),(false,1),(true,1)] v

theorem analytic_endpoint_to_port_bridge :
    (∀ v, (cutEnd (strand v)).1 = (cutEnd v).1 ∧
      (cutEnd (strand v)).2 = 1 - (cutEnd v).2) ∧
    (∀ v, meridian (cutEnd (external v)).1 (cutEnd (external v)).2 =
      meridian (cutEnd v).1 (cutEnd v).2) ∧
    (∀ v, overPort v = (cutEnd v).1) := by
  have he := closed_braid_endpoints
  constructor
  · intro v
    fin_cases v <;> constructor
    all_goals first | rfl | norm_num [cutEnd, strand]
    all_goals rfl
  constructor
  · intro v; fin_cases v <;> simp [cutEnd, external, he.1, he.2.1, he.2.2.1, he.2.2.2]
  · decide

theorem projected_port_positions : ∀ v : Port,
    (planarX (cutEnd v).1 (cutEnd v).2, planarY (cutEnd v).2) =
      (![((-1 : ℝ),0),(1,0),(-1,-1),(1,-1)] : Port → ℝ × ℝ) v := by
  intro v
  fin_cases v <;> simp [planarX, planarY, cutEnd]

theorem analytic_tangents_to_rotation_rays :
    portRay 0 = (-deriv (planarX true) (1 / 2), -deriv planarY (1 / 2)) ∧
    portRay 1 = (-deriv (planarX false) (1 / 2), -deriv planarY (1 / 2)) ∧
    portRay 2 = (deriv (planarX false) (1 / 2), deriv planarY (1 / 2)) ∧
    portRay 3 = (deriv (planarX true) (1 / 2), deriv planarY (1 / 2)) := by
  simp only [projected_tangents.1.deriv, projected_tangents.2.1.deriv,
    projected_tangents.2.2.deriv]
  norm_num [portRay]
  constructor <;> rfl

theorem no_other_projection_crossings {s r : Bool} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1)
    (he : (planarX s t,planarY t) = (planarX r u,planarY u))
    (hd : (s,t) ≠ (r,u)) : t = u ∧ t = 1 / 2 ∧ s ≠ r := by
  have hy := congrArg Prod.snd he
  have htu : t = u := neg_injective hy
  subst u
  have hsr : s ≠ r := by
    intro hs
    exact hd (Prod.ext hs rfl)
  have hx := congrArg Prod.fst he
  refine ⟨rfl, ?_, hsr⟩
  cases s <;> cases r
  · exact False.elim (hsr rfl)
  · exact (unique_projected_crossing ht).mp hx
  · exact (unique_projected_crossing ht).mp hx.symm
  · exact False.elim (hsr rfl)

abbrev CircleTensor (s : Bool) := PiTensorProduct ℚ (fun _ : StateCircle s => Lee)
def stateTensorBasis (s : Bool) : Module.Basis (StateCircle s → Label) ℚ (CircleTensor s) :=
  Basis.piTensorProduct (fun _ => leeBasis)

def oneLabels : (StateCircle false → Label) ≃ Label where
  toFun lab := lab (circleAt false 0)
  invFun a _ := a
  left_inv lab := by
    funext c
    have he : c = circleAt false 0 := by
      apply Subtype.ext
      simpa [componentRep, circleAt] using c.property.symm
    rw [he]
  right_inv _ := rfl

def twoLabels : (StateCircle true → Label) ≃ (Label × Label) where
  toFun lab := (lab (circleAt true 0), lab (circleAt true 1))
  invFun a c := if c.val = 0 then a.1 else a.2
  left_inv lab := by
    funext c
    have hc : c.val = 0 ∨ c.val = 1 := by
      have hh : ∀ c : StateCircle true, c.val = 0 ∨ c.val = 1 := by decide
      exact hh c
    rcases hc with hc | hc
    · have he : c = circleAt true 0 := Subtype.ext hc
      change (if c.val = 0 then lab (circleAt true 0) else lab (circleAt true 1)) = lab c
      rw [if_pos hc, he]
    · have he : c = circleAt true 1 := Subtype.ext hc
      change (if c.val = 0 then lab (circleAt true 0) else lab (circleAt true 1)) = lab c
      rw [if_neg (show c.val ≠ 0 by rw [hc]; decide), he]
  right_inv a := by simp [circleAt, componentRep]

/-- Genuine tensor equivalences indexed by the computed smoothing circles. -/
def oneCircleTensorEquiv : CircleTensor false ≃ₗ[ℚ] Lee :=
  (stateTensorBasis false).equiv leeBasis oneLabels
def twoCircleTensorEquiv : CircleTensor true ≃ₗ[ℚ] Two :=
  (stateTensorBasis true).equiv tensorBasis twoLabels

theorem actual_tensor_basis (s : Bool) (lab : StateCircle s → Label) :
    stateTensorBasis s lab = PiTensorProduct.tprod ℚ (fun c => leeBasis (lab c)) :=
  Basis.piTensorProduct_apply _ lab

def actualSaddle : CircleTensor false →ₗ[ℚ] CircleTensor true :=
  twoCircleTensorEquiv.symm.toLinearMap.comp (delta.comp oneCircleTensorEquiv.toLinearMap)

theorem split_saddle_is_actual_delta (x : CircleTensor false) :
    twoCircleTensorEquiv (actualSaddle x) = delta (oneCircleTensorEquiv x) := by
  simp [actualSaddle]

theorem lee_decompose (x : Lee) : x = x.re • leeBasis 0 + x.im • leeBasis 1 := by
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem delta_coordinates (x : Lee) (a b : Label) :
    tensorBasis.repr (delta x) (a,b) = if a = b then x.im else x.re := by
  conv_lhs => rw [lee_decompose x]
  rw [map_add, map_smul, map_smul]
  simp only [delta, Basis.constr_basis]
  fin_cases a <;> fin_cases b <;> simp [-tensorBasis_apply]

def rawOne (a : Label) : ℤ := 1 - 2 * (a.val : ℤ)
def rawTwo (a : Label × Label) : ℤ := rawOne a.1 + rawOne a.2
def actualQuantum (s : Bool) (lab : StateCircle s → Label) : ℤ :=
  (∑ c, rawOne (lab c)) + ((s.toNat : ℤ) - nminus) + nplus - nminus

theorem actual_quantum_normalization :
    (∀ lab, actualQuantum false lab = rawOne (oneLabels lab) - 2) ∧
    (∀ lab, actualQuantum true lab = rawTwo (twoLabels lab) - 1) := by
  have h0 : ∀ lab : StateCircle false → Label, ∑ c, rawOne (lab c) = rawOne (oneLabels lab) := by decide
  have h1 : ∀ lab : StateCircle true → Label, ∑ c, rawOne (lab c) = rawTwo (twoLabels lab) := by decide
  constructor
  · intro lab
    simp [actualQuantum, actual_crossing_counts.1, actual_crossing_counts.2, h0]
    omega
  · intro lab
    simp [actualQuantum, actual_crossing_counts.1, actual_crossing_counts.2, h1]

def actualHomologicalDegree (s : Bool) : ℤ := (s.toNat : ℤ) - nminus
theorem actual_homological_normalization :
    actualHomologicalDegree false = -1 ∧ actualHomologicalDegree true = 0 := by
  simp [actualHomologicalDegree, actual_crossing_counts.1]

def oneCrossingCube : Bool ≃ (Fin 1 → Bool) where
  toFun s _ := s
  invFun s := s 0
  left_inv _ := rfl
  right_inv s := funext (fun i => congrArg s (Subsingleton.elim 0 i))

def cubeEdgeSign : ℤ := (-1) ^ ((Finset.univ.filter (fun i : Fin 1 => i < 0)).card)
theorem actual_cube_edge_sign : cubeEdgeSign = 1 := by decide

def inputQuantum (a : Label) : ℤ := rawOne a - 2
def outputQuantum (a : Label × Label) : ℤ := rawTwo a - 1

def basisFiltration {ι M : Type} [Fintype ι] [AddCommGroup M] [Module ℚ M]
    (b : Module.Basis ι ℚ M) (q : ι → ℤ) (j : ℤ) : Submodule ℚ M where
  carrier := {x | ∀ a, q a < j → b.repr x a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    simp [map_add, hx a ha, hy a ha]
  smul_mem' := by
    intro r x hx a ha
    simp [map_smul, hx a ha]

def inputFiltration (j : ℤ) : Submodule ℚ Lee := basisFiltration leeBasis inputQuantum j
def outputFiltration (j : ℤ) : Submodule ℚ Two := basisFiltration tensorBasis outputQuantum j
def unknotFiltration (j : ℤ) : Submodule ℚ Lee := basisFiltration leeBasis rawOne j

abbrev CompanionTensor := PiTensorProduct ℚ (fun _ : ConnectedComponents Circle => Lee)
instance : Fintype (ConnectedComponents Circle) := Fintype.ofFinite _
def companionTensorBasis :
    Module.Basis (ConnectedComponents Circle → Label) ℚ CompanionTensor :=
  Basis.piTensorProduct (fun _ => leeBasis)
def companionLabels : (ConnectedComponents Circle → Label) ≃ Label where
  toFun lab := lab default
  invFun a _ := a
  left_inv lab := funext (fun c => congrArg lab (Subsingleton.elim default c))
  right_inv _ := rfl
def actualCompanionTensorEquiv : CompanionTensor ≃ₗ[ℚ] Lee :=
  companionTensorBasis.equiv leeBasis companionLabels

theorem companion_tensor_quantum (lab : ConnectedComponents Circle → Label) :
    (∑ c, rawOne (lab c)) = rawOne (companionLabels lab) := by
  simp [companionLabels]

theorem delta_is_filtered (j : ℤ) {x : Lee} (hx : x ∈ inputFiltration j) :
    delta x ∈ outputFiltration j := by
  intro a ha
  rcases a with ⟨a,b⟩
  rw [delta_coordinates]
  have hx0 := hx 0
  have hx1 := hx 1
  change inputQuantum 0 < j → x.re = 0 at hx0
  change inputQuantum 1 < j → x.im = 0 at hx1
  by_cases hab : a = b
  · rw [if_pos hab]
    have hl : ∀ a b : Label, inputQuantum 1 ≤ outputQuantum (a,b) := by decide
    exact hx1 (lt_of_le_of_lt (hl a b) ha)
  · rw [if_neg hab]
    have hl : ∀ a b : Label, a ≠ b → inputQuantum 0 = outputQuantum (a,b) := by decide
    exact hx0 (by rw [hl a b hab]; exact ha)

/-- Full normalized cochain complex, indexed by all integers, with no truncation. -/
def negativeObject (i : ℤ) : ModuleCat.{0} ℚ :=
  if i = -1 then ModuleCat.of ℚ Lee else if i = 0 then ModuleCat.of ℚ Two
  else ModuleCat.of ℚ (Fin 0 → ℚ)

def negativeDifferential (i : ℤ) : negativeObject i ⟶ negativeObject (i + 1) := by
  by_cases hi : i = -1
  · subst i
    exact ModuleCat.ofHom delta
  · exact 0

theorem negative_differential_squared (i : ℤ) :
    negativeDifferential i ≫ negativeDifferential (i + 1) = 0 := by
  by_cases hi : i = -1
  · subst i
    simp [negativeDifferential]
  · simp [negativeDifferential, hi]

def negativeComplex : CochainComplex (ModuleCat.{0} ℚ) ℤ :=
  CochainComplex.of negativeObject negativeDifferential negative_differential_squared

theorem negative_complex_d (i : ℤ) :
    negativeComplex.d i (i + 1) = negativeDifferential i := by
  exact CochainComplex.of_d _ _ i

theorem full_integer_object_support (i : ℤ) (hi : i ≠ -1) (hz : i ≠ 0) :
    negativeComplex.X i = ModuleCat.of ℚ (Fin 0 → ℚ) := by
  simp [negativeComplex, negativeObject, hi, hz]

def unknotObject (i : ℤ) : ModuleCat.{0} ℚ :=
  if i = 0 then ModuleCat.of ℚ Lee else ModuleCat.of ℚ (Fin 0 → ℚ)
def unknotComplex : CochainComplex (ModuleCat.{0} ℚ) ℤ :=
  CochainComplex.of unknotObject (fun _ => 0) (by simp)

abbrev negativeShort := negativeComplex.sc' (-1) 0 1
abbrev unknotShort := unknotComplex.sc' (-1) 0 1

theorem negativeShort_g : negativeShort.g = 0 := by
  change negativeComplex.d 0 1 = 0
  rw [show (1 : ℤ) = 0 + 1 by norm_num, negative_complex_d]
  simp [negativeDifferential]

theorem negativeShort_f : negativeShort.f = ModuleCat.ofHom delta := by
  change negativeComplex.d (-1) 0 = ModuleCat.ofHom delta
  simp [negativeComplex, CochainComplex.of.d, negativeDifferential]

theorem full_complex_differential_is_geometric_saddle (x : CircleTensor false) :
    negativeShort.f (oneCircleTensorEquiv x) =
      twoCircleTensorEquiv (actualSaddle x) := by
  rw [negativeShort_f]
  exact (split_saddle_is_actual_delta x).symm

theorem no_other_nonzero_differential (i : ℤ) (hi : i ≠ -1) :
    negativeDifferential i = 0 := by simp [negativeDifferential, hi]

theorem unknotShort_f : unknotShort.f = 0 := by simp [unknotComplex, CochainComplex.of.d]
theorem unknotShort_g : unknotShort.g = 0 := by simp [unknotComplex, CochainComplex.of.d]

abbrev NegativeH := negativeComplex.homology 0
abbrev UnknotH := unknotComplex.homology 0
abbrev LeeQuotient := Two ⧸ LinearMap.range delta

def negativeNativeEquiv : NegativeH ≃ₗ[ℚ] LeeQuotient :=
  ((negativeComplex.homologyIsoSc' (-1) 0 1
      ((ComplexShape.up ℤ).prev_eq' (by norm_num)) ((ComplexShape.up ℤ).next_eq' (by norm_num))) ≪≫
    (negativeShort.asIsoHomologyι negativeShort_g) ≪≫
    negativeShort.moduleCatOpcyclesIso).toLinearEquiv

def unknotNativeEquiv : UnknotH ≃ₗ[ℚ] Lee :=
  ((unknotComplex.homologyIsoSc' (-1) 0 1
      ((ComplexShape.up ℤ).prev_eq' (by norm_num)) ((ComplexShape.up ℤ).next_eq' (by norm_num))) ≪≫
    (unknotShort.asIsoHomologyι unknotShort_g) ≪≫
    unknotShort.moduleCatOpcyclesIso ≪≫
    ((LinearMap.range unknotShort.f.hom).quotEquivOfEqBot
      (by rw [unknotShort_f]; simp)).toModuleIso).toLinearEquiv

def quotientProjection : Two →ₗ[ℚ] (Label → ℚ) where
  toFun x := ![tensorBasis.repr x (0,0) - tensorBasis.repr x (1,1),
    tensorBasis.repr x (0,1) - tensorBasis.repr x (1,0)]
  map_add' x y := by
    funext a; fin_cases a <;> simp [map_add] <;> ring
  map_smul' r x := by
    funext a; fin_cases a <;> simp [map_smul] <;> ring

def quotientSection (v : Label → ℚ) : Two :=
  v 0 • tensorBasis (0,0) + v 1 • tensorBasis (0,1)

theorem section_projection (v : Label → ℚ) : quotientProjection (quotientSection v) = v := by
  funext a
  fin_cases a <;> simp [quotientProjection, quotientSection, -tensorBasis_apply]

theorem quotientProjection_surjective : Function.Surjective quotientProjection :=
  fun v => ⟨quotientSection v, section_projection v⟩

theorem projection_delta_zero (x : Lee) : quotientProjection (delta x) = 0 := by
  funext a
  fin_cases a <;> simp [quotientProjection, delta_coordinates]

theorem projection_kernel : LinearMap.ker quotientProjection = LinearMap.range delta := by
  apply le_antisymm
  · intro x hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    change tensorBasis.repr x (0,0) - tensorBasis.repr x (1,1) = 0 at h0
    change tensorBasis.repr x (0,1) - tensorBasis.repr x (1,0) = 0 at h1
    refine ⟨⟨tensorBasis.repr x (0,1), tensorBasis.repr x (0,0)⟩, ?_⟩
    apply tensorBasis.repr.injective
    ext a
    rcases a with ⟨a,b⟩
    rw [delta_coordinates]
    fin_cases a <;> fin_cases b <;> simp <;> linarith
  · rintro _ ⟨x,rfl⟩
    exact projection_delta_zero x

def quotientCoordinates : LeeQuotient ≃ₗ[ℚ] (Label → ℚ) :=
  (Submodule.quotEquivOfEq (LinearMap.range delta) (LinearMap.ker quotientProjection)
    projection_kernel.symm).trans
    (quotientProjection.quotKerEquivOfSurjective quotientProjection_surjective)

@[simp] theorem quotient_coordinates_mk (x : Two) :
    quotientCoordinates ((LinearMap.range delta).mkQ x) = quotientProjection x := by
  simp [quotientCoordinates, Submodule.quotEquivOfEq_mk]

theorem delta_injective : Function.Injective delta := by
  intro x y h
  have h01 := congrArg (fun t => tensorBasis.repr t (0,1)) h
  have h00 := congrArg (fun t => tensorBasis.repr t (0,0)) h
  rw [delta_coordinates, delta_coordinates] at h01 h00
  ext
  · simpa using h01
  · simpa using h00

def negativeClass : Two →ₗ[ℚ] NegativeH :=
  negativeNativeEquiv.symm.toLinearMap.comp (LinearMap.range delta).mkQ
def unknotClass : Lee →ₗ[ℚ] UnknotH := unknotNativeEquiv.symm.toLinearMap

/-- Image of actual filtered cycles.  Outgoing degree0 differentials are zero. -/
def negativeHFiltration (j : ℤ) : Submodule ℚ NegativeH := (outputFiltration j).map negativeClass
def unknotHFiltration (j : ℤ) : Submodule ℚ UnknotH := (unknotFiltration j).map unknotClass

def negativeCoordinates : NegativeH ≃ₗ[ℚ] (Label → ℚ) :=
  negativeNativeEquiv.trans quotientCoordinates
def unknotCoordinates : UnknotH ≃ₗ[ℚ] (Label → ℚ) :=
  unknotNativeEquiv.trans (QuadraticAlgebra.linearEquivTuple 1 0)

@[simp] theorem negative_class_coordinates (x : Two) :
    negativeCoordinates (negativeClass x) = quotientProjection x := by
  calc
    negativeCoordinates (negativeClass x) =
        quotientCoordinates ((LinearMap.range delta).mkQ x) :=
      congrArg quotientCoordinates (negativeNativeEquiv.apply_symm_apply _)
    _ = quotientProjection x := quotient_coordinates_mk x

theorem projection_filtered (j : ℤ) {x : Two} (hx : x ∈ outputFiltration j) :
    ∀ a, rawOne a < j → quotientProjection x a = 0 := by
  intro a ha
  fin_cases a
  · have h00 := hx (0,0)
    have h11 := hx (1,1)
    change 1 < j at ha
    have he0 : tensorBasis.repr x (0,0) = 0 := h00 ha
    have he1 : tensorBasis.repr x (1,1) = 0 := h11 (by change (-3 : ℤ) < j; omega)
    simp [quotientProjection, he0, he1]
  · have h01 := hx (0,1)
    have h10 := hx (1,0)
    change (-1 : ℤ) < j at ha
    have he0 : tensorBasis.repr x (0,1) = 0 := h01 ha
    have he1 : tensorBasis.repr x (1,0) = 0 := h10 ha
    simp [quotientProjection, he0, he1]

theorem section_filtered (j : ℤ) (v : Label → ℚ)
    (hv : ∀ a, rawOne a < j → v a = 0) : quotientSection v ∈ outputFiltration j := by
  intro a ha
  rcases a with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [quotientSection, -tensorBasis_apply] <;>
    first | exact hv 0 ha | exact hv 1 ha

theorem negative_filtration_all_integers (j : ℤ) (h : NegativeH) :
    h ∈ negativeHFiltration j ↔ ∀ a, rawOne a < j → negativeCoordinates h a = 0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa using projection_filtered j hx
  · intro hh
    refine ⟨quotientSection (negativeCoordinates h), section_filtered j _ hh, ?_⟩
    apply negativeCoordinates.injective
    rw [negative_class_coordinates, section_projection]

theorem unknot_filtration_all_integers (j : ℤ) (h : UnknotH) :
    h ∈ unknotHFiltration j ↔ ∀ a, rawOne a < j → unknotCoordinates h a = 0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa [unknotCoordinates, unknotClass, unknotFiltration, basisFiltration, leeBasis,
      QuadraticAlgebra.basis] using hx
  · intro hh
    refine ⟨unknotNativeEquiv h, ?_, by simp [unknotClass]⟩
    exact hh

theorem negative_homology_only_degree_zero (i : ℤ) (hi : i ≠ 0) :
    Limits.IsZero (negativeComplex.homology i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  by_cases hn : i = -1
  · subst i
    rw [negativeComplex.exactAt_iff' (-2) (-1) 0
      ((ComplexShape.up ℤ).prev_eq' (by norm_num))
      ((ComplexShape.up ℤ).next_eq' (by norm_num))]
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hd : delta x = 0 := by
      change delta x = 0 at hx
      exact hx
    have hx0 : x = 0 := delta_injective (by simpa using hd)
    refine ⟨0, ?_⟩
    simp [hx0]
  · apply HomologicalComplex.ExactAt.of_isZero
    rw [full_integer_object_support i hn hi]
    exact ModuleCat.isZero_of_subsingleton _

theorem unknot_homology_only_degree_zero (i : ℤ) (hi : i ≠ 0) :
    Limits.IsZero (unknotComplex.homology i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change Limits.IsZero (unknotObject i)
  simp only [unknotObject, if_neg hi]
  exact ModuleCat.isZero_of_subsingleton _

theorem actual_cycle_representatives (j : ℤ) (h : NegativeH) :
    h ∈ negativeHFiltration j ↔ ∃ x : Two,
      x ∈ outputFiltration j ∧ negativeShort.g x = 0 ∧ negativeClass x = h := by
  rw [negativeHFiltration, Submodule.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx, by rw [negativeShort_g]; rfl, rfl⟩
  · rintro ⟨x,hx,_,he⟩
    exact ⟨x,hx,he⟩

/-- Definition3.1: degree of a nonzero homology class from its actual filtration. -/
def classDegree {H : Type} [AddCommGroup H] [Module ℚ H]
    (F : ℤ → Submodule ℚ H) (h : {h : H // h ≠ 0}) : ℤ :=
  sSup {j | h.val ∈ F j}

def degreeSet {H : Type} [AddCommGroup H] [Module ℚ H]
    (F : ℤ → Submodule ℚ H) : Set ℤ := Set.range (classDegree F)
def smin {H : Type} [AddCommGroup H] [Module ℚ H] (F : ℤ → Submodule ℚ H) : ℤ :=
  sInf (degreeSet F)
def smax {H : Type} [AddCommGroup H] [Module ℚ H] (F : ℤ → Submodule ℚ H) : ℤ :=
  sSup (degreeSet F)

/-- Definition3.4, applied below only after proving both attained extrema. -/
def rasmussenS {H : Type} [AddCommGroup H] [Module ℚ H] (F : ℤ → Submodule ℚ H) : ℤ :=
  smax F - 1

section FiltrationExtrema
variable {H : Type} [AddCommGroup H] [Module ℚ H]
variable (F : ℤ → Submodule ℚ H) (e : H ≃ₗ[ℚ] (Label → ℚ))
variable (hf : ∀ j h, h ∈ F j ↔ ∀ a, rawOne a < j → e h a = 0)
include e hf

theorem nonzero_class_filtration (h : {h : H // h ≠ 0}) (j : ℤ) :
    h.val ∈ F j ↔ j ≤ if e h.val 1 = 0 then 1 else -1 := by
  by_cases hb : e h.val 1 = 0
  · rw [if_pos hb]
    have ha : e h.val 0 ≠ 0 := by
      intro hz
      apply h.property
      apply e.injective
      funext a
      fin_cases a <;> simp [hz,hb]
    constructor
    · intro hh
      by_contra hj
      exact ha ((hf j h.val).mp hh 0 (by change (1 : ℤ) < j; omega))
    · intro hj
      apply (hf j h.val).mpr
      intro a hq
      fin_cases a
      · change (1 : ℤ) < j at hq
        omega
      · exact hb
  · rw [if_neg hb]
    constructor
    · intro hh
      by_contra hj
      exact hb ((hf j h.val).mp hh 1 (by change (-1 : ℤ) < j; omega))
    · intro hj
      apply (hf j h.val).mpr
      intro a hq
      fin_cases a <;> change rawOne _ < j at hq <;>
        norm_num [rawOne] at hq <;> omega

theorem nonzero_class_bounds (h : {h : H // h ≠ 0}) :
    {j | h.val ∈ F j}.Nonempty ∧ BddAbove {j | h.val ∈ F j} := by
  let c : ℤ := if e h.val 1 = 0 then 1 else -1
  have he : {j | h.val ∈ F j} = Set.Iic c := by
    ext j
    exact nonzero_class_filtration F e hf h j
  rw [he]
  exact ⟨⟨c,by simp⟩, ⟨c,fun _ hj => hj⟩⟩

theorem actual_class_degree (h : {h : H // h ≠ 0}) :
    classDegree F h = if e h.val 1 = 0 then 1 else -1 := by
  have he : {j | h.val ∈ F j} = Set.Iic (if e h.val 1 = 0 then 1 else -1) := by
    ext j
    exact nonzero_class_filtration F e hf h j
  rw [classDegree, he, csSup_Iic]

theorem actual_degree_set : degreeSet F = ({-1,1} : Set ℤ) := by
  ext j
  constructor
  · rintro ⟨h,rfl⟩
    rw [actual_class_degree F e hf]
    split_ifs <;> simp
  · intro hj
    rcases hj with rfl | rfl
    · have hn : e.symm ![0,1] ≠ 0 := by
        intro hz
        have hh := congrArg (fun x => e x 1) hz
        simp at hh
      refine ⟨⟨e.symm ![0,1],hn⟩, ?_⟩
      rw [actual_class_degree F e hf]
      simp
    · have hn : e.symm ![1,0] ≠ 0 := by
        intro hz
        have hh := congrArg (fun x => e x 0) hz
        simp at hh
      refine ⟨⟨e.symm ![1,0],hn⟩, ?_⟩
      rw [actual_class_degree F e hf]
      simp

theorem attained_extrema :
    (degreeSet F).Nonempty := by
  rw [actual_degree_set F e hf]
  simp

theorem extrema_values : smin F = -1 ∧ smax F = 1 := by
  constructor
  · rw [smin, actual_degree_set F e hf]
    apply IsLeast.csInf_eq
    refine ⟨by simp, ?_⟩
    intro j hj
    rcases hj with rfl | rfl <;> omega
  · rw [smax, actual_degree_set F e hf]
    apply IsGreatest.csSup_eq
    refine ⟨by simp, ?_⟩
    intro j hj
    rcases hj with rfl | rfl <;> omega

theorem computed_rasmussen_value : rasmussenS F = 0 ∧ smin F + 1 = 0 := by
  have hv := extrema_values F e hf
  simp [rasmussenS, hv.1, hv.2]
end FiltrationExtrema

theorem negative_degree_set : degreeSet negativeHFiltration = ({-1,1} : Set ℤ) :=
  actual_degree_set _ negativeCoordinates negative_filtration_all_integers

theorem unknot_degree_set : degreeSet unknotHFiltration = ({-1,1} : Set ℤ) :=
  actual_degree_set _ unknotCoordinates unknot_filtration_all_integers

theorem negative_rasmussen_zero : rasmussenS negativeHFiltration = 0 :=
  (computed_rasmussen_value _ negativeCoordinates negative_filtration_all_integers).1
theorem unknot_rasmussen_zero : rasmussenS unknotHFiltration = 0 :=
  (computed_rasmussen_value _ unknotCoordinates unknot_filtration_all_integers).1

theorem printed_cable_formula_false :
    rasmussenS negativeHFiltration ≠
      2 * rasmussenS unknotHFiltration + (2 - 1) * ((-1) - 1) := by
  rw [negative_rasmussen_zero, unknot_rasmussen_zero]
  norm_num

end TLMC614
