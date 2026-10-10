import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp


/-! Actual continuous finite configuration spaces, not a vertex-only proxy. -/
namespace P4110

abbrev OrderedConfig (n : ℕ) (X : Type*) :=
  {f : Fin n → X // Function.Injective f}

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def orderedConfigHomeomorph (n : ℕ) (h : X ≃ₜ Y) :
    OrderedConfig n X ≃ₜ OrderedConfig n Y :=
  (Homeomorph.piCongrRight (fun _ : Fin n => h)).subtype fun f => by
    constructor
    · intro hf
      exact h.injective.comp hf
    · intro hf i j hij
      exact hf (congrArg h hij)

@[simp] theorem orderedConfigHomeomorph_apply (n : ℕ) (h : X ≃ₜ Y)
    (x : OrderedConfig n X) (i : Fin n) :
    (orderedConfigHomeomorph n h x).1 i = h (x.1 i) := rfl

@[simp] theorem orderedConfigHomeomorph_symm_apply (n : ℕ) (h : X ≃ₜ Y)
    (y : OrderedConfig n Y) (i : Fin n) :
    ((orderedConfigHomeomorph n h).symm y).1 i = h.symm (y.1 i) := rfl

def configReindex {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : OrderedConfig n X) : OrderedConfig n X :=
  ⟨x.1 ∘ σ, x.2.comp σ.injective⟩

theorem orderedConfigHomeomorph_equivariant {n : ℕ} (h : X ≃ₜ Y)
    (σ : Equiv.Perm (Fin n)) (x : OrderedConfig n X) :
    orderedConfigHomeomorph n h (configReindex σ x) =
      configReindex σ (orderedConfigHomeomorph n h x) := rfl

def configOrbitSetoid (n : ℕ) (X : Type*) : Setoid (OrderedConfig n X) where
  r x y := ∃ σ : Equiv.Perm (Fin n), ∀ i, y.1 i = x.1 (σ i)
  iseqv := {
    refl := fun x => ⟨Equiv.refl _, fun _ => rfl⟩
    symm := by
      rintro x y ⟨σ, hσ⟩
      refine ⟨σ.symm, fun i => ?_⟩
      simpa using (hσ (σ.symm i)).symm
    trans := by
      rintro x y z ⟨σ, hσ⟩ ⟨τ, hτ⟩
      exact ⟨τ.trans σ, fun i => (hτ i).trans (hσ (τ i))⟩
  }

abbrev UnorderedConfig (n : ℕ) (X : Type*) := Quotient (configOrbitSetoid n X)

theorem configOrbit_preserved (n : ℕ) (h : X ≃ₜ Y) (x y : OrderedConfig n X) :
    (configOrbitSetoid n X).r x y ↔
      (configOrbitSetoid n Y).r (orderedConfigHomeomorph n h x)
        (orderedConfigHomeomorph n h y) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun i => congrArg h (hσ i)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun i => h.injective (hσ i)⟩

def unorderedConfigHomeomorph (n : ℕ) (h : X ≃ₜ Y) :
    UnorderedConfig n X ≃ₜ UnorderedConfig n Y where
  toEquiv := Quotient.congr (orderedConfigHomeomorph n h).toEquiv
    (configOrbit_preserved n h)
  continuous_toFun := continuous_quot_map
    (fun x y => (configOrbit_preserved n h x y).mp)
    (orderedConfigHomeomorph n h).continuous
  continuous_invFun := continuous_quot_map
    (fun x y hxy => by
      rcases hxy with ⟨σ, hσ⟩
      exact ⟨σ, fun i => congrArg h.symm (hσ i)⟩)
    (orderedConfigHomeomorph n h).symm.continuous

#print axioms orderedConfigHomeomorph
#print axioms unorderedConfigHomeomorph
end P4110


/-! A genuine continuous geometric edge model. This is a checked partial;
the connection to every abstract endpoint-gluing graph remains an obligation. -/
namespace P4110Geometry
noncomputable section
open Set
variable {κ : Type*}
abbrev Ambient (κ : Type*) := κ → ℝ

def affinePoint (a b : Ambient κ) (t : ℝ) : Ambient κ :=
  fun i => (1 - t) * a i + t * b i

def edgeSegment (a b : Ambient κ) : Set (Ambient κ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = affinePoint a b t}

theorem affinePoint_left (a b : Ambient κ) : affinePoint a b 0 = a := by
  ext i
  simp [affinePoint]

theorem affinePoint_right (a b : Ambient κ) : affinePoint a b 1 = b := by
  ext i
  simp [affinePoint]

theorem left_mem_edgeSegment (a b : Ambient κ) : a ∈ edgeSegment a b :=
  ⟨0, le_rfl, zero_le_one, (affinePoint_left a b).symm⟩

theorem right_mem_edgeSegment (a b : Ambient κ) : b ∈ edgeSegment a b :=
  ⟨1, zero_le_one, le_rfl, (affinePoint_right a b).symm⟩

theorem edgeSegment_split (a b : Ambient κ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    edgeSegment a b = edgeSegment a (affinePoint a b r) ∪
      edgeSegment (affinePoint a b r) b := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have hmr : 0 < 1 - r := sub_pos.mpr hr1
  have hmrne : 1 - r ≠ 0 := ne_of_gt hmr
  ext x
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    by_cases htr : t ≤ r
    · left
      refine ⟨t / r, div_nonneg ht0 hr0.le, (div_le_one hr0).mpr htr, ?_⟩
      ext i
      simp only [affinePoint]
      field_simp
      ring
    · right
      have hrt : r ≤ t := le_of_lt (lt_of_not_ge htr)
      refine ⟨(t - r) / (1 - r), div_nonneg (sub_nonneg.mpr hrt) hmr.le,
        (div_le_one hmr).mpr (by linarith), ?_⟩
      ext i
      simp only [affinePoint]
      field_simp
      ring
  · rintro (⟨t, ht0, ht1, rfl⟩ | ⟨t, ht0, ht1, rfl⟩)
    · refine ⟨r * t, mul_nonneg hr0.le ht0, ?_, ?_⟩
      · nlinarith
      · ext i
        simp only [affinePoint]
        ring
    · refine ⟨r + (1 - r) * t, ?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · ext i
        simp only [affinePoint]
        ring

structure GeometricGraph (κ : Type*) where
  vertices : Set (Ambient κ)
  edges : Set (Ambient κ × Ambient κ)

def GeometricGraph.realization (G : GeometricGraph κ) : Set (Ambient κ) :=
  G.vertices ∪ {x | ∃ e ∈ G.edges, x ∈ edgeSegment e.1 e.2}

def GeometricGraph.subdivideEdge (G : GeometricGraph κ) (a b : Ambient κ) (r : ℝ) :
    GeometricGraph κ where
  vertices := insert (affinePoint a b r) G.vertices
  edges := insert (a, affinePoint a b r)
    (insert (affinePoint a b r, b) (G.edges \ {(a, b)}))

theorem realization_subdivideEdge (G : GeometricGraph κ) (a b : Ambient κ)
    (he : (a, b) ∈ G.edges) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (G.subdivideEdge a b r).realization = G.realization := by
  have split := edgeSegment_split a b r hr0 hr1
  ext x
  constructor
  · rintro (hx | ⟨e, he', hx⟩)
    · rcases hx with hx | hx
      · right
        refine ⟨(a, b), he, ?_⟩
        exact hx ▸ ⟨r, hr0.le, hr1.le, rfl⟩
      · exact Or.inl hx
    · rcases he' with hnew | hnew | hold
      · subst e
        exact Or.inr ⟨(a, b), he, split.symm ▸ Or.inl hx⟩
      · subst e
        exact Or.inr ⟨(a, b), he, split.symm ▸ Or.inr hx⟩
      · exact Or.inr ⟨e, hold.1, hx⟩
  · rintro (hx | ⟨e, he', hx⟩)
    · exact Or.inl (Or.inr hx)
    · by_cases hab : e = (a, b)
      · subst e
        have hx' : x ∈ edgeSegment a (affinePoint a b r) ∪
            edgeSegment (affinePoint a b r) b := split ▸ hx
        rcases hx' with hx' | hx'
        · exact Or.inr ⟨(a, affinePoint a b r), Or.inl rfl, hx'⟩
        · exact Or.inr ⟨(affinePoint a b r, b), Or.inr (Or.inl rfl), hx'⟩
      · exact Or.inr ⟨e, Or.inr (Or.inr ⟨he', hab⟩), hx⟩

def geometricSubdivisionHomeomorph (G : GeometricGraph κ) (a b : Ambient κ)
    (he : (a, b) ∈ G.edges) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    G.realization ≃ₜ (G.subdivideEdge a b r).realization :=
  Homeomorph.setCongr (realization_subdivideEdge G a b he r hr0 hr1).symm

#print axioms edgeSegment_split
#print axioms realization_subdivideEdge
#print axioms geometricSubdivisionHomeomorph

/-! Standard graph cells with full closed intervals and endpoint identification. -/
structure CellGraph (V E : Type*) where
  source : E → V
  target : E → V

abbrev EdgeInterval := {t : ℝ // 0 ≤ t ∧ t ≤ 1}
def intervalZero : EdgeInterval := ⟨0, le_rfl, zero_le_one⟩
def intervalOne : EdgeInterval := ⟨1, zero_le_one, le_rfl⟩
abbrev CellPoint (V E : Type*) := V ⊕ (Σ _ : E, EdgeInterval)

inductive EndpointRelation {V E : Type*} (G : CellGraph V E) :
    CellPoint V E → CellPoint V E → Prop
  | source (e : E) : EndpointRelation G (.inr ⟨e, intervalZero⟩) (.inl (G.source e))
  | target (e : E) : EndpointRelation G (.inr ⟨e, intervalOne⟩) (.inl (G.target e))

abbrev CellRealization {V E : Type*} (G : CellGraph V E) := Quot (EndpointRelation G)

def CellGraph.coordinateSupport {V E : Type*} (G : CellGraph V E)
    (φ : V → Ambient κ) : Set (Ambient κ) :=
  range φ ∪ {x | ∃ e : E, x ∈ edgeSegment (φ (G.source e)) (φ (G.target e))}

def rawCellCoordinate {V E : Type*} (G : CellGraph V E) (φ : V → Ambient κ) :
    CellPoint V E → Ambient κ :=
  Sum.elim φ (fun p => affinePoint (φ (G.source p.1)) (φ (G.target p.1)) p.2.1)

theorem rawCellCoordinate_mem {V E : Type*} (G : CellGraph V E) (φ : V → Ambient κ)
    (p : CellPoint V E) : rawCellCoordinate G φ p ∈ G.coordinateSupport φ := by
  rcases p with v | ⟨e, t⟩
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨e, t.1, t.2.1, t.2.2, rfl⟩

def rawCellMap {V E : Type*} (G : CellGraph V E) (φ : V → Ambient κ) :
    CellPoint V E → G.coordinateSupport φ :=
  fun p => ⟨rawCellCoordinate G φ p, rawCellCoordinate_mem G φ p⟩

theorem rawCellMap_respects {V E : Type*} (G : CellGraph V E) (φ : V → Ambient κ)
    (a b : CellPoint V E) (h : EndpointRelation G a b) :
    rawCellMap G φ a = rawCellMap G φ b := by
  apply Subtype.ext
  cases h with
  | source e => exact affinePoint_left _ _
  | target e => exact affinePoint_right _ _

def cellCoordinateMap {V E : Type*} (G : CellGraph V E) (φ : V → Ambient κ) :
    CellRealization G → G.coordinateSupport φ :=
  Quot.lift (rawCellMap G φ) (rawCellMap_respects G φ)

variable {V E : Type*} [TopologicalSpace V] [DiscreteTopology V]

theorem continuous_rawCellCoordinate (G : CellGraph V E) (φ : V → Ambient κ) :
    Continuous (rawCellCoordinate G φ) := by
  apply continuous_sumElim.mpr
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_sigma
    intro e
    apply continuous_pi
    intro i
    change Continuous (fun p : EdgeInterval =>
      (1 - p.1) * φ (G.source e) i + p.1 * φ (G.target e) i)
    have hc : Continuous (fun p : EdgeInterval => p.1) := continuous_subtype_val
    exact ((continuous_const.sub hc).mul continuous_const).add (hc.mul continuous_const)

theorem continuous_cellCoordinateMap (G : CellGraph V E) (φ : V → Ambient κ) :
    Continuous (cellCoordinateMap G φ) :=
  continuous_quot_lift (rawCellMap_respects G φ)
    ((continuous_rawCellCoordinate G φ).subtype_mk _)

theorem surjective_cellCoordinateMap {V E : Type*} (G : CellGraph V E)
    (φ : V → Ambient κ) : Function.Surjective (cellCoordinateMap G φ) := by
  rintro ⟨x, hx⟩
  rcases hx with ⟨v, hv⟩ | ⟨e, t, ht0, ht1, ht⟩
  · refine ⟨Quot.mk _ (.inl v), ?_⟩
    apply Subtype.ext
    exact hv
  · refine ⟨Quot.mk _ (.inr ⟨e, ⟨t, ht0, ht1⟩⟩), ?_⟩
    apply Subtype.ext
    exact ht.symm

#print axioms continuous_cellCoordinateMap
#print axioms surjective_cellCoordinateMap

def intervalHalf (t : EdgeInterval) : EdgeInterval :=
  ⟨t.1 / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

def intervalUpper (t : EdgeInterval) : EdgeInterval :=
  ⟨(1 + t.1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

def intervalMid : EdgeInterval := ⟨1 / 2, by norm_num⟩

def CellGraph.subdivideOne {V E : Type*} [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellGraph (V ⊕ Unit) (E ⊕ Unit) where
  source := Sum.elim (fun f => .inl (G.source f)) (fun _ => .inr ())
  target := Sum.elim (fun f => if f = e then .inr () else .inl (G.target f))
    (fun _ => .inl (G.target e))

def rawSubdivisionCollapse {V E : Type*} [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellPoint (V ⊕ Unit) (E ⊕ Unit) → CellRealization G :=
  Sum.elim
    (Sum.elim (fun v => Quot.mk _ (.inl v)) (fun _ => Quot.mk _ (.inr ⟨e, intervalMid⟩)))
    (fun p => match p.1 with
      | .inl f => if f = e then Quot.mk _ (.inr ⟨e, intervalHalf p.2⟩)
        else Quot.mk _ (.inr ⟨f, p.2⟩)
      | .inr _ => Quot.mk _ (.inr ⟨e, intervalUpper p.2⟩))

theorem rawSubdivisionCollapse_respects {V E : Type*} [DecidableEq E]
    (G : CellGraph V E) (e : E) (a b : CellPoint (V ⊕ Unit) (E ⊕ Unit))
    (h : EndpointRelation (G.subdivideOne e) a b) :
    rawSubdivisionCollapse G e a = rawSubdivisionCollapse G e b := by
  cases h with
  | source f =>
    rcases f with f | u
    · by_cases hfe : f = e
      · subst f
        simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inl, Sum.elim_inr, if_pos rfl]
        have hi : intervalHalf intervalZero = intervalZero := by
          apply Subtype.ext
          norm_num [intervalHalf, intervalZero]
        rw [hi]
        exact Quot.sound (EndpointRelation.source e)
      · simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inl, Sum.elim_inr, if_neg hfe]
        exact Quot.sound (EndpointRelation.source f)
    · simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inr, Sum.elim_inl]
      have hi : intervalUpper intervalZero = intervalMid := by
        apply Subtype.ext
        norm_num [intervalUpper, intervalZero, intervalMid]
      rw [hi]
  | target f =>
    rcases f with f | u
    · by_cases hfe : f = e
      · subst f
        simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inl, if_pos rfl,
          Sum.elim_inr]
        rfl
      · simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inl, Sum.elim_inr, if_neg hfe]
        exact Quot.sound (EndpointRelation.target f)
    · simp only [rawSubdivisionCollapse, CellGraph.subdivideOne, Sum.elim_inr, Sum.elim_inl]
      have hi : intervalUpper intervalOne = intervalOne := by apply Subtype.ext; norm_num [intervalUpper, intervalOne]
      rw [hi]
      exact Quot.sound (EndpointRelation.target e)

def subdivisionCollapse {V E : Type*} [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellRealization (G.subdivideOne e) → CellRealization G :=
  Quot.lift (rawSubdivisionCollapse G e) (rawSubdivisionCollapse_respects G e)

theorem continuous_rawSubdivisionCollapse [DecidableEq E] (G : CellGraph V E) (e : E) :
    Continuous (rawSubdivisionCollapse G e) := by
  apply continuous_sumElim.mpr
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_sigma
    rintro (f | u)
    · by_cases hfe : f = e
      · subst f
        simp only [rawSubdivisionCollapse, if_pos rfl]
        apply continuous_quot_mk.comp
        apply continuous_inr.comp
        apply continuous_sigmaMk.comp
        exact (continuous_subtype_val.div_const 2).subtype_mk _
      · simp only [rawSubdivisionCollapse, if_neg hfe]
        exact continuous_quot_mk.comp (continuous_inr.comp continuous_sigmaMk)
    · simp only [rawSubdivisionCollapse]
      apply continuous_quot_mk.comp
      apply continuous_inr.comp
      apply continuous_sigmaMk.comp
      exact ((continuous_const.add continuous_subtype_val).div_const 2).subtype_mk _

theorem continuous_subdivisionCollapse [DecidableEq E] (G : CellGraph V E) (e : E) :
    Continuous (subdivisionCollapse G e) :=
  continuous_quot_lift (rawSubdivisionCollapse_respects G e) (continuous_rawSubdivisionCollapse G e)

#print axioms continuous_subdivisionCollapse

def intervalLowerDouble (t : EdgeInterval) : EdgeInterval :=
  ⟨min 1 (2 * t.1), le_min zero_le_one (by linarith [t.2.1]), min_le_left _ _⟩

def intervalUpperDouble (t : EdgeInterval) : EdgeInterval :=
  ⟨max 0 (2 * t.1 - 1), le_max_left _ _, max_le zero_le_one (by linarith [t.2.2])⟩

theorem subdivision_join [DecidableEq E] (G : CellGraph V E) (e : E) :
    Quot.mk (EndpointRelation (G.subdivideOne e)) (.inr ⟨.inl e, intervalOne⟩) =
      Quot.mk (EndpointRelation (G.subdivideOne e)) (.inr ⟨.inr (), intervalZero⟩) := by
  calc
    _ = Quot.mk (EndpointRelation (G.subdivideOne e)) (.inl (.inr ())) := by
      simpa [CellGraph.subdivideOne] using
        (Quot.sound (EndpointRelation.target (G := G.subdivideOne e) (.inl e)))
    _ = _ := by
      simpa [CellGraph.subdivideOne] using
        (Quot.sound (EndpointRelation.source (G := G.subdivideOne e) (.inr ()))).symm

def splitEdge [DecidableEq E] (G : CellGraph V E) (e : E) (t : EdgeInterval) :
    CellRealization (G.subdivideOne e) :=
  if t.1 ≤ 1 / 2 then Quot.mk _ (.inr ⟨.inl e, intervalLowerDouble t⟩)
    else Quot.mk _ (.inr ⟨.inr (), intervalUpperDouble t⟩)

theorem continuous_splitEdge [DecidableEq E] (G : CellGraph V E) (e : E) :
    Continuous (splitEdge G e) := by
  have hl : Continuous (fun t : EdgeInterval =>
      Quot.mk (EndpointRelation (G.subdivideOne e)) (.inr ⟨.inl e, intervalLowerDouble t⟩)) :=
    continuous_quot_mk.comp (continuous_inr.comp (continuous_sigmaMk.comp
      ((continuous_const.min (continuous_const.mul continuous_subtype_val)).subtype_mk _)))
  have hr : Continuous (fun t : EdgeInterval =>
      Quot.mk (EndpointRelation (G.subdivideOne e)) (.inr ⟨.inr (), intervalUpperDouble t⟩)) :=
    continuous_quot_mk.comp (continuous_inr.comp (continuous_sigmaMk.comp
      ((continuous_const.max ((continuous_const.mul continuous_subtype_val).sub continuous_const)).subtype_mk _)))
  apply hl.if_le hr continuous_subtype_val continuous_const
  intro t ht
  have hlow : intervalLowerDouble t = intervalOne := by
    apply Subtype.ext
    norm_num [intervalLowerDouble, intervalOne, ht]
  have hup : intervalUpperDouble t = intervalZero := by
    apply Subtype.ext
    norm_num [intervalUpperDouble, intervalZero, ht]
  rw [hlow, hup]
  exact subdivision_join G e

@[simp] theorem splitEdge_zero [DecidableEq E] (G : CellGraph V E) (e : E) :
    splitEdge G e intervalZero = Quot.mk _ (.inr ⟨.inl e, intervalZero⟩) := by
  have hi : intervalLowerDouble intervalZero = intervalZero := by
    apply Subtype.ext
    norm_num [intervalLowerDouble, intervalZero]
  unfold splitEdge
  rw [if_pos (by norm_num [intervalZero]), hi]

@[simp] theorem splitEdge_one [DecidableEq E] (G : CellGraph V E) (e : E) :
    splitEdge G e intervalOne = Quot.mk _ (.inr ⟨.inr (), intervalOne⟩) := by
  have hi : intervalUpperDouble intervalOne = intervalOne := by
    apply Subtype.ext
    norm_num [intervalUpperDouble, intervalOne]
  unfold splitEdge
  rw [if_neg (by norm_num [intervalOne]), hi]

def rawSubdivisionExpand [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellPoint V E → CellRealization (G.subdivideOne e) :=
  Sum.elim (fun v => Quot.mk _ (.inl (.inl v)))
    (fun p => if p.1 = e then splitEdge G e p.2 else Quot.mk _ (.inr ⟨.inl p.1, p.2⟩))

theorem rawSubdivisionExpand_respects [DecidableEq E] (G : CellGraph V E) (e : E)
    (a b : CellPoint V E) (h : EndpointRelation G a b) :
    rawSubdivisionExpand G e a = rawSubdivisionExpand G e b := by
  cases h with
  | source f =>
    by_cases hfe : f = e
    · subst f
      simp only [rawSubdivisionExpand, Sum.elim_inr, Sum.elim_inl, if_pos rfl, splitEdge_zero]
      exact Quot.sound (EndpointRelation.source (G := G.subdivideOne e) (.inl e))
    · simp only [rawSubdivisionExpand, Sum.elim_inr, Sum.elim_inl, if_neg hfe]
      exact Quot.sound (EndpointRelation.source (G := G.subdivideOne e) (.inl f))
  | target f =>
    by_cases hfe : f = e
    · subst f
      simp only [rawSubdivisionExpand, Sum.elim_inr, Sum.elim_inl, if_pos rfl, splitEdge_one]
      exact Quot.sound (EndpointRelation.target (G := G.subdivideOne e) (.inr ()))
    · simp only [rawSubdivisionExpand, Sum.elim_inr, Sum.elim_inl, if_neg hfe]
      simpa [CellGraph.subdivideOne, hfe] using
        (Quot.sound (EndpointRelation.target (G := G.subdivideOne e) (.inl f)))

def subdivisionExpand [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellRealization G → CellRealization (G.subdivideOne e) :=
  Quot.lift (rawSubdivisionExpand G e) (rawSubdivisionExpand_respects G e)

theorem continuous_rawSubdivisionExpand [DecidableEq E] (G : CellGraph V E) (e : E) :
    Continuous (rawSubdivisionExpand G e) := by
  apply continuous_sumElim.mpr
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_sigma
    intro f
    by_cases hfe : f = e
    · subst f
      simpa [rawSubdivisionExpand] using continuous_splitEdge G e
    · simp only [rawSubdivisionExpand, if_neg hfe]
      exact continuous_quot_mk.comp (continuous_inr.comp continuous_sigmaMk)

theorem continuous_subdivisionExpand [DecidableEq E] (G : CellGraph V E) (e : E) :
    Continuous (subdivisionExpand G e) :=
  continuous_quot_lift (rawSubdivisionExpand_respects G e) (continuous_rawSubdivisionExpand G e)

#print axioms continuous_splitEdge
#print axioms continuous_subdivisionExpand

theorem splitEdge_half [DecidableEq E] (G : CellGraph V E) (e : E) (t : EdgeInterval) :
    splitEdge G e (intervalHalf t) = Quot.mk _ (.inr ⟨.inl e, t⟩) := by
  have hle : (intervalHalf t).1 ≤ 1 / 2 := by
    dsimp [intervalHalf]
    linarith [t.2.2]
  have hi : intervalLowerDouble (intervalHalf t) = t := by
    apply Subtype.ext
    have hm : 2 * (t.1 / 2) = t.1 := by ring
    simp only [intervalLowerDouble, intervalHalf, hm, min_eq_right t.2.2]
  unfold splitEdge
  rw [if_pos hle, hi]

theorem splitEdge_upper [DecidableEq E] (G : CellGraph V E) (e : E) (t : EdgeInterval) :
    splitEdge G e (intervalUpper t) = Quot.mk _ (.inr ⟨.inr (), t⟩) := by
  by_cases hz : t.1 = 0
  · have ht : t = intervalZero := Subtype.ext hz
    subst t
    have hi : intervalUpper intervalZero = intervalHalf intervalOne := by
      apply Subtype.ext
      norm_num [intervalUpper, intervalZero, intervalHalf, intervalOne]
    rw [hi, splitEdge_half]
    exact subdivision_join G e
  · have hgt : ¬(intervalUpper t).1 ≤ 1 / 2 := by
      dsimp [intervalUpper]
      have hpos : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm hz)
      linarith
    have hi : intervalUpperDouble (intervalUpper t) = t := by
      apply Subtype.ext
      have hm : 2 * ((1 + t.1) / 2) - 1 = t.1 := by ring
      simp only [intervalUpperDouble, intervalUpper, hm, max_eq_right t.2.1]
    unfold splitEdge
    rw [if_neg hgt, hi]

theorem collapse_splitEdge [DecidableEq E] (G : CellGraph V E) (e : E) (t : EdgeInterval) :
    subdivisionCollapse G e (splitEdge G e t) = Quot.mk _ (.inr ⟨e, t⟩) := by
  unfold splitEdge
  split_ifs with h
  · have hi : intervalHalf (intervalLowerDouble t) = t := by
      apply Subtype.ext
      have hm : 2 * t.1 ≤ 1 := by linarith
      simp only [intervalHalf, intervalLowerDouble, min_eq_right hm]
      ring
    change (if e = e then Quot.mk (EndpointRelation G) (.inr ⟨e, intervalHalf (intervalLowerDouble t)⟩)
      else Quot.mk (EndpointRelation G) (.inr ⟨e, intervalLowerDouble t⟩)) = _
    simp [hi]
  · have hi : intervalUpper (intervalUpperDouble t) = t := by
      apply Subtype.ext
      have hm : 0 ≤ 2 * t.1 - 1 := by linarith
      simp only [intervalUpper, intervalUpperDouble, max_eq_right hm]
      ring
    change Quot.mk (EndpointRelation G) (.inr ⟨e, intervalUpper (intervalUpperDouble t)⟩) = _
    rw [hi]

theorem collapse_expand [DecidableEq E] (G : CellGraph V E) (e : E)
    (q : CellRealization G) : subdivisionCollapse G e (subdivisionExpand G e q) = q := by
  induction q using Quot.inductionOn with
  | h p =>
    rcases p with v | ⟨f, t⟩
    · rfl
    · by_cases hfe : f = e
      · subst f
        change subdivisionCollapse G e (if e = e then splitEdge G e t else _) = _
        simp only [if_pos rfl]
        exact collapse_splitEdge G e t
      · simp [subdivisionExpand, rawSubdivisionExpand, subdivisionCollapse,
          rawSubdivisionCollapse, hfe]

theorem expand_collapse [DecidableEq E] (G : CellGraph V E) (e : E)
    (q : CellRealization (G.subdivideOne e)) :
    subdivisionExpand G e (subdivisionCollapse G e q) = q := by
  induction q using Quot.inductionOn with
  | h p =>
    rcases p with (v | u) | ⟨(f | u), t⟩
    · rfl
    · cases u
      change (if e = e then splitEdge G e intervalMid else _) = _
      simp only [if_pos rfl]
      have hi : intervalMid = intervalHalf intervalOne := rfl
      rw [hi, splitEdge_half]
      simpa [CellGraph.subdivideOne] using
        (Quot.sound (EndpointRelation.target (G := G.subdivideOne e) (.inl e)))
    · by_cases hfe : f = e
      · subst f
        change subdivisionExpand G e (if e = e then Quot.mk _ (.inr ⟨e, intervalHalf t⟩) else _) = _
        simp only [if_pos rfl]
        change (if e = e then splitEdge G e (intervalHalf t) else _) = _
        simp only [if_pos rfl]
        exact splitEdge_half G e t
      · simp [subdivisionExpand, rawSubdivisionExpand, subdivisionCollapse,
          rawSubdivisionCollapse, hfe]
    · cases u
      change (if e = e then splitEdge G e (intervalUpper t) else _) = _
      simp only [if_pos rfl]
      exact splitEdge_upper G e t

def cellSubdivisionHomeomorph [DecidableEq E] (G : CellGraph V E) (e : E) :
    CellRealization G ≃ₜ CellRealization (G.subdivideOne e) where
  toFun := subdivisionExpand G e
  invFun := subdivisionCollapse G e
  left_inv := collapse_expand G e
  right_inv := expand_collapse G e
  continuous_toFun := continuous_subdivisionExpand G e
  continuous_invFun := continuous_subdivisionCollapse G e

#print axioms cellSubdivisionHomeomorph

end
end P4110Geometry
namespace P4110Connected
open P4110 P4110Geometry
variable {V E : Type*} [TopologicalSpace V] [DiscreteTopology V] [DecidableEq E]
noncomputable def orderedCellSubdivisionHomeomorph (n : ℕ) (G : CellGraph V E) (e : E) :
    OrderedConfig n (CellRealization G) ≃ₜ
      OrderedConfig n (CellRealization (G.subdivideOne e)) :=
  orderedConfigHomeomorph n (cellSubdivisionHomeomorph G e)
noncomputable def unorderedCellSubdivisionHomeomorph (n : ℕ) (G : CellGraph V E) (e : E) :
    UnorderedConfig n (CellRealization G) ≃ₜ
      UnorderedConfig n (CellRealization (G.subdivideOne e)) :=
  unorderedConfigHomeomorph n (cellSubdivisionHomeomorph G e)
#print axioms orderedCellSubdivisionHomeomorph
#print axioms unorderedCellSubdivisionHomeomorph
end P4110Connected
