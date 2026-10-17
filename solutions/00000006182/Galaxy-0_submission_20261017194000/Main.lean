import Std

/-! A finite, exact counterexample to the constant-expectation-ratio clause
of TLMC 00000006182.  Vertices and edges are actual subsets of K₄. -/
namespace TLMC6182
attribute [local instance] Lean.Grind.Semiring.natCast

abbrev Vertex := Fin 4
abbrev Edge := Fin 6
abbrev Graph := Fin 16 × Fin 64
abbrev Host := Fin 64

def endpoints (e : Edge) : Vertex × Vertex :=
  match e.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

def vertexPresent (g : Graph) (v : Vertex) : Bool := g.1.val.testBit v.val

def edgePresent (g : Graph) (e : Edge) : Bool := g.2.val.testBit e.val

def vertexCount (g : Graph) : Nat :=
  ((List.finRange 4).filter (vertexPresent g)).length

def edgeCount (h : Host) : Nat :=
  ((List.finRange 6).filter (fun e => h.val.testBit e.val)).length

def incident (v : Vertex) (e : Edge) : Bool :=
  decide (v = (endpoints e).1 ∨ v = (endpoints e).2)

def degree (g : Graph) (v : Vertex) : Nat :=
  ((List.finRange 6).filter (fun e => edgePresent g e && incident v e)).length

def WellFormed (g : Graph) : Prop :=
  ∀ e : Edge, edgePresent g e = true →
    vertexPresent g (endpoints e).1 = true ∧
    vertexPresent g (endpoints e).2 = true

instance (g : Graph) : Decidable (WellFormed g) := inferInstanceAs
  (Decidable (∀ e : Edge, edgePresent g e = true →
    vertexPresent g (endpoints e).1 = true ∧ vertexPresent g (endpoints e).2 = true))

def Subgraph (g h : Graph) : Prop :=
  WellFormed g ∧
  (∀ v : Vertex, vertexPresent g v = true → vertexPresent h v = true) ∧
  (∀ e : Edge, edgePresent g e = true → edgePresent h e = true)

instance (g h : Graph) : Decidable (Subgraph g h) := inferInstanceAs
  (Decidable (WellFormed g ∧
  (∀ v : Vertex, vertexPresent g v = true → vertexPresent h v = true) ∧
  (∀ e : Edge, edgePresent g e = true → edgePresent h e = true)))

/-- Strict balance uses cross multiplication, with the nonempty vertex condition.
This is exactly |E(K)|/|V(K)| < |E(H)|/|V(H)|. -/
def StrictlyBalanced (h : Graph) : Prop :=
  WellFormed h ∧ 0 < vertexCount h ∧
  ∀ vs : Fin 16, ∀ es : Fin 64,
    let g : Graph := (vs, es)
    Subgraph g h → g ≠ h → 0 < vertexCount g →
    edgeCount g.2 * vertexCount h < edgeCount h.2 * vertexCount g

instance (h : Graph) : Decidable (StrictlyBalanced h) := inferInstanceAs
  (Decidable (WellFormed h ∧ 0 < vertexCount h ∧
  ∀ vs : Fin 16, ∀ es : Fin 64,
    Subgraph (vs, es) h → (vs, es) ≠ h → 0 < vertexCount (vs, es) →
    edgeCount es * vertexCount h < edgeCount h.2 * vertexCount (vs, es)))


/-- Undirected adjacency is read from the endpoint table and the actual edge set. -/
def Adjacent (g : Graph) (u v : Vertex) : Prop :=
  ∃ e : Edge, edgePresent g e = true ∧
    ((endpoints e = (u, v)) ∨ (endpoints e = (v, u)))

instance (g : Graph) (u v : Vertex) : Decidable (Adjacent g u v) := inferInstanceAs
  (Decidable (∃ e : Edge, edgePresent g e = true ∧
    ((endpoints e = (u, v)) ∨ (endpoints e = (v, u)))))

inductive Walk (g : Graph) : Vertex → Vertex → Prop
  | refl (v : Vertex) : Walk g v v
  | step {u v w : Vertex} : Adjacent g u v → Walk g v w → Walk g u w

def Connected (g : Graph) : Prop :=
  ∀ u v : Vertex, vertexPresent g u = true → vertexPresent g v = true → Walk g u v

/-- Every pair is joined by a walk of length at most two. -/
def DiameterAtMostTwo (g : Graph) : Prop :=
  ∀ u v : Vertex, vertexPresent g u = true → vertexPresent g v = true →
    u = v ∨ Adjacent g u v ∨ ∃ w : Vertex, Adjacent g u w ∧ Adjacent g w v

instance (g : Graph) : Decidable (DiameterAtMostTwo g) := inferInstanceAs
  (Decidable (∀ u v : Vertex, vertexPresent g u = true → vertexPresent g v = true →
    u = v ∨ Adjacent g u v ∨ ∃ w : Vertex, Adjacent g u w ∧ Adjacent g w v))

theorem diameter_two_connected {g : Graph} (h : DiameterAtMostTwo g) : Connected g := by
  intro u v hu hv
  rcases h u v hu hv with huv | huv | ⟨w, huw, hwv⟩
  · subst v; exact Walk.refl u
  · exact Walk.step huv (Walk.refl v)
  · exact Walk.step huw (Walk.step hwv (Walk.refl v))

def triangle : Graph := (7, 11)
def square : Graph := (15, 45)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The edge encoding is precisely the six unordered pairs of distinct vertices. -/
theorem endpoints_complete :
    (∀ e : Edge, (endpoints e).1 < (endpoints e).2) ∧
    (∀ u v : Vertex, u < v → ∃ e : Edge, endpoints e = (u, v) ∧
      ∀ f : Edge, endpoints f = (u, v) → f = e) := by decide

theorem triangle_counts : vertexCount triangle = 3 ∧ edgeCount triangle.2 = 3 := by decide
theorem square_counts : vertexCount square = 4 ∧ edgeCount square.2 = 4 := by decide

theorem triangle_strictly_balanced : StrictlyBalanced triangle := by decide
theorem square_strictly_balanced : StrictlyBalanced square := by decide

/-- At orders three and four, a simple graph all of whose vertices have degree
 two is necessarily the corresponding cycle. Classification below is exhaustive. -/
def Cycle (k : Nat) (g : Graph) : Prop :=
  WellFormed g ∧ vertexCount g = k ∧
    ∀ v : Vertex, vertexPresent g v = true → degree g v = 2

instance (k : Nat) (g : Graph) : Decidable (Cycle k g) := inferInstanceAs
  (Decidable (WellFormed g ∧ vertexCount g = k ∧
    ∀ v : Vertex, vertexPresent g v = true → degree g v = 2))

def triangles : List Graph := [(7, 11), (11, 21), (13, 38), (14, 56)]
def squares : List Graph := [(15, 30), (15, 45), (15, 51)]

theorem triangles_exact :
    ∀ vs : Fin 16, ∀ es : Fin 64, Cycle 3 (vs, es) ↔ (vs, es) ∈ triangles := by decide

theorem squares_exact :
    ∀ vs : Fin 16, ∀ es : Fin 64, Cycle 4 (vs, es) ↔ (vs, es) ∈ squares := by decide

theorem cycles_are_connected :
    ∀ vs : Fin 16, ∀ es : Fin 64,
      (Cycle 3 (vs, es) ∨ Cycle 4 (vs, es)) → DiameterAtMostTwo (vs, es) := by decide

theorem cycle_connected {g : Graph} (h : Cycle 3 g ∨ Cycle 4 g) : Connected g :=
  diameter_two_connected (cycles_are_connected g.1 g.2 h)

theorem representatives_nodup : triangles.Nodup ∧ squares.Nodup := by decide

def hostGraph (h : Host) : Graph := (15, h)

def copyCount (patterns : List Graph) (h : Host) : Nat :=
  (patterns.filter (fun g => decide (Subgraph g (hostGraph h)))).length

def triangleCount (h : Host) : Nat := copyCount triangles h

def squareCount (h : Host) : Nat := copyCount squares h

/-- The sample space is all 2⁶ simple graphs on four labeled vertices. -/
def hosts : List Host := List.finRange 64

theorem hosts_complete (h : Host) : h ∈ hosts := by simp [hosts]
theorem hosts_nodup : hosts.Nodup := by decide

theorem host_wellFormed : ∀ h : Host, WellFormed (hostGraph h) := by decide

/-- Product Bernoulli probability: each present edge contributes p and each
 absent edge contributes 1-p. -/
def probability {R : Type} [Lean.Grind.Field R] (p : R) (h : Host) : R :=
  p ^ edgeCount h * (1 - p) ^ (6 - edgeCount h)

def expectation {R : Type} [Lean.Grind.Field R] (p : R) (count : Host → Nat) : R :=
  (hosts.map (fun h => (count h : R) * probability p h)).sum

def mass {R : Type} [Lean.Grind.Field R] (p : R) : R := (hosts.map (probability p)).sum

/-- Histogram by edge count. The first entry is sample-space cardinality;
 the other two are sums of actual cycle-subgraph counts. -/
def histogram (k : Nat) : Nat × Nat × Nat :=
  let hs := hosts.filter (fun h => decide (edgeCount h = k))
  (hs.length, (hs.map triangleCount).sum, (hs.map squareCount).sum)

theorem histogram_exact :
    (List.range 7).map histogram =
      [(1,0,0), (6,0,0), (15,0,0), (20,4,0), (15,12,3), (6,12,6), (1,4,3)] := by decide


/-- Per-outcome data, evaluated from graph incidence, not supplied as inputs. -/
def sampleData : List (Nat × Nat × Nat) :=
  hosts.map (fun h => (triangleCount h, squareCount h, edgeCount h))

theorem sampleData_exact : sampleData = [
  (0,0,0), (0,0,1), (0,0,1), (0,0,2), (0,0,1), (0,0,2), (0,0,2), (0,0,3),
  (0,0,1), (0,0,2), (0,0,2), (1,0,3), (0,0,2), (0,0,3), (0,0,3), (1,0,4),
  (0,0,1), (0,0,2), (0,0,2), (0,0,3), (0,0,2), (1,0,3), (0,0,3), (1,0,4),
  (0,0,2), (0,0,3), (0,0,3), (1,0,4), (0,0,3), (1,0,4), (0,1,4), (2,1,5),
  (0,0,1), (0,0,2), (0,0,2), (0,0,3), (0,0,2), (0,0,3), (1,0,3), (1,0,4),
  (0,0,2), (0,0,3), (0,0,3), (1,0,4), (0,0,3), (0,1,4), (1,0,4), (2,1,5),
  (0,0,2), (0,0,3), (0,0,3), (0,1,4), (0,0,3), (1,0,4), (1,0,4), (2,1,5),
  (1,0,3), (1,0,4), (1,0,4), (2,1,5), (1,0,4), (2,1,5), (2,1,5), (4,3,6)] := by decide

theorem triangle_expectation_formula {R : Type} [Lean.Grind.Field R] (p : R) :
    expectation p triangleCount = 4 * p^3 := by
  have reindex : expectation p triangleCount =
      (sampleData.map (fun x => (x.1 : R) * p^x.2.2 * (1-p)^(6-x.2.2))).sum := by
    simp only [expectation, sampleData, List.map_map, Function.comp_def, probability]
    congr 2
    funext h
    exact Lean.Grind.Semiring.mul_assoc _ _ _ |>.symm
  rw [reindex, sampleData_exact]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  grind

theorem square_expectation_formula {R : Type} [Lean.Grind.Field R] (p : R) :
    expectation p squareCount = 3 * p^4 := by
  have reindex : expectation p squareCount =
      (sampleData.map (fun x => (x.2.1 : R) * p^x.2.2 * (1-p)^(6-x.2.2))).sum := by
    simp only [expectation, sampleData, List.map_map, Function.comp_def, probability]
    congr 2
    funext h
    exact Lean.Grind.Semiring.mul_assoc _ _ _ |>.symm
  rw [reindex, sampleData_exact]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  grind

theorem probability_mass_one {R : Type} [Lean.Grind.Field R] (p : R) : mass p = 1 := by
  have reindex : mass p =
      (sampleData.map (fun x => p^x.2.2 * (1-p)^(6-x.2.2))).sum := by
    simp only [mass, sampleData, List.map_map, Function.comp_def]
    rfl
  rw [reindex, sampleData_exact]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  grind



theorem probability_nonnegative {p : Rat} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : Host) :
    0 ≤ probability p h := by
  exact Rat.mul_nonneg (Rat.pow_nonneg hp)
    (Rat.pow_nonneg ((Rat.le_iff_sub_nonneg p 1).mp hp1))


/-- The standard product-measure definition, proved for an arbitrary Boolean list. -/
theorem bernoulli_product (p q : Rat) (bs : List Bool) :
    (bs.map (fun b => if b then p else q)).prod =
      p ^ (bs.filter id).length * q ^ (bs.filter (fun b => !b)).length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp [ih, Rat.pow_succ] <;> grind

def edgeBits (h : Host) : List Bool :=
  (List.finRange 6).map (fun e => h.val.testBit e.val)

/-- Every assignment of the six edge indicators occurs in the sample space. -/
theorem masks_complete : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    ∃ h : Host, edgeBits h = [b0,b1,b2,b3,b4,b5] := by decide

/-- Distinct outcomes encode distinct simple graphs. -/
theorem masks_unique : ∀ h k : Host, edgeBits h = edgeBits k → h = k := by decide

theorem edgeBits_counts : ∀ h : Host,
    ((edgeBits h).filter id).length = edgeCount h ∧
    ((edgeBits h).filter (fun b => !b)).length = 6 - edgeCount h := by decide

theorem probability_is_independent_edge_product (p : Rat) (h : Host) :
    probability p h = ((edgeBits h).map (fun b => if b then p else 1-p)).prod := by
  rw [bernoulli_product, (edgeBits_counts h).1, (edgeBits_counts h).2]
  rfl

theorem expectations_at_half :
    expectation (1/2 : Rat) triangleCount = 1/2 ∧
    expectation (1/2 : Rat) squareCount = 3/16 := by
  rw [triangle_expectation_formula, square_expectation_formula]
  grind

theorem expectations_at_one :
    expectation (1 : Rat) triangleCount = 4 ∧ expectation (1 : Rat) squareCount = 3 := by
  rw [triangle_expectation_formula, square_expectation_formula]
  grind

theorem expectations_at_quarter :
    expectation (1/4 : Rat) triangleCount = 1/16 ∧
    expectation (1/4 : Rat) squareCount = 3/256 := by
  rw [triangle_expectation_formula, square_expectation_formula]
  grind

/-- Both witnesses are strictly inside the probability interval. -/
theorem interior_parameters :
    (0 : Rat) < 1/4 ∧ (1/4 : Rat) < 1 ∧
    (0 : Rat) < 1/2 ∧ (1/2 : Rat) < 1 := by grind

/-- Unequal cross products avoid any division or denominator convention. -/
theorem expectation_ratio_changes :
    expectation (1/4 : Rat) triangleCount * expectation (1/2 : Rat) squareCount ≠
      expectation (1/2 : Rat) triangleCount * expectation (1/4 : Rat) squareCount := by
  rw [expectations_at_quarter.1, expectations_at_half.2,
    expectations_at_half.1, expectations_at_quarter.2]
  grind

/-- In particular, no common proportionality constant works for all p in (0,1). -/
theorem no_constant_ratio :
    ¬ ∃ c : Rat, ∀ p : Rat, 0 < p → p < 1 →
      expectation p triangleCount = c * expectation p squareCount := by
  rintro ⟨c, hc⟩
  have hq := hc (1/4) interior_parameters.1 interior_parameters.2.1
  have hh := hc (1/2) interior_parameters.2.2.1 interior_parameters.2.2.2
  have hne := expectation_ratio_changes
  rw [hq, hh] at hne
  apply hne
  grind

/-- Final counterexample: genuine equally dense strictly balanced cycles,
 ordinary Bernoulli random graph expectations, and failure of constant ratio. -/
theorem conjecture_6182_constant_ratio_disproved :
    StrictlyBalanced triangle ∧ StrictlyBalanced square ∧
    Connected triangle ∧ Connected square ∧
    edgeCount triangle.2 * vertexCount square = edgeCount square.2 * vertexCount triangle ∧
    (∀ p : Rat, 0 ≤ p → p ≤ 1 →
      mass p = 1 ∧ ∀ h : Host, 0 ≤ probability p h) ∧
    ¬ ∃ c : Rat, ∀ p : Rat, 0 < p → p < 1 →
      expectation p triangleCount = c * expectation p squareCount := by
  refine ⟨triangle_strictly_balanced, square_strictly_balanced,
    cycle_connected (Or.inl ?_), cycle_connected (Or.inr ?_), ?_, ?_, no_constant_ratio⟩
  · decide
  · decide
  · rw [triangle_counts.1, triangle_counts.2, square_counts.1, square_counts.2]
  · intro p hp hp1
    exact ⟨probability_mass_one p, probability_nonnegative hp hp1⟩


/-- This certificate excludes a real or complex proportionality constant too:
 it is valid in every characteristic-zero field, using the same graph sums. -/
theorem no_constant_in_any_characteristic_zero_field
    {R : Type} [Lean.Grind.Field R] [Lean.Grind.IsCharP R 0] :
    ¬ ∃ c : R,
      expectation (1/4 : R) triangleCount = c * expectation (1/4 : R) squareCount ∧
      expectation (1/2 : R) triangleCount = c * expectation (1/2 : R) squareCount := by
  rintro ⟨c, hq, hh⟩
  rw [triangle_expectation_formula, square_expectation_formula] at hq hh
  grind

end TLMC6182
