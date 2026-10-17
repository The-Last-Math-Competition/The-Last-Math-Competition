import Init
set_option maxRecDepth 10000

/- #4228: a cellular chain model for the actual path 0--1--2.
Edges are oriented 0->1 and 1->2. Tree counts use the conventional
zero-dimensional trees (one vertex) and one-dimensional spanning trees.
No theorem about a different, unspecified notion of "tree count" is claimed. -/
namespace EulerTrees

def d0 (e : Int × Int) : Int × Int × Int := (-e.1,e.1-e.2,e.2)
def augment (z : Int × Int × Int) : Int := z.1+z.2.1+z.2.2

theorem d0_kernel (e : Int × Int) : d0 e = (0,0,0) ↔ e=(0,0) := by
  rcases e with ⟨a,b⟩
  simp only [d0, Prod.mk.injEq]
  omega

theorem d0_image (z : Int × Int × Int) :
    (∃ e, d0 e=z) ↔ augment z=0 := by
  constructor
  · rintro ⟨e,rfl⟩
    simp [augment,d0]
    omega
  · intro hz
    refine ⟨(-z.1,z.2.2),?_⟩
    rcases z with ⟨x,y,z⟩
    change x+y+z=0 at hz
    change (-(-x),-x-z,z)=(x,y,z)
    apply Prod.ext
    · exact Int.neg_neg x
    · apply Prod.ext
      · change -x-z=y
        omega
      · rfl

/-- Integral cellular chain groups, including all zero groups above degree 1. -/
def Chain : Nat → Type
  | 0 => Int × Int × Int
  | 1 => Int × Int
  | _+2 => PUnit
def zero : (n : Nat) → Chain n
  | 0 => (0,0,0)
  | 1 => (0,0)
  | _+2 => PUnit.unit
def scale : (n : Nat) → Int → Chain n → Chain n
  | 0, q, z => (q*z.1,q*z.2.1,q*z.2.2)
  | 1, q, z => (q*z.1,q*z.2)
  | _+2, _, _ => PUnit.unit
def boundary : (n : Nat) → Chain (n+1) → Chain n
  | 0, e => d0 e
  | 1, _ => (0,0)
  | _+2, _ => PUnit.unit
def Cycle : (n : Nat) → Chain n → Prop
  | 0, _ => True
  | n+1, z => boundary n z = zero n
def IsBoundary (n : Nat) (z : Chain n) : Prop :=
  ∃ e : Chain (n+1), boundary n e=z

theorem boundary_squared (n : Nat) (z : Chain (n+2)) :
    boundary n (boundary (n+1) z) = zero n := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- Standard quotient criterion for torsion-free H_n=cycles/boundaries:
if a positive integral multiple of a cycle is a boundary, so is the cycle. -/
def HomologyTorsionFree (n : Nat) : Prop :=
  ∀ (q : Int), 0<q → ∀ z : Chain n,
    Cycle n z → IsBoundary n (scale n q z) → IsBoundary n z

theorem h0_torsion_free : HomologyTorsionFree 0 := by
  intro q hq z _ hz
  change (∃ e, d0 e=z)
  apply (d0_image z).mpr
  have h := (d0_image (scale 0 q z)).mp hz
  change q*z.1+q*z.2.1+q*z.2.2=0 at h
  have hprod : q * augment z=0 := by
    simpa [augment,Int.mul_add] using h
  rcases Int.mul_eq_zero.mp hprod with hzero | hzero
  · omega
  · exact hzero

theorem homology_torsion_free (n : Nat) : HomologyTorsionFree n := by
  cases n with
  | zero => exact h0_torsion_free
  | succ n =>
    cases n with
    | zero =>
      intro q _ z hz _
      have hz0 : z=(0,0) := (d0_kernel z).mp hz
      exact ⟨PUnit.unit,hz0.symm⟩
    | succ n =>
      intro q _ z _ _
      refine ⟨PUnit.unit,?_⟩
      cases z
      rfl

/- A mask chooses a spanning subgraph from the two edges. The image
condition is integral connectivity; the kernel condition is acyclicity.
For a graph these are exactly the cellular-homology definition of a tree. -/
def Allowed (s : Bool × Bool) (e : Int × Int) : Prop :=
  (s.1=false → e.1=0) ∧ (s.2=false → e.2=0)
def IsSpanningTree (s : Bool × Bool) : Prop :=
  (∀ z, augment z=0 → ∃ e, Allowed s e ∧ d0 e=z) ∧
  (∀ e, Allowed s e → d0 e=(0,0,0) → e=(0,0))

theorem spanning_tree_iff (s : Bool × Bool) :
    IsSpanningTree s ↔ s=(true,true) := by
  constructor
  · intro hs
    obtain ⟨a,ha,hda⟩ := hs.1 (-1,1,0) (by decide)
    obtain ⟨b,hb,hdb⟩ := hs.1 (0,-1,1) (by decide)
    have ha1 : a.1=1 := by
      have he := congrArg Prod.fst hda
      change -a.1 = -1 at he
      omega
    have hb2 : b.2=1 := by
      have he := congrArg (fun z : Int × Int × Int => z.2.2) hdb
      exact he
    have hs1 : s.1=true := by
      cases h : s.1 with
      | false => have he := ha.1 h; omega
      | true => rfl
    have hs2 : s.2=true := by
      cases h : s.2 with
      | false => have he := hb.2 h; omega
      | true => rfl
    exact Prod.ext hs1 hs2
  · rintro rfl
    constructor
    · intro z hz
      obtain ⟨e,he⟩ := (d0_image z).mpr hz
      exact ⟨e,by simp [Allowed],he⟩
    · intro e _ he
      exact (d0_kernel e).mp he

def edgeMasks : List (Bool × Bool) :=
  [(false,false),(false,true),(true,false),(true,true)]
theorem edge_masks_complete (s : Bool × Bool) : s ∈ edgeMasks := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide
theorem edge_masks_nodup : edgeMasks.Nodup := by decide
def tree1 : Nat := (edgeMasks.filter (fun s => s.1 && s.2)).length
theorem tree_filter_correct (s : Bool × Bool) :
    (s.1 && s.2)=true ↔ IsSpanningTree s := by
  rw [spanning_tree_iff]
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide

/-- A zero-dimensional spanning tree consists of exactly one vertex.
The three singleton vertex sets are enumerated by Fin 3. -/
def tree0 : Nat := (List.finRange 3).length
def vertexCount : Nat := (List.finRange 3).length
def edgeCount : Nat := (List.finRange 2).length
def euler : Int := (vertexCount : Int)-edgeCount
def alternatingTrees : Int := (tree0 : Int)-tree1
theorem counts : tree0=3 ∧ tree1=1 ∧ euler=1 ∧ alternatingTrees=2 := by decide

theorem counterexample : (∀ n, HomologyTorsionFree n) ∧
    euler ≠ alternatingTrees := by
  exact ⟨homology_torsion_free,by decide⟩

#print axioms counterexample
#print axioms spanning_tree_iff
#print axioms tree_filter_correct
end EulerTrees
