import Std

namespace C3576

inductive Block where
  | left | middle | right
  deriving DecidableEq

inductive Swap where
  | leftPair | rightPair

def permutation : Swap → Block → Block
  | .leftPair, .left => .middle
  | .leftPair, .middle => .left
  | .leftPair, .right => .right
  | .rightPair, .left => .left
  | .rightPair, .middle => .right
  | .rightPair, .right => .middle

theorem permutation_involution (which : Swap) (i : Block) :
    permutation which (permutation which i) = i := by
  cases which <;> cases i <;> rfl

abbrev Point := Int × Int
abbrev Blocks := Block → Point

def reindex {A : Type} (σ : Block → Block) (v : Block → A) : Block → A :=
  fun i => v (σ i)

def basis (i : Block) : Blocks := fun j => if j = i then (1, 0) else (0, 0)

theorem reindex_faithful {σ τ : Block → Block}
    (equal : ∀ v : Blocks, reindex σ v = reindex τ v) : σ = τ := by
  funext i
  by_cases h : τ i = σ i
  · exact h.symm
  · have values := congrFun (equal (basis (σ i))) i
    simp [reindex, basis, h] at values

def addPoint (a b : Point) : Point := (a.1 + b.1, a.2 + b.2)
def subtractPoint (a b : Point) : Point := (a.1 - b.1, a.2 - b.2)
def scalePoint (a : Int) (p : Point) : Point := (a * p.1, a * p.2)

theorem reindex_add (σ : Block → Block) (u v : Blocks) :
    reindex σ (fun i => addPoint (u i) (v i)) =
      fun i => addPoint (reindex σ u i) (reindex σ v i) := rfl

theorem reindex_scale (σ : Block → Block) (a : Int) (v : Blocks) :
    reindex σ (fun i => scalePoint a (v i)) =
      fun i => scalePoint a (reindex σ v i) := rfl

def CollisionFree (v : Blocks) : Prop :=
  ∀ i j : Block, i ≠ j → v i ≠ v j

theorem action_free_at_configuration {v : Blocks} (distinct : CollisionFree v)
    (σ : Block → Block) (fixed : reindex σ v = v) : σ = id := by
  funext i
  by_cases h : σ i = i
  · exact h
  · exact False.elim (distinct (σ i) i h (congrFun fixed i))

inductive Segment where
  | first | second

/-- Coordinates with common denominator `D`. The time parameter is `s / D`. -/
def relative (segment : Segment) (D s : Int) : Point :=
  match segment with
  | .first => (s - D, s)
  | .second => (s, D - s)

def base (D : Int) : Blocks
  | .left => (-2 * D, 0)
  | .middle => (0, 0)
  | .right => (2 * D, 0)

def swapPath (which : Swap) (segment : Segment) (D s : Int) : Blocks :=
  let offset := relative segment D s
  fun i =>
    match which, i with
    | .leftPair, .left => addPoint (-D, 0) offset
    | .leftPair, .middle => subtractPoint (-D, 0) offset
    | .leftPair, .right => base D .right
    | .rightPair, .left => base D .left
    | .rightPair, .middle => addPoint (D, 0) offset
    | .rightPair, .right => subtractPoint (D, 0) offset

theorem swap_path_collision_free (which : Swap) (segment : Segment) {D s : Int}
    (positive : 0 < D) (nonnegative : 0 ≤ s) (bounded : s ≤ D) :
    CollisionFree (swapPath which segment D s) := by
  intro i j different equal
  cases which <;> cases segment <;> cases i <;> cases j <;>
    simp [swapPath, relative, base, addPoint, subtractPoint] at different equal <;> omega

theorem swap_path_start (which : Swap) (D : Int) : swapPath which .first D 0 = base D := by
  funext i
  cases which <;> cases i <;>
    simp [swapPath, relative, base, addPoint, subtractPoint] <;> omega

theorem swap_paths_glue (which : Swap) (D : Int) :
    swapPath which .first D D = swapPath which .second D 0 := by
  funext i
  cases which <;> cases i <;> simp [swapPath, relative]

theorem swap_path_end (which : Swap) (D : Int) :
    swapPath which .second D D = reindex (permutation which) (base D) := by
  funext i
  cases which <;> cases i <;>
    simp [swapPath, relative, base, addPoint, subtractPoint, reindex, permutation] <;> omega

theorem swaps_do_not_commute :
    reindex (permutation .leftPair) (reindex (permutation .rightPair) (basis .left)) ≠
      reindex (permutation .rightPair) (reindex (permutation .leftPair) (basis .left)) := by
  intro equal
  have values := congrFun equal Block.middle
  simp [reindex, permutation, basis] at values

/-- The algebraic transport calculation after the tangent maps of the covering
are substituted. Upstairs the connection transports the coordinate vector unchanged. -/
theorem normalized_transport {Tangent : Type} (which : Swap)
    (atStart atEnd : Blocks → Tangent) (identify : Tangent → Blocks)
    (leftInverse : ∀ v, identify (atStart v) = v)
    (deckDerivative : ∀ v, atEnd (reindex (permutation which) v) = atStart v) :
    (fun v => identify (atEnd v)) = reindex (permutation which) := by
  funext v
  have twice : reindex (permutation which) (reindex (permutation which) v) = v := by
    funext i
    simp [reindex, permutation_involution]
  have endIdentification := deckDerivative (reindex (permutation which) v)
  rw [twice] at endIdentification
  rw [endIdentification, leftInverse]

theorem lifted_transports_do_not_commute {Tangent : Type}
    (atStart atLeftEnd atRightEnd : Blocks → Tangent) (identify : Tangent → Blocks)
    (leftInverse : ∀ v, identify (atStart v) = v)
    (leftDerivative : ∀ v, atLeftEnd (reindex (permutation .leftPair) v) = atStart v)
    (rightDerivative : ∀ v, atRightEnd (reindex (permutation .rightPair) v) = atStart v) :
    ∃ v, identify (atLeftEnd (identify (atRightEnd v))) ≠
      identify (atRightEnd (identify (atLeftEnd v))) := by
  have left := normalized_transport .leftPair atStart atLeftEnd identify leftInverse leftDerivative
  have right := normalized_transport .rightPair atStart atRightEnd identify leftInverse rightDerivative
  refine ⟨basis .left, ?_⟩
  change (fun v => identify (atLeftEnd v)) ((fun v => identify (atRightEnd v)) (basis .left)) ≠
    (fun v => identify (atRightEnd v)) ((fun v => identify (atLeftEnd v)) (basis .left))
  rw [left, right]
  exact swaps_do_not_commute

#print axioms reindex_faithful
#print axioms swap_path_collision_free
#print axioms lifted_transports_do_not_commute

end C3576
