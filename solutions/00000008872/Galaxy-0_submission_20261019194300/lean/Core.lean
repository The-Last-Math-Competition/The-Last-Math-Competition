import Std

/-! Finite normal-play short games, with Conway's recursive comparison. -/
namespace TLMC8872

inductive Game where
  | node : List Game → List Game → Game
  deriving Repr

/-- Conway comparison: no left option of `g` is at least `h`, and no right
option of `h` is at most `g`. -/
def le : (g h : Game) → Bool
  | .node gl gr, .node hl hr =>
    gl.attach.all (fun x => !(le (.node hl hr) x.val)) &&
    hr.attach.all (fun y => !(le y.val (.node gl gr)))
termination_by g h => sizeOf g + sizeOf h
decreasing_by
  · have h := List.sizeOf_lt_of_mem x.property
    simp_wf
    omega
  · have h := List.sizeOf_lt_of_mem y.property
    simp_wf
    omega

theorem le_node (gl gr hl hr : List Game) :
    le (.node gl gr) (.node hl hr) =
      (gl.all (fun x => !(le (.node hl hr) x)) &&
        hr.all (fun y => !(le y (.node gl gr)))) := by
  rw [le]
  congr 1
  · rw [List.all_subtype (g := fun x => !(le (.node hl hr) x)) (by intros; rfl)]
    simp
  · rw [List.all_subtype (g := fun y => !(le y (.node gl gr))) (by intros; rfl)]
    simp

def zero : Game := .node [] []
def star : Game := .node [zero] [zero]

theorem le_zero_node (l r : List Game) :
    le zero (.node l r) = r.all (fun g => !(le g zero)) := by
  simpa only [zero, List.all_nil, Bool.true_and] using le_node [] [] l r

theorem le_node_zero (l r : List Game) :
    le (.node l r) zero = l.all (fun g => !(le zero g)) := by
  simpa only [zero, List.all_nil, Bool.and_true] using le_node l r [] []

def Equiv (g h : Game) : Prop := le g h = true ∧ le h g = true

def Lt (g h : Game) : Prop := le g h = true ∧ le h g = false

/-- Negation swaps Left and Right recursively. -/
def neg : Game → Game
  | .node l r => .node (r.map neg) (l.map neg)

/-- The canonical positive dyadic games `1, 1/2, 1/4, ...`. -/
def tiny : Nat → Game
  | 0 => .node [zero] []
  | n + 1 => .node [zero] [tiny n]

/-- Every follower is either terminal for both players or offers moves to both. -/
inductive AllSmall : Game → Prop where
  | node {l r : List Game}
      (balanced : l = [] ↔ r = [])
      (left : ∀ g ∈ l, AllSmall g)
      (right : ∀ g ∈ r, AllSmall g) : AllSmall (.node l r)

/-- Having numerical part zero: between every positive dyadic bound and its
negative, in Conway's strict order. -/
def NumericalPartZero (g : Game) : Prop :=
  ∀ n : Nat, Lt (neg (tiny n)) g ∧ Lt g (tiny n)

end TLMC8872
