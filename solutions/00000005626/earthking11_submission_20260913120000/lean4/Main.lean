/-
  Disproof of conjecture 00000005626.

  Claim (informal): every 6-point subset of the plane in general position
  contains an "empty pentagon", and Horton-type sets are the unique
  counterexample family.

  Counterexample: the five vertices of a convex pentagon together with an
  interior point.  The set is in general position (no three points
  collinear) but contains no empty pentagon.

  Everything below is exact integer arithmetic.  No Mathlib, no ℝ, no
  floating point.  All proofs are by kernel `decide`.

  Coordinates:
    P1 = (0,0)   P2 = (4,0)   P3 = (5,2)   P4 = (2,4)   P5 = (-1,2)
    C  = (2,1)   (strictly interior lattice point, no three collinear)

  NOTE.  The interior point (2,2) is NOT usable: it is collinear with
  P3 = (5,2) and P5 = (-1,2).  The point (2,1) is the unique lattice point
  that is strictly inside the hull of every four of the five outer
  vertices and keeps all six points in general position.
-/

import Std

namespace Tlmc5626

/-- An integer lattice point. -/
abbrev Point := Int × Int

/-- Oriented area (cross product) of the turn `o -> a -> b`.
    Positive means a left turn, negative a right turn, zero collinear. -/
def cross (o a b : Point) : Int :=
  (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-! ### The six points -/

def P1 : Point := (0, 0)
def P2 : Point := (4, 0)
def P3 : Point := (5, 2)
def P4 : Point := (2, 4)
def P5 : Point := (-1, 2)
def C  : Point := (2, 1)

/-- The five outer vertices, in counter-clockwise order. -/
def outer : List Point := [P1, P2, P3, P4, P5]

/-- The full six-point set. -/
def allPoints : List Point := [P1, P2, P3, P4, P5, C]

/-! ### Computable geometry helpers (integer arithmetic) -/

def nonneg (n : Int) : Bool := decide (0 ≤ n)
def nonpos (n : Int) : Bool := decide (n ≤ 0)

/-- `p` lies in the closed triangle `u v w` (either orientation). -/
def inTri (u v w p : Point) : Bool :=
  let s1 := cross u v p
  let s2 := cross v w p
  let s3 := cross w u p
  (nonneg s1 && nonneg s2 && nonneg s3) ||
  (nonpos s1 && nonpos s2 && nonpos s3)

/-- `p` lies in the convex hull of four points (Carathéodory in dimension 2). -/
def inConv4 (a b c d p : Point) : Bool :=
  inTri a b c p || inTri a b d p || inTri a c d p || inTri b c d p

/-- `p` lies in the convex hull of five points (Carathéodory in dimension 2). -/
def inConv5 (a b c d e p : Point) : Bool :=
  inTri a b c p || inTri a b d p || inTri a b e p || inTri a c d p ||
  inTri a c e p || inTri a d e p || inTri b c d p || inTri b c e p ||
  inTri b d e p || inTri c d e p

/-- The five points are in strictly convex position, i.e. every one of them
    is an extreme point: no point lies in the convex hull of the other four.
    This test is independent of the order in which the points are supplied. -/
def strictlyConvex5 (a b c d e : Point) : Bool :=
  !inConv4 b c d e a && !inConv4 a c d e b && !inConv4 a b d e c &&
  !inConv4 a b c e d && !inConv4 a b c d e

/-- The five points form an *empty pentagon* with respect to the complement
    `{q}`: they are in strictly convex position and the remaining point `q`
    is not inside their convex hull. -/
def emptyPentWith (q a b c d e : Point) : Bool :=
  strictlyConvex5 a b c d e && !inConv5 a b c d e q

/-! ### The counterexample verified -/

/-- General position: no three of the six points are collinear (20 triples). -/
abbrev GeneralPosition : Prop :=
  cross P1 P2 P3 ≠ 0 ∧ cross P1 P2 P4 ≠ 0 ∧ cross P1 P2 P5 ≠ 0 ∧
  cross P1 P2 C  ≠ 0 ∧ cross P1 P3 P4 ≠ 0 ∧ cross P1 P3 P5 ≠ 0 ∧
  cross P1 P3 C  ≠ 0 ∧ cross P1 P4 P5 ≠ 0 ∧ cross P1 P4 C  ≠ 0 ∧
  cross P1 P5 C  ≠ 0 ∧ cross P2 P3 P4 ≠ 0 ∧ cross P2 P3 P5 ≠ 0 ∧
  cross P2 P3 C  ≠ 0 ∧ cross P2 P4 P5 ≠ 0 ∧ cross P2 P4 C  ≠ 0 ∧
  cross P2 P5 C  ≠ 0 ∧ cross P3 P4 P5 ≠ 0 ∧ cross P3 P4 C  ≠ 0 ∧
  cross P3 P5 C  ≠ 0 ∧ cross P4 P5 C  ≠ 0

/-- The five outer vertices are strictly convex: the five consecutive cross
    products are all of the same (positive) sign. -/
abbrev PentagonStrictlyConvex : Prop :=
  0 < cross P1 P2 P3 ∧ 0 < cross P2 P3 P4 ∧ 0 < cross P3 P4 P5 ∧
  0 < cross P4 P5 P1 ∧ 0 < cross P5 P1 P2

/-- The centre `(2,1)` lies strictly on the interior side of each of the
    five edges of the outer pentagon (oriented counter-clockwise). -/
abbrev CentreStrictlyInside : Prop :=
  0 < cross P1 P2 C ∧ 0 < cross P2 P3 C ∧ 0 < cross P3 P4 C ∧
  0 < cross P4 P5 C ∧ 0 < cross P5 P1 C

/-- No five of the six points form an empty pentagon: enumerate all six
    5-element subsets explicitly. -/
abbrev NoEmptyPentagon : Prop :=
  emptyPentWith C P1 P2 P3 P4 P5 = false ∧
  emptyPentWith P1 P2 P3 P4 P5 C = false ∧
  emptyPentWith P2 P1 P3 P4 P5 C = false ∧
  emptyPentWith P3 P1 P2 P4 P5 C = false ∧
  emptyPentWith P4 P1 P2 P3 P5 C = false ∧
  emptyPentWith P5 P1 P2 P3 P4 C = false

theorem general_position : GeneralPosition := by decide

theorem pentagon_strictly_convex : PentagonStrictlyConvex := by decide

theorem centre_strictly_inside : CentreStrictlyInside := by decide

theorem no_empty_pentagon : NoEmptyPentagon := by decide

/-- The conjunction of everything: the six points are in general position,
    the five outer points are strictly convex, the centre is strictly
    inside their hull, and consequently no 5-subset is an empty pentagon.
    Hence conjecture 00000005626 is FALSE. -/
theorem conjecture_00000005626_false :
    GeneralPosition ∧ PentagonStrictlyConvex ∧ CentreStrictlyInside ∧
      NoEmptyPentagon :=
  ⟨general_position, pentagon_strictly_convex, centre_strictly_inside,
    no_empty_pentagon⟩

end Tlmc5626
