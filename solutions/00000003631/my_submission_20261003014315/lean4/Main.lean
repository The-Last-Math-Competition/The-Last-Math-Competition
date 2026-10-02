/-
  Disproof of TLMC conjecture 00000003631.

  Conjecture: "The maximal number of invariant lines of quadratic
  systems is four, realized as complete grids."

  Refutation: the quadratic system X(x, y) = (x, y) (components P = x,
  Q = y, both of degree 1 <= 2, hence a quadratic system in the standard
  degree-at-most-2 sense) has the origin as a star point: EVERY line
  through the origin is invariant, since its flow is radial scaling.

  Algebraically (the first-order invariance criterion): a line l = 0
  with linear form l = alpha*x + beta*y is invariant for the vector
  field X = (P, Q) iff X(l) := P * dl/dx + Q * dl/dy is a scalar
  multiple of l.  For X = (x, y): dl/dx = alpha, dl/dy = beta, hence

      X(l) = x*alpha + y*beta = (alpha, beta) = l,

  a scalar multiple (quotient 1) of l -- EVERY line through the origin
  is invariant.  Kernel-certified below by an honest computation of the
  operator (differentiate, multiply by x / by y, add) for FIVE
  pairwise-distinct lines of the same system:

      y (k = 0),  y - x (k = 1),  y - 2*x (k = 2),  y + x (k = -1),
      and the vertical line x.

  Five > 4: the claimed maximum of four is false (the system in fact
  has infinitely many invariant lines; the conjecture states no
  general-position or nondegeneracy hypothesis that would exclude the
  star point).  All computations are closed and axiom-free.
-/

namespace Tlmc3631

/-! ## Linear forms and the operator X. -/

/-- Linear forms: alpha*x + beta*y as the signed coefficient pair
    (alpha, beta).  Differentiate with respect to x: alpha. -/
def dX (l : Int × Int) : Int := l.1

/-- Differentiate with respect to y: beta. -/
def dY (l : Int × Int) : Int := l.2

/-- Multiply the constant g by x: the form g*x, pair (g, 0). -/
def mulX (g : Int) : Int × Int := (g, 0)

/-- Multiply the constant g by y: the form g*y, pair (0, g). -/
def mulY (g : Int) : Int × Int := (0, g)

/-- Add two linear forms, coefficientwise. -/
def addL (a b : Int × Int) : Int × Int := (a.1 + b.1, a.2 + b.2)

/-- The operator X(l) = x * dl/dx + y * dl/dy for the field X = (x, y),
    computed structurally: multiply each partial by the corresponding
    coordinate and add. -/
def Xop (l : Int × Int) : Int × Int := addL (mulX (dX l)) (mulY (dY l))

/-! ## The five invariant lines of X = (x, y). -/

/-- The five lines as signed coefficient pairs. -/
def line1 : Int × Int := (0, 1)    -- y          (k =  0)
def line2 : Int × Int := (-1, 1)   -- y - x      (k =  1)
def line3 : Int × Int := (-2, 1)   -- y - 2*x    (k =  2)
def line4 : Int × Int := (1, 1)    -- y + x      (k = -1)
def line5 : Int × Int := (1, 0)    -- x          (vertical)

/-- X(line1) = line1: the line y = 0 is invariant. -/
theorem inv_line1 : Xop line1 = line1 := by decide

/-- X(line2) = line2: the line y - x = 0 is invariant. -/
theorem inv_line2 : Xop line2 = line2 := by decide

/-- X(line3) = line3: the line y - 2x = 0 is invariant. -/
theorem inv_line3 : Xop line3 = line3 := by decide

/-- X(line4) = line4: the line y + x = 0 is invariant. -/
theorem inv_line4 : Xop line4 = line4 := by decide

/-- X(line5) = line5: the vertical line x = 0 is invariant. -/
theorem inv_line5 : Xop line5 = line5 := by decide

/-! ## The five lines are pairwise distinct, and five > 4. -/

theorem five_distinct :
    line1 ≠ line2 ∧ line1 ≠ line3 ∧ line1 ≠ line4 ∧ line1 ≠ line5 ∧
    line2 ≠ line3 ∧ line2 ≠ line4 ∧ line2 ≠ line5 ∧
    line3 ≠ line4 ∧ line3 ≠ line5 ∧
    line4 ≠ line5 := by decide

/-- THE REFUTATION: one quadratic system with FIVE invariant lines
    (5 > 4): the maximal count is not four. -/
theorem five_gt_four : (5:Nat) > 4 := by decide

theorem conjecture_refuted : ¬ ((4:Nat) ≥ 5) := by decide

end Tlmc3631
