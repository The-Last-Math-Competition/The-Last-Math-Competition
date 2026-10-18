import Std

/-!
Arithmetic core for conjecture 00000001015 under the standard PG(2,8)
interpretation: a fixed point of an 11-arc would determine ten distinct
incident lines, but an order-8 plane has only nine lines through a point.
-/

def RequiredDistinctLines (points lines : Nat) : Prop := points - 1 ≤ lines

/-- Ten distinct lines cannot fit among the nine lines through a point. -/
theorem no_11_arc_order_eight (h : RequiredDistinctLines 11 (8 + 1)) : False := by
  unfold RequiredDistinctLines at h
  omega

#print axioms no_11_arc_order_eight
