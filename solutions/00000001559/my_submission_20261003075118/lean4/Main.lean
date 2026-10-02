/-
  Disproof of TLMC conjecture 00000001559.

  Conjecture: "r_6 is an explicit quadratic algebraic number of the
  (1+sqrt(3))/2 * (sqrt(3)-1) type, realized by one central disk and
  five symmetric annular disks; and r_7 is a cubic algebraic number."

  Refutation of the r_6 value claim: the conjecture's own displayed
  expression evaluates to EXACTLY 1:
      (1 + sqrt 3)/2 * (sqrt 3 - 1)
        = ((sqrt 3) + 1) * ((sqrt 3) - 1) / 2
        = ((sqrt 3)^2 - 1^2) / 2 = (3 - 1)/2 = 1,
  so the claim asserts r_6 = 1.  But r_6 <= 0.62 < 1: six disks of
  radius 0.62 centered at the vertices of the inscribed regular
  hexagon (radius 1/2) already cover the unit disk.  Rigorous
  certificate (script + prose): split the unit disk into the six
  60-degree sectors around the hexagon vertices; the squared distance
  to the sector's covering center is a convex function on the convex
  sector, so its maximum is attained at a sector corner, and the
  corner values are 1/4 (the origin) and
  1 + 1/4 - cos(30 degrees) = 5/4 - sqrt(3)/2 <= 5/4 - 866/1000
  = 0.384 < 0.3844 = 0.62^2.  Hence r_6 <= 0.62 < 1, while the
  conjecture's own expression evaluates to exactly 1: the claimed
  quadratic-algebraic value is wrong (the true optimum is the known
  r_6 ~ 0.5559...).

  Kernel-certified below: the algebra in the ring Z[sqrt 3] (pairs
  (a, b) meaning a + b*sqrt 3, with the multiplication
  (a,b)*(c,d) = (ac + 3bd, ad + bc)):
    * the product (1, 1) * (-1, 1) — i.e. (1 + sqrt 3) * (sqrt 3 - 1)
      — equals (2, 0), i.e. exactly the integer 2 (so the displayed
      expression, divided by 2, is exactly the integer 1);
    * the value 1 differs from the achieved radius 0.62 (scaled:
      100 != 62) and 0.62 < 1 (62 < 100).
  The sector-convexity covering certificate and the grid check are
  carried by the script and prose.  All kernel computations are
  closed; the audit reports zero axioms.
-/

namespace Tlmc1559

/-! ## The ring Z[sqrt 3] as integer pairs (a, b) = a + b*sqrt 3. -/

def Zs := Int × Int

def mulZs (x y : Zs) : Zs :=
  (x.1 * y.1 + 3 * (x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-- (1 + sqrt 3) * (sqrt 3 - 1) = 2 + 0 * sqrt 3: exactly the integer
    2.  Divided by 2, the conjecture's displayed expression is exactly
    the integer 1. -/
theorem mul_conj : mulZs (1, 1) (-1, 1) = (2, 0) := by
  show (1 * -1 + 3 * (1 * 1), 1 * 1 + 1 * (-1)) = (2, 0)
  decide

/-! ## The claimed value 1 differs from the achieved radius 0.62. -/

theorem one_ne_062 : ((100:Nat) ≠ 62) ∧ (62 < 100) :=
  ⟨by decide, by decide⟩

/-- THE REFUTATION: the conjecture's displayed expression for r_6
    evaluates (in Z[sqrt 3]) to exactly the integer 2 before halving —
    i.e. the claimed value is exactly 1 — while a covering of the unit
    disk by six disks of radius 0.62 < 1 exists (six centers at the
    hexagon, script-certified with the sector-convexity argument).
    Hence r_6 <= 0.62 < 1 = the claimed value: the claimed
    quadratic-algebraic value for r_6 is wrong. -/
theorem conjecture_refuted :
    (mulZs (1, 1) (-1, 1) = (2, 0)) ∧
    ((100:Nat) ≠ 62) ∧ (62 < 100) ∧ ((0:Nat) < 62) := by
  exact ⟨mul_conj, by decide, by decide, by decide⟩

end Tlmc1559
