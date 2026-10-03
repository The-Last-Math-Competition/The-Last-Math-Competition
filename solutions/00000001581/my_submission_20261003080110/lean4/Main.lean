/-
  Disproof of TLMC conjecture 00000001581.

  Conjecture: "The count of Q-points of the PVI monodromy manifold is
  N_p = p^2 + ap + 1 with a in {-1, 0, 1} (point-count patterns)."

  Refutation at the Fricke-surface instance p = 5, kappa = 1: the
  Fricke surface x^2 + y^2 + z^2 - x*y*z = kappa over F_5 with
  kappa = 1 has
      N_5 = 6
  F_5-rational points (exhaustively enumerated: (0,0,1), (0,0,4),
  (0,1,0), (0,4,0), (1,0,0), (4,0,0) — kernel-certified by the count
  function below), while the conjectured point-count pattern at p = 5
  requires N_5 in {p^2 - p + 1, p^2 + 1, p^2 + p + 1} = {21, 26, 31}.
  6 is none of these: the point-count pattern is violated.

  Kernel-certified below:
    * the count function: over the 5^3 = 125 triples in
      {0,1,2,3,4}^3, the number satisfying
      x^2 + y^2 + z^2 + 4*x*y*z == 1 (mod 5)  [equivalent to the
      surface equation since -x*y*z = 4*x*y*z mod 5]  is exactly 6 —
      proved by kernel reduction (rfl) of the ground computation;
    * the six certified points themselves (each satisfies the mod-5
      surface equation — rfl);
    * the pattern arithmetic: p^2 - p + 1 = 21, p^2 + 1 = 26,
      p^2 + p + 1 = 31 at p = 5, and 6 is not among them;
    * the complement sanity: (0,0,0) and (1,1,1) are NOT on the
      kappa = 1 surface mod 5.
  The identification "Fricke surface = PVI monodromy manifold" and the
  interpretation over F_5 are classical and cited in prose.  All
  kernel computations are closed; the audit reports zero axioms.
-/

namespace Tlmc1581

/-! ## The surface membership and its point count over F_5. -/

/-- Membership in x^2 + y^2 + z^2 - xyz = 1 over F_5 (with
    -xyz = 4xyz mod 5), for coordinates in {0,...,4}. -/
def onS (x y z : Nat) : Bool := (x * x + y * y + z * z + 4 * (x * y * z)) % 5 == 1

/-- The number of surface points with x in {0,...,k-1}, y fixed loop... --
    counting over z, then y, then x, for k = 5. -/
def cntZ (x y : Nat) : Nat :=
  ((List.range 5).filter (fun z => onS x y z)).length

def cntY (x : Nat) : Nat :=
  ((List.range 5).foldl (fun acc y => acc + cntZ x y) 0)

def cntX : Nat :=
  ((List.range 5).foldl (fun acc x => acc + cntY x) 0)

/-- The exhaustive count over all 125 triples is exactly 6 — the
    points are (0,0,1), (0,0,4), (0,1,0), (0,4,0), (1,0,0), (4,0,0). -/
theorem count_eq_6 : cntX = 6 := rfl

/-- Each of the six points lies on the surface (kernel-checked). -/
theorem six_points :
    (onS 0 0 1 = true) ∧ (onS 0 0 4 = true) ∧ (onS 0 1 0 = true) ∧
    (onS 0 4 0 = true) ∧ (onS 1 0 0 = true) ∧ (onS 4 0 0 = true) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Sanity: (0,0,0) and (1,1,1) are NOT on the kappa = 1 surface. -/
theorem non_points :
    (onS 0 0 0 = false) ∧ (onS 1 1 1 = false) :=
  ⟨rfl, rfl⟩

/-! ## The conjectured pattern at p = 5 and the mismatch. -/

/-- The pattern values p^2 + a*p + 1 at p = 5 for a in {-1, 0, 1}:
    21, 26, 31. -/
theorem pattern_5 :
    ((5:Nat) * 5 - 5 + 1 = 21) ∧ (5 * 5 + 1 = 26) ∧ (5 * 5 + 5 + 1 = 31) := by
  decide

/-- THE REFUTATION: the Fricke surface x^2 + y^2 + z^2 - xyz = 1 over
    F_5 has exactly 6 points (kernel-certified exhaustive count),
    while the conjectured pattern at p = 5 demands N_5 in
    {21, 26, 31}: 6 is none of them.  The point-count pattern is
    violated. -/
theorem conjecture_refuted :
    (cntX = 6) ∧
    ((5:Nat) * 5 - 5 + 1 = 21) ∧ (5 * 5 + 1 = 26) ∧ (5 * 5 + 5 + 1 = 31) ∧
    (cntX ≠ 21) ∧ (cntX ≠ 26) ∧ (cntX ≠ 31) := by
  exact ⟨count_eq_6, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

end Tlmc1581
