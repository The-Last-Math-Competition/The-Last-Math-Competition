# Disproof of conjecture `00000001581`

**Verdict: FALSE — the Fricke surface x² + y² + z² − xyz = 1 over F₅
has exactly N₅ = 6 points (kernel-certified exhaustive count), while
the conjectured point-count pattern demands N₅ ∈ {p² − p + 1, p² + 1,
p² + p + 1} = {21, 26, 31} at p = 5.  6 is none of them.**

## The conjecture (verbatim from `conjectures/00000001581.md`)

> Definition: The isomonodromy deformation and its monodromy manifold.
> Conjecture: The count of Q-points of the PVI monodromy manifold is
> N_p = p² + ap + 1 with a ∈ {−1, 0, 1} (point-count patterns).

## The refutation

The PVI monodromy manifold is the Fricke surface x² + y² + z² −
xyz = κ (classical identification).  Over F₅ with κ = 1 (a genuine
PVI-type parameter), the exhaustive count over the 125 triples of
F₅³ gives

    N₅ = 6:   (0,0,1), (0,0,4), (0,1,0), (0,4,0), (1,0,0), (4,0,0),

while the pattern N_p = p² + ap + 1 with a ∈ {−1, 0, 1} at p = 5
demands N₅ ∈ {21, 26, 31}.  6 is not among them: the pattern is
violated.  (Contrast: the degenerate κ = 0 surface has 41 points.)

The kernel certifies the complete count by reduction of a defined
counting function over List.range 5 (all 125 triples), the six
individual memberships, the two non-memberships ((0,0,0) and (1,1,1)
are off-surface), and the pattern arithmetic.

## Verification

* `reproduce.py` — brute-force enumeration over F₅³ with exact
  condition x² + y² + z² − xyz = 1 (mod 5): N₅ = 6 with the listed
  points; pattern values {21, 26, 31}; contrast count for κ = 0 (41).
* Lean 4 (core, v4.33.1), `lean4/` — the membership predicate (using
  −xyz = 4xyz mod 5), the count function over List.range 5, the
  theorem count = 6 proved by kernel reduction, the six memberships,
  two sanity non-memberships, and the pattern arithmetic.  All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the complete F₅ enumeration (count 6, the six
points, and the pattern arithmetic).  The identification "PVI
monodromy manifold = Fricke surface" is classical and cited in prose.
The point-count pattern is refuted at p = 5, κ = 1.
