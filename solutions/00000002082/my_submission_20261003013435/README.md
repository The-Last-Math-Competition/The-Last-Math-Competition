# Disproof of conjecture `00000002082`

**Verdict: FALSE — at n = 2 the product Δ¹×Δ¹ is the unit square, whose
EHZ capacity is at least π/4 (inscribed disk), and π/4 > 1/√2: the
claimed closed form 1/√n fails already at n = 2.**

## The conjecture (verbatim from `conjectures/00000002082.md`)

> Definition: The EHZ capacity is the Ekeland–Hofer–Zehnder capacity of
> Lagrangian cylinders. Conjecture: The EHZ capacity of the product of
> simplices Δ¹×Δ^{n−1} is a radical rational number (concretely the
> explicit closed form 1/√n); the value is obtained by a Billroth-type
> geodesic exhaustion.

## The counterexample (n = 2)

Δ¹×Δ¹ is the unit square [0,1]² (affinely, with the standard
symmetrized form). Classical facts:

1. The square contains the inscribed disk of radius 1/2 centered at
   (1/2, 1/2).
2. EHZ capacity is monotone under inclusion.
3. The EHZ capacity of a disk of radius r is π·r² (Ekeland–Hofer–Zehnder;
   e.g. Hofer–Zehnder, *Symplectic capacities and Hamiltonian
   dynamics*, and the standard disk computation).

Hence c_EHZ(square) ≥ π·(1/2)² = π/4. By Archimedes' bound π > 3
(indeed π > 22/7), π/4 > 3/4, and (3/4)² = 9/16 > 1/2 gives
3/4 > 1/√2. Therefore

    c_EHZ(Δ¹×Δ¹) ≥ π/4 > 3/4 > 1/√2,

so the claimed capacity 1/√n at n = 2 is strictly exceeded — the
closed form is false, independent of any "Billroth-type geodesic
exhaustion" justification.

## Verification

* `reproduce.py` — exact-fraction comparison of the chain
  (3/4)² = 9/16 > 1/2 and the numerical values; verifies the inscribed
  disk containment (max distance from center (1/2,1/2) to square
  boundary in the L∞ metric is 1/2, and the Euclidean inscribed disk of
  radius 1/2 lies in the square).
* Lean 4 (core, v4.33.1) — `lean4/`: the quadratic comparison
  2·9 > 16 (equivalently (3/4)² > 1/2, i.e. 3/4 > 1/√2) and the bound
  values; all audited theorems report `does not depend on any axioms`.
  The geometric facts (inscribed disk; capacity monotonicity; disk
  capacity πr²) and Archimedes' π > 3 are classical and cited.

## Boundary

Only the closed-form value at n = 2 is refuted (it already falsifies
the displayed formula); the Billroth-exhaustion clause and larger n are
not addressed.
