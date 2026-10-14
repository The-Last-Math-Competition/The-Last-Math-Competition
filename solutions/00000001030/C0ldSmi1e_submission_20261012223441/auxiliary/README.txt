EXACT AUXILIARY CHECKER FOR CONJECTURE 00000001030

Run using Python 3 and its standard library only:

  python3 check_icosahedron.py

The script exits with status 0 when the coordinate checks and sensitivity tests
all pass; otherwise it exits with status 1. It deterministically overwrites
exact-check-results.json and exact-check.log in this same auxiliary directory.
The JSON records the SHA-256 of the checker source, and the log records the
SHA-256 of both source and JSON. No network access, external packages, floating
point numbers, or prior conjecture artifacts are used.

The twelve raw points are the three cyclic families
  (0, +/-1, +/-phi), (+/-1, +/-phi, 0), (+/-phi, 0, +/-1),
with independent signs, phi=(1+sqrt(5))/2. The exact field class represents
a+b*sqrt(5) with Fraction coefficients. Its comparison routine uses rational
squares and signs, so supporting-plane decisions do not use tolerances.

Normalized points are raw points divided by r, where r is defined to be the
positive square root of R=phi+2. The checker verifies R>0 and that every raw
point has squared norm R. It does not incorrectly assume r belongs to
Q(sqrt(5)). At even total degree d, normalized moments divide the raw mean by
R^(d/2), which is a field element. At odd degree, every raw mean is checked to
be exactly zero. A nonzero odd result in a broken input is recorded honestly
as a quotient by r^d; equality with a target is checked by exact squared
equality and equal signs, using r>0.

The full result contains:
  - all twelve raw coordinates and their squared norms;
  - separate cardinality and distinctness checks;
  - each of the 56 exponent triples of total degree at most five, its raw mean,
    exact normalized mean, target, and pass/fail result;
  - the ten nonzero and forty-six zero target-moment counts;
  - all 66 unordered off-diagonal normalized inner products;
  - the antipode and five upper/five lower neighbors of every vertex;
  - an affine-dimension witness, all twenty supporting triangular faces and
    their exact supporting-plane offsets, all thirty edges, and incidence
    counts. Every raw edge has squared length four.

Supporting faces are found by enumerating all noncollinear triples. Each
candidate plane is checked against every vertex with exact signs; coplanar
vertices determine its full exposed vertex set. The result verifies that all
exposed facets found this way have three vertices, every edge belongs to two
faces, every vertex has five edges and five faces, and V-E+F=2. These are useful
finite data for identifying the displayed coordinate model geometrically.

Sensitivity checks exercise actual ways a purported certificate could be
wrong:
  - delete one vertex;
  - change one nonzero coordinate sign at one vertex, causing a duplicate and
    incorrect moments;
  - add the exact rational 1/10^30 to one coordinate, defeating any reliance on
    floating point tolerances;
  - change the x^2 target from 1/3 to 2/5.
Each must be rejected by specified substantive checks. Positive controls apply
a global coordinate reflection and the rational plane rotation with entries
3/5 and 4/5; both must retain every coordinate/moment/geometry property. These
controls distinguish malformed data from valid congruent configurations.

Proof boundary

The sphere-moment table is an INPUT TARGET to this finite checker. The code
does not prove that these are the integrals of monomials against normalized
Hausdorff surface measure. Nor does it prove the monomial-to-polynomial bridge,
the universal minimum-cardinality lower bound, or classification of every
twelve-point design. Those are proved in the accompanying Lean project.
The checker also is not a Lean-kernel certificate: its exact Python arithmetic
offers independent finite verification and mutation sensitivity, and must not
be substituted for formal proof obligations. The report and Lean project
must establish the same integrated definition and full theorem scope.
