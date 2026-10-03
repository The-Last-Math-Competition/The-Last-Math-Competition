# Disproof of conjecture `00000003970`

**Verdict: FALSE (minimal-number clause) — the minimal vertex number
for the subgraph-count/spectrum separation is 5, not "6 or 7".
Certified pair on 5 vertices: G₁ = K₃ + 2K₁ and G₂ = P₃ + K₂ have
IDENTICAL connected-induced-subgraph counts (5, 3, 1, 0, 0) while
their adjacency spectra differ: spec(G₁) = {2, −1, −1, 0, 0} with
characteristic polynomial x²(x−2)(x+1)², versus spec(G₂) =
{√2, 1, 0, −1, −√2} with x(x²−2)(x²−1).  The separation shows in
p(2) = 0 vs p(2) = 12 and in the (−1)-multiplicity 2 vs 1; and
n ≤ 4 is exhaustively clean (no separation at all).**

## The conjecture (verbatim from `conjectures/00000003970.md`)

> Definition: The subgraph count vector is the sequence of the
> numbers of subgraphs of each order. Conjecture: There exist two
> graphs whose counts of all connected subgraphs coincide while
> their adjacency spectra differ; the minimal vertex number for such
> a separation is 6 or 7, and all cases can be completely
> enumerated. (minimal subgraph-count spectrum separation)

## The refutation

At n = 5 take G₁ = K₃ ∪ 2K₁ (triangle plus two isolates) and
G₂ = P₃ ∪ K₂ (path plus an edge).  Connected induced subgraphs by
order: G₁ has 5 vertices, 3 edges (the triangle's), exactly 1
connected triple (the triangle), and nothing larger; G₂ has 5
vertices, 3 edges (2 + 1), exactly 1 connected triple (the path),
and nothing larger.  The count vectors (5, 3, 1, 0, 0) coincide.
The spectra do not: the characteristic polynomial of G₁ is
x²(x−2)(x+1)² (eigenvalues 2, −1, −1, 0, 0) and that of G₂ is
x(x²−2)(x²−1) (eigenvalues √2, 1, 0, −1, −√2).  At x = 2 the first
vanishes (2 is an eigenvalue of the triangle) while the second
equals 12; and the multiplicity of −1 is 2 versus 1.

Since exhaustive enumeration over all 2^C(n,2) graphs at
n = 2, 3, 4 yields no separation (every count-vector class contains
a single spectrum class), the minimal vertex number is exactly 5 —
the conjecture's "6 or 7" is false.  (The existence clause of the
conjecture survives; it is the minimal-number and enumeration
claims that are refuted.  Under the non-induced connected-subgraph
reading the sweep reports no separation up to n = 7 at all — a
second, independent failure of the enumeration claim.)

## Verification

* `reproduce.py` — the certified pair (identical counts, distinct
  eigenvalues); exhaustive enumeration at n = 2, 3, 4 (no
  separation).
* Lean 4 (core, v4.33.1), `lean4/` — `count_vertices`,
  `count_edges`, `count_triples` (the identical counts), `spec1_two`
  (the factor (2−2) = 0 for G₁), `spec2_no_two`/`polys_differ`
  (p₂(2) = 2·(4−2)·(4−1) = 12 ≠ 0 for G₂), `multiplicity_gap`
  (2 = 1+1 vs 1 ≠ 1+1), `conjecture_refuted`.  All 8 audited
  theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the count identity and the spectral anchors at
the certified 5-vertex pair; the n ≤ 4 exhaustive enumeration and
the eigenvalue numerics are in the script.  The minimal-number
claim is refuted; no claim is made about the non-induced reading
beyond the sweep's negative result recorded in prose.
