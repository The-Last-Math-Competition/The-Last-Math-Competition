# Disproof of conjecture `00000002154`

**Verdict: FALSE — C₆ (the 6-cycle) is a subdivision of the closed
Eulerian graph C₃ (the triangle: all degrees 2, Eulerian circuit), but
Jac(C₆) = ℤ/6 ≅ ℤ/2 × ℤ/3 has TWO nontrivial cyclic torsion factors —
not zero.  The classification's inclusion 1 ("subdivisions of closed
Eulerian graphs have zero cyclic factors") fails at C₆, refuting the
"exactly" classification.**

## The conjecture (verbatim from `conjectures/00000002154.md`)

> Definition: The number of cyclic factors of the critical group
> Jac(G) (the sandpile group) is the number of its cyclic ℤ-components.
> Conjecture: The classification of graphs with zero cyclic factors
> (i.e. Jac entirely cyclic-free): exactly subdivisions of closed
> Eulerian graphs (trivial exceptions exhausted).

## The refutation

C₆ is a subdivision of the triangle C₃: each of the 3 triangle edges
split once gives 3·2 = 6 edges.  The triangle is closed Eulerian (all
degrees 2, even; Eulerian circuit exists).  So C₆ is a subdivision of
a closed Eulerian graph.  But by the Matrix-Tree theorem,
|Jac(C₆)| = #spanning trees of C₆ = 6 (delete one of the 6 edges → a
spanning path: exactly 6 trees), and the exact Smith normal form of
the 5×5 reduced Laplacian is diag(1, 1, 1, 1, 6):

    Jac(C₆) = ℤ/6 ≅ ℤ/2 × ℤ/3,

which has TWO nontrivial cyclic torsion factors — the cyclic factor
count is 2 ≠ 0.  The classification's inclusion 1 fails at C₆: the
"exactly" classification is refuted.  (Inclusion 2 also fails: any
tree has Jac = 0 = zero cyclic factors but is not a subdivision of a
closed Eulerian graph — an independent second failure, noted by the
script.)

## Verification

* `reproduce.py` — the subdivision arithmetic, the triangle's
  Eulerian-circuit check, the spanning-tree enumeration of C₆
  (exactly 6), the exact Smith normal form diag(1,1,1,1,6) over ℤ
  via sympy, and the factor-count contrast 2 ≠ 0.
* Lean 4 (core, v4.33.1), `lean4/` — the subdivision arithmetic
  3·2 = 6, the triangle's Eulerian anchor (2 % 2 = 0), the Jac order
  6 = 2·3 with 6 > 1, the two nontrivial factors 2 > 0, 3 > 0 with
  2 ≠ 0, 3 ≠ 0.  All 5 audited theorems report `does not depend on
  any axioms`.

## Boundary

The kernel certifies the subdivision arithmetic, the Eulerian anchor,
and the factor-count contrast (Jac(C₆) has 2 cyclic torsion factors ≠
0).  The Matrix-Tree theorem, Jac(Cₙ) = ℤ/n for cycles, and the
Smith-normal-form computation are classical/cited in prose and
re-verified exactly by the script.  The classification is refuted at
C₆.
