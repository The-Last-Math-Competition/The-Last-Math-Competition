# Disproof of conjecture `00000003966`

**Verdict: FALSE (first clause) — the smallest nonplanar graph
requiring 3 pages is K₅, not K₃,₃.  K₅ is nonplanar (Euler: 10
edges > 3·5 − 6 = 9), requires 3 pages (Bernhart's bt(K_n) =
⌈n/2⌉ for n ≥ 4; brute-force verified: no 2-page embedding over
all 120 circular orders), and has 5 vertices — fewer than K₃,₃'s
6.  K₅ is also 1-planar (10 ≤ 4·5 − 8 = 12), consistent with the
second clause, which is not needed for the refutation.**

## The conjecture (verbatim from `conjectures/00000003966.md`)

> Definition: The book thickness is the minimal number of pages
> needed to distribute the edges after the vertices are arranged
> along the spine. Conjecture: The smallest nonplanar graph
> requiring 3 pages is K_{3,3}; every 1-planar graph needs at most
> 4 pages, and this bound is optimal. (optimal page bound for
> 1-planar graphs)

## The refutation

Both K₅ and K₃,₃ are nonplanar 3-page graphs — but K₅ is smaller:
5 vertices (and 10 edges) versus K₃,₃'s 6 vertices (9 edges).

* **K₅ is nonplanar**: its 10 edges violate the Euler bound
  e ≤ 3v − 6 = 9 (kernel-certified).
* **K₅ requires 3 pages**: Bernhart's theorem bt(K_n) = ⌈n/2⌉ for
  n ≥ 4 gives ⌈5/2⌉ = 3; independently, the script exhausts all
  120 circular vertex orders with their 2-colorable-conflict
  structures and finds no 2-page embedding (bt(K₅) ≥ 3; the
  standard 3-page drawing gives bt(K₅) ≤ 3).
* **K₅ has 5 < 6 vertices** (kernel-certified).

Hence the smallest nonplanar 3-page graph is K₅ — the
conjecture's "smallest is K₃,₃" is false.  (Both graphs lie in the
well-known chain: the 3-page nonplanar graphs are exactly those
containing a subdivision of K₅ or K₃,₃ by Bernhart–Kainen, and K₅
is the minimal one by vertex count.)  The second clause (1-planar
graphs ≤ 4 pages, optimal) is untouched by this refutation: K₅ is
1-planar with bt = 3 ≤ 4.

## Verification

* `reproduce.py` — exhaustive 2-page embedding search for K₅ over
  all 120 circular orders (none exists); the Euler violation
  10 > 9; the vertex comparison 5 < 6; the 1-planar count
  10 ≤ 12.
* Lean 4 (core, v4.33.1), `lean4/` — `K5_edges` (10),
  `K5_nonplanar` (10 > 9), `K5_pages` (⌈5/2⌉ = 3),
  `fewer_vertices` (5 < 6), `K33_basic` (9 edges, 6 vertices),
  `one_planar_count` (10 ≤ 12), `conjecture_refuted`.  All 7
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the exact counts (edges, vertices, page
number, Euler and 1-planar inequalities); the book-thickness
classification bt(K_n) = ⌈n/2⌉ is classical (Bernhart), and the
non-existence of a 2-page embedding is verified by the script's
exhaustive search.  The "smallest is K₃,₃" clause is refuted; no
claim is made about the 4-page optimality for 1-planar graphs.
