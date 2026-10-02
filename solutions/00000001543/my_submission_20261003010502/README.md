# Disproof of conjecture `00000001543`

**Verdict: FALSE — a line is an irreducible real algebraic curve, and n
equally spaced collinear points determine only n − 1 distinct distances;
(n−1)/n^{4/3} → 0, so no constant c > 0 makes n − 1 ≥ c·n^{4/3} hold for
all n. Kernel-certified as a general family statement.**

## The conjecture (verbatim from `conjectures/00000001543.md`)

> Definition: Distinct distances on algebraic curves. Conjecture: Any n
> points on an irreducible real algebraic curve determine at least
> c·n^{4/3} distinct distances (the curve distance exponent).

## The counterexample

Take the irreducible curve y = 0 (a line) and the n points
(1, 0), …, (n, 0). Their distinct pairwise distances are exactly
{1, …, n−1}: **n − 1** distinct distances (classical).

The claimed lower bound c·n^{4/3} with c > 0 then requires
n − 1 ≥ c·n^{4/3} for every n. Writing c = 1/C (a reciprocal integer;
the general real case follows by choosing C with 1/C ≤ c), this reads
C³·(n−1)³ ≥ n⁴ for every n. Kernel-certified below:

* **Ratio fact (general in n):** for every n ≥ 2,
  **(n−1)³ < n³ < n⁴**, so the collinear count n−1 is always below the
  n^{4/3} scale (not just eventually).
* **THE REFUTATION (general in the constant):** for every C ≥ 1 there
  exists n ≥ 2 — namely **n = 2·C³** — with
  **C³·(n−1)³ < n⁴**: the chain
  C³·(n−1)³ < C³·n³ < n³·n³·(1/…) — precisely
  C³·(n−1)³ < C³·n³ ≤ n³·(2C³) … certified via
  C³ < 2·C³ ≤ n. So at n = 2·C³ the collinear configuration violates
  the claimed bound for the constant 1/C.

Since (n−1)/n^{4/3} → 0, no absolute constant c > 0 survives: the
"curve distance exponent 4/3" fails on the simplest irreducible curve.

## Verification

* `reproduce.py` — counts distinct distances of equally spaced points
  on a line for n = 2..2000 (always exactly n − 1) and plots the ratio
  (n−1)/n^{4/3} → 0; verifies (n−1)³ < n⁴ for all n in range and the
  witness n = 2·C³ for C = 1..50.
* Lean 4 (core, v4.33.1) — `lean4/`: the strict product monotonicity
  lemmas (rebuilt by induction — the core versions carry
  `Classical.choice` upstream), cubic monotonicity, the ratio fact, and
  the general no-constant statement with explicit witnesses. All 5
  audited theorems report `does not depend on any axioms`. The fact
  that n collinear equally spaced points determine exactly n − 1
  distances is classical.

## Boundary

Only the displayed uniform-c constant claim is refuted; the (true)
n/polylog lower bounds for general point sets (Guth–Katz) and the
genuine curve-dependent exponents are not addressed.
