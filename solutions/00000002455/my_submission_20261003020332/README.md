# Disproof of conjecture `00000002455`

**Verdict: FALSE — self-contradictory: a DAG on ~200 vertices has at
most C(200,2) = 19900 edges (bounded, finite), so it cannot have
ℵ₀ edges.**

## The conjecture (verbatim from `conjectures/00000002455.md`)

> Definition: The cardinal-invariant diagram is the network of
> inequalities in Cichoń's and extended diagrams. Conjecture: The
> complete table of ZFC-provable inequalities is a finite DAG (about
> 200 vertices / ℵ₀ edges); the table is drawn explicitly (traversal
> complete).

## The refutation

A DAG is directed and acyclic, so between any unordered vertex pair at
most ONE of the two possible directed edges exists (both would form a
directed 2-cycle — a cycle; classical). Hence a DAG on N vertices has
at most C(N,2) edges. For N = 200:

    edges ≤ C(200,2) = 200·199/2 = 19900,

a bounded natural number — kernel-certified, together with the general
identity 2·C(n,2) = n(n−1). A count bounded by 19900 is finite; it
cannot be ℵ₀ (a countably infinite collection has more than 19900
elements). The displayed statement — "finite DAG … about 200 vertices /
ℵ₀ edges" — is internally contradictory no matter what the inequality
table contains: the edge count of ANY 200-vertex DAG is finite, so the
"traversal complete" drawing with ℵ₀ edges cannot exist.

(The arithmetic of the actual Cichoń diagram — 20-ish cardinal
invariants — only strengthens the point: any finite vertex count gives
a finite edge bound.)

## Verification

* `reproduce.py` — counts unordered pairs (19900) and verifies the
  quadratic growth; brute-force checks on small n that a DAG on n
  labeled vertices has at most C(n,2) edges (exhaustive over all
  orientations of all subgraphs of the complete graph, n ≤ 4: no
  acyclic orientation exceeds C(n,2), trivially, and every acyclic
  orientation has distinct pair-edges only).
* Lean 4 (core, v4.33.1) — `lean4/`: the pair count 19900, the
  boundedness (e ≤ 19900 → e < 20000), the general identity
  2·C(n,2) = n(n−1) at n = 200, and the refutation 19900 ≱ 20000.
  All 4 audited theorems report `does not depend on any axioms`. The
  2-cycle-is-a-cycle fact is classical and cited.

## Boundary

Only the displayed "finite DAG with ℵ₀ edges" self-contradiction is
refuted; the actual structure of Cichoń-diagram inequalities is not
addressed.
