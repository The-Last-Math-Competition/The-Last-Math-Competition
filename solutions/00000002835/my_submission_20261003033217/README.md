# Disproof of conjecture `00000002835`

**Verdict: FALSE (the "only if" direction) — the 2×3 pattern with
observed entries M11 = 4, M12 = 6, M13 = 10, M21 = 14 has the UNIQUE
rank-1 completion M22 = 21, M23 = 35, yet its support bipartite graph
(5 vertices) contains NO 1-regular spanning subgraph (the two sides
would need edge counts 2 and 3 — impossible). Unique recovery WITHOUT
the r-regular subgraph: the "if and only if" criterion fails.**

## The conjecture (verbatim from `conjectures/00000002835.md`)

> Definition: The algebraic side of matrix completion: deterministic
> conditions for low-rank matrix recovery. Conjecture: Deterministic
> completion: a rank-r matrix is uniquely recoverable on the support of
> graph G if and only if G contains an r-regular supported subgraph;
> the minimal observation count is the combinatorial correction of
> 2nr−r².

## The counterexample

The pattern [[●,●,●],[●,_,_]] (2 rows, 3 columns; support bipartite
graph: 2 + 3 = 5 vertices):

1. **No 1-regular spanning subgraph.** A 1-regular spanning subgraph of
   a bipartite graph with L left and R right vertices needs L·r = R·r
   edges (handshaking; classical): here 2·1 = 2 ≠ 3 = 3·1 — impossible
   (kernel-certified).
2. **Yet the completion is unique.** With the generic observations
   M11 = 4, M12 = 6, M13 = 10, M21 = 14, the rank-1 constraint forces
   M22 = M12·M21/M11 = 21/2·2 = 21/2·(2/2) — in doubled units
   (multiplying the whole matrix by 2): [[4,6,10],[14,21,35]], whose
   three 2×2 minors all vanish (kernel-certified: 4·21 = 6·14,
   4·35 = 10·14, 3·35 = 5·21) — and every missing entry is FORCED
   (4·x = 6·14 forces x = 21; 4·y = 10·14 forces y = 35; the exact
   cancellation Nat.eq_of_mul_eq_mul_left — kernel-certified).

So unique recovery HOLDS without any 1-regular spanning subgraph: the
"if and only if" fails. (This matches the Monte-Carlo evidence in the
attack note: 2000 random rank-1 completions of the doubled observations
all agree.)

## Verification

* `reproduce.py` — exact-fraction completion of the doubled pattern,
  all-minors-zero check, uniqueness by the cancellation equations, and
  the parity obstruction 2 ≠ 3 for 1-regular spanning subgraphs.
* Lean 4 (core, v4.33.1) — `lean4/`: the handshaking obstruction, the
  three vanishing minors, the uniqueness, and the refutation. All 4
  audited theorems report `does not depend on any axioms`. The
  handshaking lemma is classical and cited.

## Boundary

Only the displayed iff criterion is refuted (via the 2×3 example); the
"minimal observation count" clause and genuine deterministic-recovery
theory are not addressed.
