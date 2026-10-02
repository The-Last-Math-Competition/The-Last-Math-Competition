# Disproof of conjecture `00000002310`

**Verdict: FALSE — the natural action of S₉ is an almost-simple group
action with base size exactly 8 > 7, so the supremum of base sizes over
almost simple groups is at least 8, not 7.**

## The conjecture (verbatim from `conjectures/00000002310.md`)

> Definition: The base size b(G) is the minimal size of a base with
> trivial pointwise stabilizer. Conjecture: The supremum of b over
> almost simple groups is 7 (attained by the action of Sp₈(2)); the
> complete exception table for b = 6 or 7 contains exactly 3 groups.

## The counterexample: S₉ in its natural action

S₉ (n ≥ 5) is almost simple (classical: A₉ is nonabelian simple and
has index 2 in S₉). Its base size acting on {0, …, 8}:

1. **8 points always form a base.** Any permutation fixing 8 of the 9
   points also fixes the ninth: if f(m) = j ≠ m then f j = j = f m,
   contradicting injectivity (kernel-certified, via the trichotomy on
   f(m) vs m).
2. **7 points do not.** The transposition (0 8) fixes all of
   {1, …, 7} pointwise and is not the identity (it moves 0) — so the
   pointwise stabilizer of any 7-set that omits two points contains a
   nontrivial element; kernel-certified with the explicit swap on
   [0, 9): injective, in-range, fixes 1..7, moves 0.

Hence b(S₉, natural) = **8 > 7**: the claimed supremum is false, and
Sp₈(2) does not attain it.

## Verification

* `reproduce.py` — brute-forces all permutations of 9 points: computes
  the minimal base size (8, exhaustively over subsets and the full
  symmetric group S₉ = 362880 elements), and lists a nontrivial
  stabilizer element for each 7-subset.
* Lean 4 (core, v4.33.1) — `lean4/`: the swap's trichotomy, injectivity,
  range, the 7-point failure, the 8-point sufficiency (trichotomy +
  injectivity), and the refutation 7 ≱ 8. All 6 audited theorems report
  `does not depend on any axioms`. Permutations are formalized as
  injective self-maps of [0, 9) — base size needs only injectivity and
  pointwise fixing, no group machinery. S₉'s almost-simplicity is
  classical.

## Boundary

Only the supremum claim is refuted; the "exception table contains
exactly 3 groups" clause for b = 6 or 7 is not addressed.
