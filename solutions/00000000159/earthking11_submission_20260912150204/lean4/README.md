# Lean 4 formalisation for conjecture `00000000159`

**Verdict: FALSE** — the arithmetic core of the edge-count obstruction is
formalised here in core Lean 4 (`import Std`, **no Mathlib**), with no `sorry`.

## Build

```bash
cd lean4
lake build
lake env lean Check.lean     # prints the axiom footprint of every theorem
```

## Statement table

| Lean name | informal statement |
|---|---|
| `validLengths` | the four available prime cycle lengths for `K_11`, i.e. `[3,5,7,11]` |
| `edgeCount p` | the number of edges of `K_p`, i.e. `p * (p - 1) / 2` |
| `isPrime n` | a self-contained computable primality test (`Nat.Prime` is Mathlib-only) |
| `prime_mem_validLengths` | a `List.all` check over `List.range 12`: every `p` in `[3,11]` with `isPrime p = true` belongs to `validLengths` |
| `validLengths_sum` | `[3,5,7,11].sum = 26` |
| `del`, `del_mem_of_mem`, `del_nodup`, `del_sum`, `del_not_mem` | removal helper and its basic laws |
| `sublist_sum_le` | if `L.Nodup` and every `x ∈ L` lies in `A`, then `L.sum ≤ A.sum` |
| `sum_validLengths_le` | a duplicate-free list of available lengths has sum `≤ 26` |
| `no_sum_55` | no such list has sum `55` |
| `conjecture_00000000159_false` | if such a list totals `edgeCount 11`, we get `False` |
| `conjecture_00000000159_false_cover` | the same for the weaker covering reading (`edgeCount 11 ≤ L.sum`) |

`Check.lean` prints `#print axioms` for each of these. Because the development
uses only core Lean plus `Std`, the expected output is that no theorem depends
on any axiom beyond core (no `sorryAx`, no `Classical.choice`).

## Proof strategy

1. `validLengths` is the concrete list `[3, 5, 7, 11]`; `validLengths_sum`
   evaluates its sum to `26` by `decide`.
2. `sublist_sum_le` is proved by structural recursion on `A`. If a duplicate-free
   `L` has all members in `a :: t`, either it contains `a` — then `del_sum`
   splits off one copy of `a`, `del_not_mem` shows the removal introduces no
   `a`, and the induction hypothesis bounds the remainder by `t.sum` — or it
   does not, and then all of `L` already lies in `t` and the induction
   hypothesis applies directly.
3. `sum_validLengths_le` instantiates `A = validLengths` and evaluates the
   bound `validLengths.sum = 26`.
4. `no_sum_55` combines the bound with `26 < 55`; the two main theorems feed it
   the edge count `edgeCount 11 = 11 * 10 / 2` in the exact and covering
   readings respectively.

## Scope of the formalisation (read this)

Only the **arithmetic core** of the disproof is formalised. Concretely, the Lean
theorem says:

> there is no duplicate-free list `L` of members of `{3,5,7,11}` whose sum
> equals (or, in the covering version, is at least) `C(11,2) = 55`.

The graph-theoretic reduction *to* that arithmetic statement is **not**
formalised. Two bridges are taken on paper and are elementary:

1. A cycle of a simple graph has length equal to its number of distinct
   vertices, hence at least `3` and at most `p` for a cycle in `K_p`
   (`main.tex`, Lemma 1). So the cycle lengths of a cover of `K_11` are
   pairwise distinct primes drawn from `{3,5,7,11}`.
2. An edge-disjoint decomposition has total length exactly `|E(K_11)| = 55`,
   and a mere cover has total length at least `55`.

Formalising (1) would require a graph library (vertices, walks, simple cycles)
that is far beyond core Lean; (2) is immediate from the definitions. We chose to
keep the development dependency-free and `sorry`-free rather than to import
Mathlib or to state an unproved bridge. The formalised statement is **not
vacuous**: it genuinely rules out every list of pairwise distinct available
prime lengths from reaching the required total.

## Note on the environment

The `lean-toolchain` pins `leanprover/lean4:v4.33.1`. The development was
written to use only stable core `Std` API (`List.Nodup`, `List.mem_cons`,
`List.sum`, `decide`, `induction`, `simp`, `rw`) and deliberately avoids
Mathlib-only tactics such as `norm_num`, `linarith` and `omega`, so that it can
be built with the pinned core toolchain and no dependencies.
