# Disproof of conjecture `00000000471`

**Verdict: FALSE.** The conjectured closed form for the number of hypertrees of
`K_n^{(3)}` is refuted twice over: it exceeds the total number of subhypergraphs
throughout the range it claims to cover, and exhaustive enumeration disagrees
with it at every `n` we can check directly.

## The conjecture

> **Definition:** A hypertree of the `r`-uniform complete hypergraph `K_n^{(r)}`
> is a minimally connected subhypergraph of its edge set; `t(K_n^{(r)})` denotes
> their count. **Conjecture:** For `r = 3`,
> `t(K_n^{(3)}) = n^{C(n−1,2)−1} · ∏_{i=1}^{n−1} f(i)` with the explicit
> polynomial `f(i) = i² − i + 1`; this formula covers all known values for
> `n ≤ 6`.

Write `Φ(n)` for the right-hand side.

## Refutation I — the counting bound (this is the one that matters)

A hypertree is a subhypergraph, and a subhypergraph of `K_n^{(3)}` is determined
by a subset of its `C(n,3)` edges. Hence

```
t(K_n^{(3)}) ≤ 2^{C(n,3)}
```

**no matter how "connected" and "minimal" are read.** The formula already
violates this at the very first case:

| n | `C(n,3)` | `2^{C(n,3)}` | `Φ(n)` | `Φ(n) / bound` |
|---|---|---|---|---|
| 3 | 1 | 2 | **3** | 1.5× |
| 4 | 4 | 16 | 336 | 21× |
| 5 | 10 | 1024 | 853125 | 833× |
| 6 | 20 | 1048576 | 57775431168 | **55099×** |

The bound is violated for every `n` with `3 ≤ n ≤ 13`, and holds from `n = 14`
onwards (where `C(n,3) ≈ n³/6` finally outgrows `≈ (n²/2)·log₂ n`). One
counterexample is enough, and every value the conjecture claims to have checked
sits inside the violated range.

At `n = 3` this is a two-line computation: `C(2,2) − 1 = 0`, so
`Φ(3) = 3⁰ · (1)(3) = 3`, whereas there are only `2^{C(3,3)} = 2` subhypergraphs
in total.

## Refutation II — exact enumeration

| n | subhypergraphs | `t(K_n^{(3)})` | `Φ(n)` |
|---|---|---|---|
| 3 | 2 | **1** | 3 |
| 4 | 16 | **6** | 336 |
| 5 | 1024 | **25** | 853125 |

- **n = 3.** The edge set has one member, `{1,2,3}`. The empty subhypergraph is
  not connected; the full one is connected and vacuously minimal. So
  `t = 1` against `Φ(3) = 3`.
- **n = 4.** One edge covers only three vertices, so two are needed; two triples
  cover all four vertices exactly when they omit different vertices, giving
  `C(4,2) = 6`, all minimal. So `t = 6` against `Φ(4) = 336`.
- **n = 5.** Exhaustive search over all 1024 subhypergraphs gives `t = 25`
  (fifteen consisting of two edges meeting in one vertex, ten consisting of
  three edges sharing a common pair), against `Φ(5) = 853125`.

`n = 6` has `2^20 = 1048576` subhypergraphs; we do not enumerate it, because
Refutation I already disposes of it.

## Robustness

Refutation I uses only that a hypertree is determined by a subset of the edge
set — which is true under any definition. It does not matter whether
connectivity is read via the 2-section, via incidence-graph connectivity, or via
any stronger notion, and it does not matter whether "minimal" means minimal by
inclusion or of minimum cardinality.

The only reading we know of that would evade the bound is one in which a
subhypergraph may also delete vertices, so that `t` counts hypertrees spanning
*any* subset of the vertex set. Under that reading the count at `n = 3` is `4`
(one spanning hypertree plus one singleton per vertex), which still disagrees
with `Φ(3) = 3`. We record this for completeness only; the standard reading —
and the one consistent with the classical `t(K_n) = n^{n−2}` — is the spanning
one.

## Verification

| what | how |
|---|---|
| the bound table and the exact counts | `python3 reproduce.py` (standard library only, recomputes everything from scratch) |
| formal proof | `lean4/` — `lake build && lake env lean Check.lean` |

The Lean project is core-only (no Mathlib, no `sorry`) and proves:

- `sublists_length` — the powerset of an `m`-set has `2^m` elements;
- `filter_length_le` and `hypertrees_le_subhypergraphs` —
  `t(K_n^{(3)}) ≤ 2^{C(n,3)}`;
- `refutation_bound_3` — `Φ(3) > t(K_3^{(3)})`;
- `refutation_bound_6` — `Φ(6) > 2^{C(6,3)}`, i.e. `57775431168 > 2^20`;
- `hypertrees3_length = 1`, `hypertrees4_length = 6`, `hypertrees5_length = 25`,
  each by `rfl`, so the kernel performs the search itself;
- `refutation_exact_3/4/5` — `Φ(n) ≠ t(K_n^{(3)})`.

**Axiom audit:** `hypertrees3/4/5_length` and the three `refutation_exact_*`
theorems **depend on no axioms at all**; the bound theorems depend on `propext`
and `Quot.sound`, inherited from the standard treatment of lists.

## Files

| file | what it is |
|---|---|
| `README.md` | this file |
| `main.tex` | LaTeX source of the write-up |
| `build/main.pdf` | compiled write-up |
| `build/log.txt` | build log |
| `lean4/Main.lean` | the formalisation |
| `lean4/Check.lean` | prints the enumerations, the theorems, and the axioms |
| `lean4/lakefile.toml`, `lean4/lean-toolchain` | Lean build configuration |
| `lean4/README.md` | how to build the Lean project |
| `reproduce.py` | standalone reproduction (standard library only) |

## Scope

We refute the closed form as stated. We make no claim about the correct value of
`t(K_n^{(3)})` beyond `n ≤ 5`, and no claim about the analogous formula for
`r ≠ 3`. The values `1, 6, 25` are reported to pin down the small cases, not to
suggest a pattern — three terms are not enough to guess one.
