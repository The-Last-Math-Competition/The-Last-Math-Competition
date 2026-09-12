# Disproof of conjecture `00000001668`

**Verdict: FALSE.** Both branches of the classification table are wrong, and
the failure of the "4 otherwise" branch is *structural*: the value 4 is
unattainable for **every** admissible `(n, k)`.

## The conjecture

> **Definition:** The circular chromatic number of the generalized Petersen
> graph G(n,k) is the minimum number of colors in a circular coloring (colors
> increasing along distance). **Conjecture:** The complete classification
> table: χ_c(G(n,k)) = 3 when n ≡ 0 mod 3 and k ≡ 1 mod 3, and 4 otherwise
> (consistent with computations for n ≤ 30); the table is closed for all n and
> k.

## Reading used

The gloss "colors increasing along distance" is not the standard definition of
a circular colouring and is ambiguous as written. We refute the conjecture
under the **standard** definition, which is the only reading under which the
numerical table in the conjecture is meaningful:

- `G(n,k)` has vertices `u₀…u_{n−1}`, `v₀…v_{n−1}` and edges `uᵢuᵢ₊₁`,
  `vᵢvᵢ₊ₖ`, `uᵢvᵢ` (indices mod `n`), for `n ≥ 3` and `1 ≤ k ≤ n/2`.
- A `(p,q)`-colouring is `c : V → ℤ_p` with `q ≤ |c(x) − c(y)|_p ≤ p − q` on
  every edge, where `|d|_p = min(d mod p, p − (d mod p))`.
- `χ_c(G) = min { p/q : G has a (p,q)-colouring }`.

## Why it is false

### The "4 otherwise" branch is impossible — structurally

For every admissible `(n,k)` the graph `G(n,k)` is connected and has maximum
degree exactly 3. (Outer vertices have degree 3 always; inner vertices have
degree 3 when `k < n/2`, and degree 2 when `k = n/2`, since then the inner star
polygon degenerates to a perfect matching. In all cases `Δ = 3`.)

`G(n,k)` is never `K₄`: it has `2n ≥ 6` vertices. **Brooks' theorem** then gives

```
χ(G(n,k)) ≤ 3.
```

Since `χ_c(G) ≤ χ(G)` always, we get

```
χ_c(G(n,k)) ≤ 3 < 4
```

for **every** admissible `(n,k)`. The "4 otherwise" branch can therefore never
hold. This is not a boundary case or an arithmetic slip — it is a statement
about the classification framework. No repair of the form "change 4 to some
other constant" can work either, since the "otherwise" value would have to be
attainable on the complement of the `S₃` branch, where `χ_c ∈ (χ − 1, χ]` with
`χ ≤ 3`.

### The "3" branch also fails

Take `n = 6`, `k = 1`. Then `n ≡ 0 mod 3` and `k ≡ 1 mod 3`, so the conjecture
predicts `χ_c = 3`. But `G(6,1)` is the hexagonal prism `C₆ × K₂`, which is
**bipartite**, so `χ(G(6,1)) = 2` and hence `χ_c(G(6,1)) ≤ 2`. The predicted
value 3 is wrong. The same applies to `(12,1)` and `(18,7)`.

So **neither branch is right**, and there is no branch the conjecture gets
correct.

### Explicit values with certificates

| `n` | `k` | `\|V\|` | `χ` | `χ_c` | predicted | how certified |
|---|---|---|---|---|---|---|
| 5 | 1 | 10 | 3 | **5/2** | 4 | exact: `(5,2)`-colouring + contains `C₅` |
| 6 | 1 | 12 | 2 | **2** | 3 | exact: bipartite + has an edge |
| 7 | 1 | 14 | 3 | **7/3** | 4 | exact: `(7,3)`-colouring + contains `C₇` |
| 5 | 2 | 10 | 3 | 3 | 4 | search only (rigorous: `χ_c ≤ χ = 3`) |
| 7 | 2 | 14 | 3 | 3 | 4 | search only (rigorous: `χ_c ≤ χ = 3`) |
| 7 | 3 | 14 | 3 | 3 | 4 | search only (rigorous: `χ_c ≤ χ = 3`) |

Certificates (a `(p,q)`-colouring of `ℤ_p`, with zero violating edges):

```
G(5,1)  (5,2)-colouring   p/q = 5/2
   outer u_0..u_4 = [0, 2, 4, 1, 3]
   inner v_0..v_4 = [2, 4, 1, 3, 0]

G(7,1)  (7,3)-colouring   p/q = 7/3
   outer u_0..u_6 = [0, 3, 6, 2, 5, 1, 4]
   inner v_0..v_6 = [3, 6, 2, 5, 1, 4, 0]

G(6,1)  (2,1)-colouring   p/q = 2
   outer u_0..u_5 = [0, 1, 0, 1, 0, 1]
   inner v_0..v_5 = [1, 0, 1, 0, 1, 0]
```

**Smallest counterexample to the "4" branch: `G(5,1)`**, the pentagonal prism,
with `χ_c = 5/2` against a predicted 4. The value is exact on both sides: the
`(5,2)`-colouring gives `≤ 5/2`, and `G(5,1)` contains the 5-cycle `C₅`, giving
`≥ χ_c(C₅) = 5/2`.

**Smallest counterexample to the "3" branch: `G(6,1)`**, bipartite, with
`χ_c = 2` against a predicted 3.

Rows marked "search only" report the minimum found by exhaustive
`(p,q)`-search with `p ≤ |V|`. For those we claim only the rigorous bound
`χ_c ≤ χ = 3`, which already refutes the predicted value 4. We have separated
the rigorously certified entries from the computational ones so a reviewer can
weigh them accordingly. **None of the exact values is load-bearing**: the
refutation rests only on `χ_c ≤ χ` and Brooks' theorem.

## Scope of the sweep

Over the **96** admissible pairs with `5 ≤ n ≤ 20` (including `k = n/2`), the
bound `χ_c ≤ χ` refutes **89** outright — exactly those pairs with
`χ(G(n,k)) < prediction`.

The remaining **7** are `(9,1), (9,4), (12,4), (15,1), (15,4), (15,7), (18,4)`,
all with `n ≡ 0 mod 3`, `k ≡ 1 mod 3` and `χ = 3`.

**This does not mean those cases are verified.** The test applied is
`χ ≥ prediction`, a *necessary* condition derived from `χ_c ≤ χ`. Passing it
means only that this one inequality does not already refute the case — it is
possible that `χ_c < 3` for some of them. We make no claim either way, and we
deliberately avoid describing them as "the branch the conjecture gets right",
which would be an overclaim. Note that `(6,1)`, `(12,1)` and `(18,7)` satisfy
`n ≡ 0 mod 3`, `k ≡ 1 mod 3` yet are refuted, because `χ = 2 < 3`.

## The definitional fork at k = n/2

Some authors restrict the definition to `k < n/2`. We include `k = n/2`
because the conjecture quantifies over "all n and k". At `k = n/2` the graph is
only subcubic (`Δ = 3`, inner vertices of degree 2), and Brooks' theorem needs
only the maximum degree, so the conclusion is unaffected. Under the restricted
convention one simply deletes those 9 cases; the refutation does not depend on
them.

## Files

| file | purpose |
|---|---|
| `main.tex` | the proof (LaTeX) |
| `build/main.pdf` | compiled PDF, built with `tectonic` |
| `reproduce.py` | verifies `Δ = 3`, connectedness, `χ ≤ 3`; computes exact `χ_c` with certificates; runs the sweep |
| `lean4/` | Lean 4 formalisation — **status: complete**, zero `sorry`, core Lean only |

## Reproducing

Pure Python 3, standard library only:

```bash
python3 reproduce.py
```

Output: the structural table (99 graphs for `3 ≤ n ≤ 20`, all connected with
`Δ = 3` and `χ ≤ 3`), the exact `χ_c` values with their certificates, and the
sweep reporting 96 cases with 89 refuted.

## Status against the submission rules

Rule 3 requires LaTeX, a compiled PDF, and a Lean 4 project. All three are here.

| artefact | where | how to check |
|---|---|---|
| LaTeX source | `main.tex` | — |
| compiled PDF | `build/main.pdf` | `mkdir -p build && tectonic main.tex --outdir build` |
| Lean 4 project | `lean4/` | `cd lean4 && lake build && lake env lean Check.lean` |

The Lean 4 project is **complete**: it compiles with core Lean 4 (no Mathlib, no
`lake exe cache get`, no network access), contains no `sorry`, and every theorem
depends only on `[propext, Quot.sound]`.

**One scope boundary, stated explicitly.** The Lean file formalises the two
explicit finite certificates — `G(5,1)` with its `(5,2)`-colouring and `G(6,1)`
with its `(2,1)`-colouring — which by themselves refute both branches of the
classification table. It does **not** formalise §3's stronger structural claim
that `χ_c(G(n,k)) ≤ 3` for every admissible `(n,k)`, because that rests on
Brooks' theorem. Brooks' theorem is neither formalised nor assumed; it does not
appear in the Lean source in any form. The structural argument therefore
remains a LaTeX-only result, while the refutation of the conjecture itself is
formalised unconditionally. See `lean4/README.md` for the details.
