# Disproof of conjecture `00000002308`

**Verdict: FALSE.**

This submission disproves conjecture `00000002308` as stated. The refutation is
unconditional and completely elementary: under the standard meaning of
*complete*, the symmetric group `S_3` of order `6` is solvable and complete, so
the smallest non-trivial solvable complete group has order `6`, not the claimed
`2^{11}·3 = 6144`. The claimed number is wrong under every reading of the
conjecture, including the non-solvable one.

## The conjecture

Quoted verbatim from `conjectures/00000002308.md`:

> **English.** Definition: A complete group satisfies G = Aut(G). Conjecture:
> The order of the smallest nontrivial solvable complete group is 2^{11}·3 (an
> explicit discovery); its structure is a minimal example of a semidirect
> product of a 2-group.
>
> **中文。** 定义：完全群指 G=Aut(G) 的群。猜想：最小非显然可解完全群的阶为
> 2^{11}·3(显式发现);其结构为 2-群的半直积的极小例。

## The definition

A group `G` is **complete** when

1. its center is trivial, `Z(G) = {1}`, and
2. every automorphism of `G` is inner, `Aut(G) = Inn(G)`.

Equivalently, the conjugation map `G → Aut(G)`, `g ↦ (x ↦ g x g⁻¹)`, is an
isomorphism; for a centerless group it is injective, so completeness is
`Aut(G) = Inn(G)`, whence `G ≅ Aut(G)` and `|G| = |Aut(G)|`. The trivial group
is excluded as "nontrivial".

## The witness `S_3`

Model `S_3` as the six permutations of `{0,1,2}`:

```
index 0 = id
index 1 = (12)
index 2 = (01)     <- call this tau
index 3 = (012)    <- call this sigma
index 4 = (021)
index 5 = (02)
```

The transposition `tau = (01)` and the 3-cycle `sigma = (012)` generate `S_3`:
the six words `1, tau·sigma, tau, sigma, sigma², tau·sigma²` are pairwise
distinct and exhaust the group (verified by a finite check in `reproduce.py` and
in the Lean certificate).

### Completeness of `S_3`

- **Trivial center.** A direct computation over all six elements shows that the
  only element commuting with every element of `S_3` is the identity:
  `Z(S_3) = {1}`. (E.g. `(01)(012) = (021) ≠ (012)(01) = (12)`, and likewise for
  the other transpositions and 3-cycles.)
- **`|Aut(S_3)| = 6`.** `reproduce.py` enumerates **all `6! = 720` bijections**
  `S_3 → S_3` and keeps those satisfying `f(ab) = f(a)f(b)` for all `a,b`.
  Exactly **6** of the 720 bijections are homomorphisms, so `|Aut(S_3)| = 6`.
- **`Aut(S_3) = Inn(S_3)` and `|Inn(S_3)| = 6`.** The six conjugations
  `x ↦ g x g⁻¹` are pairwise distinct, each is a bijective homomorphism, and
  the set of all six equals the set of automorphisms found above. Hence
  `Aut(S_3) = Inn(S_3)` and both have order `6`, so `S_3 ≅ Aut(S_3)`.

Therefore `S_3` is complete. An equivalent generator-based reduction (used in
the Lean proof for speed) counts the same value: a homomorphism out of `S_3` is
determined by `(f(tau), f(sigma))`, the six words force
`f(tau·sigma) = f(tau)f(sigma)` etc., and among the `6 × 6 = 36` pairs exactly
`10` extend to endomorphisms (1 trivial, 3 with image of order 2, 6
automorphisms), again giving `|Aut(S_3)| = 6`.

### Solvability and the semidirect-product structure

`A_3 = {1, sigma, sigma²}` is cyclic of order 3, hence abelian; it is normal in
`S_3` and has index `6/3 = 2`, with quotient `S_3/A_3 ≅ Z/2`, abelian. Thus the
series `1 ◁ A_3 ◁ S_3` has abelian factors `Z/3` and `Z/2`, and `S_3` is
**solvable**.

Let `T = ⟨tau⟩ = {1, tau}`, a 2-group of order `2 = 2¹`. Then
`A_3 ∩ T = {1}`, `A_3 · T` has `3·2 = 6` elements and therefore equals `S_3`,
and `A_3` is normal, so

```
S_3 = A_3 ⋊ T ≅ Z/3 ⋊ Z/2
```

is an internal **semidirect product**; the conjugation action of `T` on `A_3`
is non-trivial (`tau·sigma·tau⁻¹ = sigma⁻¹ ≠ sigma`), so it is not the direct
product `Z/6`. This is exactly the structural description the conjecture asks
for, but realised at order `6`.

## Minimality: orders 2, 3, 4, 5

Every group of order `2`, `3`, `4` or `5` is abelian. For prime order (2, 3, 5)
this is Lagrange: a non-identity element has order dividing the prime, hence
equal to it, so it generates the group, which is cyclic and abelian. For order
4: either there is an element of order 4 (the group is cyclic, abelian) or every
non-identity element has order 2 (then `g² = 1` for all `g`, abelian).

`reproduce.py` carries out an independent **exhaustive** machine check: every
group table can be relabelled into a *reduced Latin square* (first row and
column `0,1,…,n−1`), so enumerating all reduced Latin squares and retaining the
associative ones covers all groups of that order. The counts are:

| order `n` | reduced Latin squares | group tables found | non-abelian |
|:---------:|:---------------------:|:------------------:|:-----------:|
| 2 | 1 | 1 | 0 |
| 3 | 1 | 1 | 0 |
| 4 | 4 | 4 | 0 |
| 5 | 56 | 6 | 0 |

All are abelian, so no group of order `2, 3, 4, 5` is complete: each is abelian,
its center is the whole group, and that center is non-trivial. Since `S_3`, of
order `6`, is solvable and complete, **6 is the least order of a non-trivial
solvable complete group**, and `6 < 6144`.

## Literature note

The symmetric group `S_n` is complete for every `n ≠ 2, 6` (with `S_6` the
famous exception, since `Out(S_6) = Z/2`). In particular `S_3` is complete —
this is the standard folklore result and agrees with the computation above. If
one instead reads the conjecture as asking for the smallest **non-solvable**
complete group, the answer is `S_5` of order `120`: the alternating group `A_5`
of order `60` is *not* complete because `Out(A_5) = Z/2 ≠ 1`, while `S_5` is
complete (it is centerless and `Out(S_5) = 1`). Again `120 < 6144`. Under every
reading the value `2^{11}·3` is wrong.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definition, `S_3` verification, minimality, literature note, file list, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): builds `S_3`, computes the center, enumerates all 720 bijections for `Aut`, shows `Aut = Inn` of order 6, verifies solvability and `S_3 = C_3 ⋊ C_2`, exhaustively checks orders 2–5, asserts `6 < 6144`, `PASS`/`FAIL` and non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc2308`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`); generator-based automorphism count. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, performance note, encoding pitfalls, measured build times. |

## Reproducing

Python (dependency-free, runs in a fraction of a second):

```sh
python3 reproduce.py
```

It builds `S_3` as the permutations of `{0,1,2}`, computes `Z(S_3) = {1}`,
filters all `720` bijections `S_3 → S_3` for homomorphisms to get
`|Aut(S_3)| = 6`, shows the six conjugations are distinct with
`Aut(S_3) = Inn(S_3)`, verifies solvability and `S_3 = C_3 ⋊ C_2` with a
non-trivial action, exhaustively enumerates reduced Latin squares of orders
`2–5` to confirm all such groups are abelian, checks `6 < 2¹¹·3 = 6144`, prints
`PASS` and exits `0` on success.

LaTeX document:

```sh
mkdir -p build
tectonic --outdir build main.tex
```

(produces `build/main.pdf`; the `build/` directory must exist, after which it is
reused).

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0` in about `2.6` seconds (measured); `Check.lean` prints
`#print axioms` for every theorem and reports no `sorryAx` — most theorems
depend only on `propext`, and `card_S3` and `six_lt_6144` on no axioms at all.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (project `tlmc2308`, library
  `Main`, no dependencies), `Main.lean`, `Check.lean`, and `lean4/README.md`.
  It formalises `card_S3`, `center_trivial`, `card_inn`, `card_aut`,
  `aut_eq_inn`, `A3_normal`, `A3_index2`, `A3_abelian`, `six_lt_6144` and the
  collected `conjecture_00000002308_false`, using core Lean only (no Mathlib)
  and containing no `sorry`; the audit reports no `sorryAx`.
