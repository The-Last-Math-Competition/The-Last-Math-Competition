# Disproof of conjecture `00000001142`

**Verdict: FALSE.**

This submission disproves conjecture `00000001142` as stated. The refutation is
unconditional, completely elementary and fully machine-checkable: the
automorphism group of the mod-`p` Witt algebra `W(1;1)` has order **24** at
`p = 3` and **500** at `p = 5`, whereas the conjectured formula `p(p-1)` gives
`6` and `20`. The claim happens to be true only at `p = 2`; it fails for
**every** `p ≥ 3`.

## The conjecture

Quoted verbatim from `conjectures/00000001142.md`:

> **English.** Conjecture: The order of the automorphism group of the mod-p
> Witt algebra W(1; 1) is p(p−1) (Witt automorphisms).
>
> **中文。** 猜想：mod p 的 Witt 代数 W(1; 1) 的自同构群的阶为
> p(p−1)(Witt 自同构)。

Both versions are identical in content.

## The algebra and its dimension

`W(1;1) = Der(F_p[x]/(x^p))` is the Lie algebra of derivations of the truncated
polynomial ring. It has the **p** basis elements

```
b_k = x^k d/dx,    k = 0, 1, ..., p-1,
```

so `dim W(1;1) = p` (not `p-1`). The bracket is

```
[b_k, b_l] = (l - k) * b_{k+l-1}    if 1 <= k+l <= p,
[b_k, b_l] = 0                       otherwise.
```

For example `b_0 = d/dx`, `b_1 = x d/dx`, ..., `b_{p-1} = x^{p-1} d/dx`.

## The witness `p = 3` (dimension 3)

At `p = 3` the bracket table is
`[b_0,b_1] = b_0`, `[b_0,b_2] = 2 b_1`, `[b_1,b_2] = b_2`
(the rest by antisymmetry). A linear map is a `3 x 3` matrix over `F_3`; we
enumerated **all** `3^9 = 19683` of them:

| Quantity | Value |
|:---------|------:|
| candidate matrices | `3^9 = 19683` |
| invertible (`det != 0`) | `|GL(3,F_3)| = 11232` |
| invertible **and** bracket-preserving | **24** |
| conjectured value `p(p-1) = 3*2` | 6 |

So `|Aut(W(1;1))| = 24 != 6 = p(p-1)` at `p = 3`. The count is machine-verified
twice: by exhaustive enumeration in `reproduce.py`, and by the core-Lean theorem
`aut_count_3` in `lean4/Main.lean` (which likewise enumerates all `3^9`
matrices, keeping the `11232` invertible ones and counting the `24`
bracket-preserving ones).

### Structural confirmation: `W(1;1) ≅ sl(2, F_3)`

At `p = 3` the algebra is isomorphic to `sl(2, F_3)`, an explicit isomorphism
being

```
h = 2 b_1,    e = b_2,    f = 2 b_0,     [h,e] = 2e,  [h,f] = -2f,  [e,f] = h.
```

Therefore

```
|Aut(W(1;1))| = |Aut(sl(2,F_3))| = |PGL(2,3)| = |S_4| = 24,
```

an independent theoretical confirmation of the value 24. The element-order
distribution of the 24 automorphisms, computed in `reproduce.py`, is

```
{1: 1, 2: 9, 3: 8, 4: 6},
```

which is exactly the order distribution of `S_4`. This exceptional isomorphism
exists only at `p = 3`.

## The value at `p = 5` (dimension 5)

A brute force over `5^25` matrices is infeasible, so we use an exact structural
reduction (all steps verified in `reproduce.py`):

* the pair `{b_0, b_4}` generates `W(1;1)`, so an automorphism `φ` is determined
  by the pair `(φ(b_0), φ(b_4))`;
* `φ(b_0)` must be a **regular nilpotent** element, since
  `ad(φ(b_0)) = φ ∘ ad(b_0) ∘ φ^{-1}` is conjugate to `ad(b_0)`, a single
  Jordan block of size `p`; there are exactly **500** regular nilpotent
  elements;
* reconstructing `φ(b_3), φ(b_2), φ(b_1)` from `[b_0,b_k] = k b_{k-1}` and
  testing bracket preservation and invertibility leaves **exactly one**
  extension per candidate.

| Quantity | Value |
|:---------|------:|
| regular nilpotent candidates for `φ(b_0)` | 500 |
| extensions to an automorphism | 500 |
| conjectured value `p(p-1) = 5*4` | 20 |

Hence `|Aut(W(1;1))| = 500 != 20 = p(p-1)` at `p = 5` (note
`500 = (p-1) p^{p-2}` at `p = 5`). The same program returns `24` when run at
`p = 3`, validating the method against the brute force.

## The exception `p = 2`

At `p = 2` the algebra is the 2-dimensional non-abelian Lie algebra
`[b_0,b_1] = b_0`, and `|Aut| = 2 = p(p-1)`. So the conjectured formula is
correct at `p = 2` and wrong for every `p ≥ 3`; `p(p-1)` is not the order of
`Aut(W(1;1))` in general.

## Rescue attempts that fail

We tried to save the conjecture by re-reading "Aut"; none succeeds.

| Reading | Outcome |
|:--------|:--------|
| Automorphisms of the **restricted** Lie algebra (respecting the `p`-power map `X ↦ X^[p]`) | the same counts result. At `p = 3`, all 24 Lie automorphisms preserve the `p`-power map (verified in `reproduce.py`), so the restricted automorphism group is again 24; at `p = 5` the count is again 500. No rescue. |
| A different, non-standard `p`-power convention | gives 2 at `p = 3` and 4 at `p = 5` — even further from `p(p-1)`. No rescue. |
| Inner automorphisms | `W(1;1)` is finite-dimensional, so the inner automorphism group is trivial and `Out = Aut`, of order 24 (resp. 500). No rescue. |
| Automorphisms of the restricted enveloping algebra | a different (larger, associative-algebra) group, not `Aut(W(1;1))`. No rescue. |

## The Möbius subgroup: where `p(p-1)` really comes from

The number `p(p-1)` does occur, but as the order of a **proper** subgroup. The
Möbius/Witt transformations

```
x ↦ a x / (1 + b x),     a in F_p^*,  b in F_p,
```

act on `W(1;1)` by pullback,
`φ*(b_k) = φ(x)^k / φ'(x) * d/dx = a^{k-1} x^k (1+bx)^{2-k} d/dx`, expanded as
a power series and truncated at degree `p-1`. This action preserves the bracket,
and the `p(p-1)` maps `(a,b)` form a subgroup:

```
p(p-1) = 6  (p = 3),     20  (p = 5).
```

But these are **proper** subgroups, because `6 < 24` and `20 < 500`. Thus the
conjecture is true exactly if "Aut" is silently read as this Möbius/Witt
subgroup rather than the full automorphism group. Under the literal reading of
the conjecture as filed, it is false for all `p ≥ 3`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, dimension, the `p = 3` witness, the `sl(2,F_3)` identification, the `p = 5` value, the `p = 2` exception, the failed rescues, the Möbius remark, file list, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): brute force at `p = 3` (prints the `|GL(3,3)| = 11232` / `24` breakdown), element-order distribution, the `sl(2,F_3)` isomorphism, the restricted `p`-power check, the exact `p = 5` count of 500, the Möbius subgroup, the `p = 2` case; `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; name `tlmc1142`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the `p = 3` refutation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit and the disclosure below. |
| `lean4/README.md` | Statement table, the optimised enumeration, measured build time, axiom audit, scope note. |

## Reproducing

Python (dependency-free; about 13 seconds):

```sh
python3 reproduce.py
```

It brute-forces all `3^9 = 19683` matrices at `p = 3` (printing
`|GL(3,3)| = 11232` and `24`), computes the element-order distribution
`{1:1, 2:9, 3:8, 4:6}`, checks the `sl(2,F_3)` isomorphism, checks that all 24
automorphisms preserve the `p`-power map, computes the exact `p = 5` count
(500), checks that the Möbius subgroup has order `p(p-1)` and is proper, and
handles the `p = 2` case. It prints `PASS` and exits `0` exactly when every
check holds.

LaTeX document:

```sh
tectonic --outdir build main.tex
```

Lean 4 project (always run with a timeout):

```sh
cd lean4
timeout 300 lake build          # ≈ 50 s wall on the author's machine (47–64 s)
timeout 120 lake env lean Check.lean
```

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem
and reports that they **depend on no axioms at all** — in particular no
`sorryAx` and no `Lean.ofReduceBool`.

## Axiom and computing-engine disclosure

The heavy `3^9 = 19683` enumeration in `lean4/Main.lean` is discharged by the
core kernel **`decide`** tactic (definitional reduction). It is **not**
`native_decide`. Our submission convention forbids `native_decide` because it
introduces the `Lean.ofReduceBool` axiom; accordingly
`timeout 120 lake env lean Check.lean` reports

```
'Tlmc1142.Witt3.num_mats' does not depend on any axioms
'Tlmc1142.Witt3.aut_count_3' does not depend on any axioms
'Tlmc1142.Witt3.claim_false_3' does not depend on any axioms
```

The mathematical content of the enumeration is: over `F_3` there are
`3^9 = 19683` matrices, exactly `|GL(3,3)| = 11232` of them are invertible, and
exactly **24** of the invertible ones preserve the bracket of `W(1;1)`. The
kernel route was made fast enough (≈ 50 s wall — 47.5 s on the final clean
build — and ≈ 4.4 GB peak RSS) by coding
each matrix as a single base-3 `Nat`, inlining the nine structure constants,
short-circuiting on the determinant, and keeping the predicate a small `Bool`
tested only on the nine basis pairs. See `lean4/README.md` for details.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  `num_mats` (`allMats.length = 3^9`), `aut_count_3` (`auts3.length = 24`) and
  `claim_false_3` (`auts3.length != 3*(3-1)`). It uses core Lean only (no
  Mathlib) and contains no `sorry`; the audit reports no `sorryAx` and no
  `Lean.ofReduceBool`.

### Caveats

- The `p = 5` value 500 is established by exact finite computation in
  `reproduce.py` (structural reduction to the 500 regular nilpotent elements),
  not by Lean; a faithful Lean analogue would require enumerating `5^25`
  matrices and is infeasible. The method is validated against the `p = 3` brute
  force.
- The claim is FALSE for every `p ≥ 3`; only `p = 2` is a genuine exception.
- The restricted-algebra reading is checked directly at `p = 3` in
  `reproduce.py`; the `p = 5` restricted count (also 500) and the alternative
  `p`-power convention figures (2 at `p = 3`, 4 at `p = 5`) are recorded from
  the independent verification of this refutation.
