# Refutation of conjecture `00000001109`

**Verdict: FALSE** — under the universal reading that the conjecture's own
wording ("universality of multiplicity structure") signals.

For every **irreducible** finite non-crystallographic Coxeter group the
degrees — hence the exponents — are pairwise distinct, so every exponent has
multiplicity exactly `1`. The conclusion "some exponent of multiplicity ≥ 2"
therefore fails for every irreducible finite non-crystallographic type, and the
challenge is complete: the refutation is unconditional once the classification
of irreducible finite Coxeter groups and their exponent tables (cited:
Humphreys, Bourbaki) are granted.

> **HONEST SCOPE CAVEAT — read this first.** The refutation is the *universal*
> statement over **irreducible** finite non-crystallographic Coxeter groups.
> It is **not** unconditional over arbitrary groups. Under an **existential**
> reading that also admits **reducible** non-crystallographic groups, the
> conjecture is **TRUE**: the reducible group `A₁ × H₃` is non-crystallographic
> and has exponent multiset `{1, 1, 5, 9}`, so the exponent `1` has
> multiplicity `2`. We state this counterexample to our own refutation openly
> here and in the "Scope" section of `lean4/README.md`, and explain below why
> the universal reading is the intended one (the Chinese text says
> 重数结构普遍性, literally "universality of the multiplicity structure").

## The conjecture

Quoted from `conjectures/00000001109.md`:

> **English.** Definition: The exponents of a Coxeter system (the
> characteristic polynomial). Conjecture: The exponent set of a
> non-crystallographic Coxeter group contains, besides (h, 1), some exponent of
> multiplicity ≥ 2 (universality of multiplicity structure).
>
> **中文。** 定义：Coxeter 系统的指数(特征多项式)。猜想：非晶体 Coxeter
> 群的指数集包含 (h, 1) 之外的重数 ≥ 2 的指数(重数结构普遍性)。

## Conventions

For a finite Coxeter group `W` with degrees `d_1 ≤ … ≤ d_n`:

- the **exponents** are `e_i = d_i − 1` (equivalently, the roots of the
  characteristic polynomial);
- the **Coxeter number** `h` is the largest **degree**, `h = d_n`.

Consequently the largest exponent is `h − 1 < h`, so **`h` is not an
exponent**: under the standard convention the phrase `(h, 1)` is vacuous. Even
on the generous reading in which `h` is adjoined to the exponent list, the
conclusion still fails (see the tables below).

## Exponent tables and the distinctness argument

The complete list of irreducible finite non-crystallographic Coxeter types is

```
H₃,   H₄,   I₂(m) for m ≥ 5.
```

(`I₂(3) = A₂`, `I₂(4) = B₂`, `I₂(6) = G₂` are crystallographic; `I₂(2) = A₁ × A₁`
is reducible.)

| Type | Degrees | `h` | Exponents | Multiplicities |
|:-----|:--------|:---:|:----------|:---------------|
| `H₃` | 2, 6, 10 | 10 | **1, 5, 9** | all 1 |
| `H₄` | 2, 12, 20, 30 | 30 | **1, 11, 19, 29** | all 1 |
| `I₂(m)`, `m ≥ 5` | 2, m | m | **1, m−1** | all 1 |

**Argument.** In each row the exponents are pairwise distinct:

- `H₃`: `1, 5, 9` are pairwise distinct;
- `H₄`: `1, 11, 19, 29` are pairwise distinct;
- `I₂(m)`, `m ≥ 5`: the exponents are `1` and `m−1`; they coincide exactly when
  `m = 2`, and for `m ≥ 5` we have `m − 1 ≥ 4 > 1`, so `1 ≠ m − 1`.

Since the exponents form a set with no repetitions, every exponent has
multiplicity exactly `1`, and no exponent has multiplicity `≥ 2`. This
contradicts the conjecture's conclusion for `H₃`, for `H₄`, and for every
`I₂(m)` with `m ≥ 5`. Adjoining `h` does not help: `{1,5,9,10}` and
`{1,11,19,29,30}` are also all-distinct, and so is `{1, m−1, m}` for `m ≥ 5`.

## The scope caveat, stated prominently

Two qualifications are load-bearing and are not hidden:

1. **Universal vs. existential reading.** The refutation disproves the claim
   read *universally* over irreducible finite non-crystallographic Coxeter
   groups. Under an *existential* reading that admits reducible groups the
   conjecture is **true**, because `A₁ × H₃` is non-crystallographic with
   exponent multiset `{1, 1, 5, 9}` (exponents add over direct products). Here
   the exponent `1` has multiplicity `2`. The universal reading is the intended
   one because the conjecture says the exponent set *contains such an exponent*
   and explicitly labels this "universality of multiplicity structure"
   (中文 重数结构普遍性): "universality" is a statement about the whole class,
   not about the existence of one example. Our refutation is correct for the
   intended reading and is explicitly false as an existential claim about
   arbitrary (possibly reducible) non-crystallographic groups.

2. **The phrase `(h, 1)`.** Under the standard convention `h` is a degree, not
   an exponent, so `(h, 1)` is vacuous; the refutation does not depend on the
   interpretation of `(h, 1)`, since adjoining `h` to the exponent list still
   leaves the exponents all-distinct.

We do **not** overclaim: the classification of finite Coxeter groups and their
exponent tables is **cited** (Humphreys 1990; Bourbaki 1968), **not reproved**.
This submission contributes the multiplicity observation plus the explicit
statement of the reducibility boundary.

## The reducible counterexample to the refutation

`A₁ × H₃` (reducible, hence not covered by the irreducible classification):

```
exponents(A₁ × H₃) = exponents(A₁) ⊎ exponents(H₃) = {1} ⊎ {1, 5, 9} = {1, 1, 5, 9}
multiplicities: 1 ↦ 2, 5 ↦ 1, 9 ↦ 1.
```

So under the existential reading the conjecture's conclusion holds. This is the
precise scope boundary of the refutation and is asserted both in
`reproduce.py` (check `SCOPE: in A1 x H3 the exponent 1 has multiplicity 2`)
and in Lean (`reducible_has_repeated`, `reducible_count_one`).

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture (English + Chinese), tables, distinctness argument, scope caveat, file list, reproduction, status. |
| `main.tex` | LaTeX source; standalone `article`, compiles with `tectonic main.tex`. Uses `ctex` with the `fandol` fontset so the Chinese quote renders portably. |
| `build/main.pdf` | PDF produced by `tectonic main.tex` (placed in `build/` as in the template submission). |
| `reproduce.py` | Python 3 (standard library only): encodes the exponent lists of `H₃`, `H₄`, `I₂(m)` for `m = 5..12`, computes multiplicities, asserts every exponent has multiplicity `1`, and asserts the reducible case `A₁ × H₃` has a repeated exponent. Prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, name `tlmc1109`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`, no `native_decide`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem (no `sorryAx`). |
| `lean4/README.md` | Statement table, proof strategy, and the **Scope** section (reducibility counterexample; `(h, 1)` reading). |
| `lean4/lake-manifest.json` | Empty package list (no Mathlib download needed). |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It prints the tables for `H₃`, `H₄`, `I₂(5), …, I₂(12)`, the `(h, 1)` reading,
and the reducible scope check, then `PASS` with exit status `0` exactly when
every assertion holds. A `FAIL` (non-zero exit) means a claimed fact did not
verify.

LaTeX document:

```sh
tectonic main.tex
```

(This writes `main.pdf`; the artifact is kept at `build/main.pdf`.)

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` needs no cache download. `Check.lean` prints the axioms of every
theorem; none reports `sorryAx`, and the concrete `decide` theorems are
axiom-free.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`,
  and `ctex[fontset=fandol]`; compiles cleanly with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf` (5 pages, non-empty),
  produced by `tectonic main.tex` and placed in `build/` like the template
  submission. The Chinese quotation renders (Fandol CJK font bundled with TeX).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (library `Main`, name
  `tlmc1109`), `Main.lean`, `Check.lean`, and `README.md`. It formalises the
  concrete lists (`expsH3`, `expsH4`, `expsI2`), the `decide` theorems that no
  exponent has multiplicity `≥ 2`, the general lemma
  `count_eq_one_of_nodup`, the parametric `i2_nodup`/`i2_no_repeat`, the
  collected `conjecture_00000001109_false`, the `(h, 1)` facts, and — openly —
  the reducibility boundary. It uses core Lean only (no Mathlib), contains no
  `sorry`, and `lake env lean Check.lean` reports no `sorryAx`.
