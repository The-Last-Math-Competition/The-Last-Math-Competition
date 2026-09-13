# Disproof of conjecture `00000001075`

**Verdict: FALSE.**

This submission disproves conjecture `00000001075` as stated. Over the field
`F_5` the function

```
f = delta_0 - delta_1 = (1, -1, 0, 0, 0)
```

is an equality configuration of the entropic uncertainty bound
`#supp(f) + #supp(f_hat) = 6 = q + 1`, but it is **not** a Fourier translate
of an affine function `a*x + b` and its support pair is `(2,4)`, not the
claimed `(q,1) = (5,1)`. An exhaustive enumeration of all `3^5 = 243`
functions `F_5 -> {0,+-1}` shows there are exactly `32` equality
configurations, of which `20` have support pair `(2,4)` and none of those is
an affine Fourier translate. Hence both the parenthetical "(support pairs of
`q` and `1`)" and the clause "no other equality configurations exist" fail.

The refutation is unconditional and elementary. All arithmetic is exact in
`Z[omega] = Z[x]/(x^4+x^3+x^2+x+1)`; no floating point is used anywhere.

## The conjecture

> **Definition:** The entropic uncertainty principle for the finite-field
> Fourier transform states `#supp(f) + #supp(f_hat) >= q+1`.
> **Conjecture:** Equality holds exactly for Fourier translates of affine
> functions `a*x + b` (support pairs of `q` and `1`), and no other equality
> configurations exist.

Original bilingual statement as filed in `conjectures/00000001075.md`:

> **English.** Definition: The entropic uncertainty principle for the
> finite-field Fourier transform states #supp(f) + #supp(f̂) ≥ q+1.
> Conjecture: Equality holds exactly for Fourier translates of affine
> functions a·x + b (support pairs of q and 1), and no other equality
> configurations exist.
>
> **中文。** 定义：有限域傅里叶变换 f̂ 的熵不确定原理指
> #supp(f)+#supp(f̂) ≥ q+1。猜想：等号成立的函数恰为仿射函数 a·x+b 的
> Fourier 平移(即支撑为 q 与 1 的对),不存在其他等号构型。

The conjecture makes two assertions:
(i) every equality configuration is a Fourier (time-frequency) translate of
an affine function and has support pair `(q,1)` (equivalently `(1,q)`);
(ii) there are no other equality configurations.
Both are refuted below, over the prime `q = 5`.

## The witness and its exact transform

Fix a primitive fifth root of unity `omega`, so `omega^5 = 1` and
`1 + omega + omega^2 + omega^3 + omega^4 = 0`. Work in

```
Z[omega] = Z[x]/(x^4+x^3+x^2+x+1),
```

with `omega^4 = -(1 + omega + omega^2 + omega^3)`; elements are integer
4-tuples `(c0,c1,c2,c3)` standing for `c0 + c1*omega + c2*omega^2 + c3*omega^3`.

Take the witness `f = delta_0 - delta_1`, i.e. `f(0)=1`, `f(1)=-1`,
`f(2)=f(3)=f(4)=0`.

The finite-field Fourier transform is `f_hat(xi) = sum_x f(x) omega^(xi*x)`.
Only `x = 0, 1` contribute:

```
f_hat(xi) = omega^0 - omega^xi = 1 - omega^xi.
```

**`#supp(f) = 2`**, and **`f_hat(xi) = 0` iff `xi = 0`**: if `xi = 0` then
`f_hat(0) = 0`; conversely `1 - omega^xi = 0` means `omega^xi = 1`, but
`omega` has order `5` (its minimal polynomial is `x^4+x^3+x^2+x+1`, so
`omega != 1` and `xi in {1,2,3,4}` gives `omega^xi != 1`). Hence
**`#supp(f_hat) = 4`**, with exact values

| `xi` | `f_hat(xi)` | 4-tuple |
|:----:|:-----------:|:-------:|
| 0 | 0 | `(0,0,0,0)` |
| 1 | `1 - omega` | `(1,-1,0,0)` |
| 2 | `1 - omega^2` | `(1,0,-1,0)` |
| 3 | `1 - omega^3` | `(1,0,0,-1)` |
| 4 | `1 - omega^4 = 2 + omega + omega^2 + omega^3` | `(2,1,1,1)` |

Therefore

```
#supp(f) + #supp(f_hat) = 2 + 4 = 6 = 5 + 1 = q + 1.
```

So `f` **is** an equality configuration, with support pair `(2,4)` rather than
the claimed `(q,1) = (5,1)`.

## The zero-count argument: `f` is not a Fourier translate of an affine map

Write `g_{a,b}(x) = a*x + b` on `F_5`. Its zero set is:

- `a != 0`: exactly one zero, at `x = -b*a^{-1}` (a bijection of `F_5`);
- `a = 0, b != 0`: no zeros (a nonzero constant);
- `a = b = 0`: all five points (the zero function).

A time-frequency translate is `(T_{alpha,beta} h)(x) = omega^(beta*x) *
h(x + alpha)`. Since `omega^(beta*x)` is a unit in `Z[omega]` (never zero),
the zero set of `T_{alpha,beta} h` is the zero set of `h` shifted by
`-alpha`; in particular the **number** of zeros is invariant. So every
translate of an affine function has `5`, `0`, or `1` zeros.

The witness has zero set `{2,3,4}`, of size **3**. Hence no time-frequency
translate of any affine function equals `f`. The same conclusion follows from
support sizes: a nonzero affine function has support `4` or `5`, the zero
function has support `0`, translates preserve the support size, and
`#supp(f) = 2`.

This is confirmed by an exhaustive exact check over all `5^4 = 625` tuples
`(a,b,alpha,beta)`, both for the translate and for the transform of a
translate; no match exists.

**Why `F_3` is not enough.** Over `F_3` the analogue `(1,-1,0)` is a
translate of the affine function `x |-> x+1` (as a function `F_3 -> F_3`,
`-1 = 2` and `(1,2,0) = (x+1)`). Over `F_5`, `(1,-1,0,0,0)` has three zeros
while no affine function has three zeros, so it is a genuine counterexample.
This is why the witness is taken over `F_5`.

## The 32 equality configurations on `F_5`

Enumerating all `3^5 = 243` functions `f : F_5 -> {0,+-1}` and computing
`f_hat` exactly in `Z[omega]`, the equality case
`#supp(f) + #supp(f_hat) = 6` occurs for exactly **32** functions:

| `#supp(f)` | description | count |
|:----------:|:------------|:-----:|
| 1 | the ten functions `+-delta_p`, `p in F_5` | 10 |
| 2 | the twenty functions `+-(delta_p - delta_q)`, `p != q` | 20 |
| 5 | the two nonzero constants `+-1` | 2 |
| | **total** | **32** |

Facts verified by `reproduce.py`:

- The uncertainty bound `#supp(f) + #supp(f_hat) >= 6` holds for every
  **nonzero** function among the 243 (the minimum is `6`; only `f = 0` gives
  `0`, as it must).
- The `20` functions of type `(2,4)` are exactly `+-(delta_p - delta_q)` for
  the ten unordered pairs `{p,q}` (two signs each), and **none** of them is a
  time-frequency translate of an affine function.
- The type-`(5,1)` functions are the two nonzero constants; the type-`(1,5)`
  functions are the ten `+-delta_p`, the Fourier duals of the constants. Thus
  the whole affine/Fourier-dual family accounts for only `2 + 10 = 12` of the
  `32` equality configurations; the remaining `20` are the extra ones whose
  existence the conjecture denies.

This refutes clause (ii) ("no other equality configurations exist") and shows
clause (i) is incomplete: the witness (and `19` others) have support pair
`(2,4) != (5,1)`.

## Context: the premise is not a general theorem

The bound `#supp(f) + #supp(f_hat) >= q+1` is **false** for general `q`; only
its prime-field case is used above. For `q = p^k`, `k >= 2`, let `H <= F_q` be
the subgroup of size `p^(k-1)` (equivalently a hyperplane of the additive
group). Then `f = 1_H` has Fourier transform supported on the annihilator
`H^perp`, another hyperplane of size `p^(k-1)`, so

```
#supp(f) + #supp(f_hat) = p^(k-1) + p < p^k + 1 = q + 1   (k >= 2).
```

For example, over `F_4 = F_2[t]/(t^2+t+1)` the subgroup `{0,1}` and its
annihilator both have size `2`, giving `2 + 2 = 4 < 5` (checked in
`reproduce.py`). For **prime** `q` the bound does hold for nonzero `f`, as the
`q = 5` enumeration confirms. Choosing the prime `q = 5` keeps the
counterexample inside the regime where the premise is true, so the refutation
is not an artifact of a false hypothesis.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the witness, the zero-count argument, the 32-configuration enumeration, reproduction commands, and the submission-rule status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by the Tectonic build of `main.tex`. |
| `reproduce.py` | Python 3 (standard library only) exact `Z[omega]` arithmetic: the witness transform, the exhaustive non-membership checks, the 243-function enumeration, and the `q = 4` context check. Asserts everything and prints `PASS`/`FAIL`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

The numerical checks are dependency-free and run in well under a second:

```sh
python3 reproduce.py
```

It prints the witness transform `f_hat = (0, 1-w, 1-w^2, 1-w^3, 1-w^4)`, the
support values `2` and `4`, the exhaustive checks over `5^4 = 625` tuples,
the `243`-function enumeration with the `10/20/2` split, and ends with
`PASS`; a `FAIL` (non-zero exit status) means some claimed fact did not
verify.

The LaTeX document is built with:

```sh
tectonic main.tex            # writes ./main.pdf
tectonic --outdir build main.tex   # writes build/main.pdf (as shipped)
```

The document is a standalone `article`; it uses only `geometry`, `amsmath`,
`amssymb`, `amsthm`, `array`, `parskip`, and `xeCJK` (the latter so that the
Chinese quote renders; a CJK font such as Songti/Noto is used if present, and
the file still compiles without one).

The Lean 4 project is built with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib. The observed `#print axioms` output is `[propext]` for every theorem,
with no `sorryAx` and no `Lean.ofReduceBool`.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `xeCJK`, designed to compile with `tectonic main.tex`.
- **PDF document** — `build/main.pdf` is produced by the Tectonic build of
  `main.tex`; the source is self-contained and uses no external figures or
  non-standard packages (the only environment-dependent item is the CJK font,
  used solely to render the Chinese quotation, with a built-in fallback).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. It formalises the witness's
  support values `2` and `4`, the equality `2 + 4 = 6`, the explicit transform
  values `f_hat(xi) = 1 - omega^xi` in `Z[omega]`, and the non-membership of
  the witness among time-frequency translates of affine functions (and among
  transforms of such translates). It is written in core Lean only (no Mathlib)
  and contains no `sorry`.
- **Reproduction** — `reproduce.py` is pure standard-library Python 3 and
  verifies all numerical claims exactly, with exact `Z[omega]` arithmetic and
  no floating point.
