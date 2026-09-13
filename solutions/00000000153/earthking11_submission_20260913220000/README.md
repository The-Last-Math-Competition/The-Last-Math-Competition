# Disproof of conjecture `00000000153`

**Verdict: FALSE.**

This submission disproves conjecture `00000000153` as stated. The refutation is
unconditional and elementary. The witness is the finite discrete system
`X = Z/4 = {0,1,2,3}` with the shift `T(x) = x + 1`:

* `(X, T)` is **minimal** — `T` is a single 4-cycle, so the full orbit of every
  point is all of `X`;
* but the **prime-index orbit** of `x` is `{T^p x : p prime} = X \ {x}`: it
  omits exactly one residue, namely `x` itself. Indeed no prime is divisible
  by `4`, so `p mod 4 ∈ {1,2,3}` and `T^p x ≠ x` for every prime `p`;
* in the **discrete topology** the closure of a set is the set itself, so the
  prime-index orbit closure omits `x` and is **not** all of `X`.

At the conjecture's own witness point `x = 0` the prime-index orbit is
`{p mod 4 : p prime} = {1, 2, 3}`, whose closure in the discrete topology is
`{1,2,3} ≠ X = {0,1,2,3}`. The conclusion fails in a minimal system, so the
conjecture is false. In fact the conclusion fails at **every** `x ∈ X`, not
just at `x = 0`.

## The conjecture

Quoted verbatim from `conjectures/00000000153.md`:

> **English.** Conjecture: Minimal transitivity of prime orbits: in any minimal
> topological dynamical system (X, T), for every x ∈ X the orbit closure
> {T^{p_n}x : n ≥ 1} equals X.
>
> **中文。** 猜想：素数轨道的极小传递性:在任何极小拓扑动力系统 (X, T) 中,对每个
> x ∈ X,轨道闭包 {T^{p_n}x : n ≥ 1} = X。

### Definitions the statement leaves implicit

The file assumes the following standard notions without stating them. We fix
them explicitly, so that the refutation cannot be dismissed as a misreading.

* **Topological dynamical system.** A topological space `X` together with a
  continuous map `T : X → X`. In the usual setting of topological dynamics `X`
  is also assumed compact Hausdorff. Our witness is compact, Hausdorff, and
  metric, so it satisfies that convention.
* **Minimal system.** `(X, T)` is minimal if every orbit is dense in `X`,
  equivalently if the only closed `T`-invariant subset of `X` is `X` itself.
  In a minimal system the *full* orbit `{T^n x : n ≥ 0}` is dense for every
  `x ∈ X`.
* **The prime sequence.** `(p_n)_{n≥1} = (2, 3, 5, 7, 11, …)` is the sequence
  of primes in increasing order; `p_1 = 2` and `p_n` is the n-th prime. The
  prime-index orbit of `x` is
  `P(x) = {T^{p_n} x : n ≥ 1} = {T^p x : p prime}`, the two descriptions
  agreeing because `n ↦ p_n` is a bijection onto the primes.
* **Orbit closure.** `A‾` is the closure of `A ⊆ X`. The conjecture asserts
  `P(x)‾ = X` for every `x ∈ X`, i.e. `{T^{p_n} x : n ≥ 1}‾ = X`.

The file imposes **no** restriction that `X` be infinite, perfect, or free of
isolated points, and the quantification "for every `x ∈ X`" is unrestricted.
See the caveat below.

## The witness: `X = Z/4` with the shift

Take `X = Z/4 = {0,1,2,3}` with the discrete topology and `T(x) = x + 1 mod 4`.
Then `X` is finite, hence compact; discrete, hence Hausdorff and metric; and
`T` is continuous (every map on a discrete space is), so `(X, T)` is a compact
metric topological dynamical system in the strictest sense. The dynamics is one
cycle:

```
0 --T--> 1 --T--> 2 --T--> 3 --T--> 0
```

### `(X, T)` is minimal

Iterating, `T^n x = x + n mod 4` for all `n ≥ 0`. For fixed `x`, as `n` runs
over `{0,1,2,3}` the values `x, x+1, x+2, x+3` run over all four residues, and
`T^4 x = x`. Hence the full orbit `{T^n x : n ≥ 0}` equals `X` for every `x`:
every orbit is dense (indeed equal to `X`), so `(X, T)` is minimal.

### No prime is divisible by `4`

**Lemma.** If `p` is prime then `4 ∤ p`.

**Proof.** Suppose `4 | p`. Then `p = 4k`, so `p` is even, i.e. `2 | p`. Since
`p` is prime and `2 | p`, the divisor `2` of `p` is either `1` or `p`; `2 = 1`
is false, so `p = 2`. But `4 | 2` is false. Contradiction. ∎

Equivalently: the only even prime is `2`, and `4 ∤ 2`. Therefore
`p mod 4 ∈ {1,2,3}` for every prime, and `0` is never attained. The value set
is exactly `{1,2,3}`, witnessed by `2 mod 4 = 2`, `3 mod 4 = 3`,
`5 mod 4 = 1`.

### The prime-index orbit is `X \ {x}`

Since `T^n x = x + n mod 4`, for a prime `p` we have
`T^p x = x + (p mod 4) mod 4`. By the lemma `p mod 4 ∈ {1,2,3}`, so
`T^p x ≠ x`: the base point is never in `P(x)`. Conversely, for any `y ≠ x` put
`d = y − x mod 4 ∈ {1,2,3}` and choose a prime `p ≡ d (mod 4)`:
`d = 1 → p = 5`, `d = 2 → p = 2`, `d = 3 → p = 3`. Then `T^p x = x + d = y`, so
`y ∈ P(x)`. Hence

```
P(x) = {T^p x : p prime} = X \ {x}      for every x ∈ X.
```

For `x = 0` this is `P(0) = {1,2,3}`. Because `X` is discrete, every subset is
closed, so the closure is the set itself:

```
closure(P(0)) = {1,2,3} ≠ {0,1,2,3} = X.
```

**Corollary.** `(X, T)` is a minimal topological dynamical system, but
`P(x)‾ = X \ {x} ⊊ X` for every `x`. The conjecture's conclusion fails at every
point; a fortiori it fails at `x = 0`.

## Caveat: the sharpness note

**This caveat is part of the result and must be read together with it.**

1. **The witness has isolated points and is finite.** `X = Z/4` is a finite
   discrete space, so every point is isolated. Some authors in topological
   dynamics restrict attention to minimal systems on compact metric spaces
   **without isolated points** (or simply **infinite** spaces). `X = Z/4` lies
   outside that additional, **unstated** hypothesis. If one *adds* the
   hypothesis "`X` is a compact metric space with no isolated points" (or just
   "`X` is infinite"), then `Fin 4` is excluded and the conjecture so modified
   is **not touched** by this counterexample; its status remains open here.

2. **But the file states no such hypothesis.** The filed statement is "in any
   minimal topological dynamical system `(X, T)`", with no cardinality,
   perfectness, or no-isolated-points restriction, and it quantifies
   "for every `x ∈ X`". Under the literal statement `(Z/4, +1)` is an
   admissible minimal system and `x = 0` an admissible point, so the literal
   statement is refuted. The finite case is not a technicality outside an
   intended domain unless that domain is restricted **in writing**.

3. **The alternative "closure of the full orbit" reading is a collapse, not a
   rescue.** If one reads the ambiguous `{T^{p_n}x : n ≥ 1}` as the *full*
   orbit `{T^n x : n ≥ 0}` (i.e. `p_n = n`), then in a minimal system the full
   orbit is dense **by definition**, so the claim becomes trivially true for
   every `x` in every minimal system. That is a collapse of the conjecture to
   the definition of minimality, not a substantive theorem and not a repair of
   the prime-index claim. The file's notation `p_n` is the standard one for the
   n-th prime and the conjecture is titled "prime orbits".

**Summary.** The literal conjecture is false and the refutation is elementary
and rigorous. The only way to avoid it is to add a hypothesis (infiniteness /
no isolated points) that the filed statement does not contain. Under that added
hypothesis the witness is excluded and the conjecture is untouched — which is
exactly what makes the statement as filed defective. The prime sequence starts
at `p_1 = 2`; including `p = 2` does not help, since `2 mod 4 = 2 ≠ 0`.

## Numerical table

| `x` | full orbit `{T^n x}` | prime orbit `P(x)` | omitted | `P(x)‾ = X`? |
|----:|:---------------------|:-------------------|:-------:|:------------:|
| 0 | `{0,1,2,3}` | `{1,2,3}` | 0 | no |
| 1 | `{0,1,2,3}` | `{0,2,3}` | 1 | no |
| 2 | `{0,1,2,3}` | `{0,1,3}` | 2 | no |
| 3 | `{0,1,2,3}` | `{0,1,2}` | 3 | no |

Every full orbit is `X` (minimal), yet every prime-index orbit omits exactly one
point, so no prime-index orbit closure equals `X`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture, definitions, witness, `4 ∤ p` proof, caveat, table, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic main.tex` and placed in `build/`. |
| `reproduce.py` | Python 3 (standard library only): sieves all primes `< 10^6`, checks the residue set `{1,2,3}`, the 4-cycle, minimality, and each prime orbit; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc153`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, about half a second):

```sh
python3 reproduce.py
```

It sieves all `78498` primes `p < 10^6`, verifies that none is divisible by `4`
and that `{p mod 4} = {1,2,3}`; verifies that `T` is a 4-cycle and that the full
orbit of every `x` is `X` (minimality); and verifies that for each
`x ∈ {0,1,2,3}` the prime-index orbit is exactly `X \ {x}`, so its closure is a
proper subset of `X`. It prints `PASS` and exits `0` exactly when every check
holds, and exits non-zero otherwise.

LaTeX document:

```sh
tectonic main.tex          # or: tectonic --outdir build main.tex
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

* **LaTeX source** — present (`main.tex`), a standalone `article` that uses only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `parskip`, and `booktabs`, and
  compiles with `tectonic main.tex`.
* **PDF document** — present at `build/main.pdf`, produced by `tectonic main.tex`
  and placed in `build/` (the same location as the template submission).
* **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  the system (`Fin 4`, `T x = x+1`), minimality (`minimal`, `isMinimal`),
  primality and the key arithmetic fact (`four_not_dvd_of_isPrime`), the
  prime-index orbit (`primeOrbitAt_not_self`, `primeOrbitAt_not_univ`,
  `prime_iter_zero_val_ne_zero`), the closure model
  (`primeOrbitClosure_not_univ`), and the packaged refutation
  (`conjecture_00000000153_false`,
  `conjecture_00000000153_false_at_zero`). It uses core Lean only (no Mathlib)
  and contains no `sorry`; `lake env lean Check.lean` reports no `sorryAx` for
  any theorem, only `propext` and `Quot.sound`.
