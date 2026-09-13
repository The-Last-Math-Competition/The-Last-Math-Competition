# Disproof of conjecture `00000001192`

**Verdict: FALSE.**

The conjecture, as filed in `conjectures/00000001192.md`, claims that
`c(n, q)` — the number of subgroups of `GL_n(F_q)` whose order equals that of
the commutator (derived) subgroup — is an **integer-coefficient** polynomial in
`q` of degree `n² − n` with leading coefficient

```
LC(n) = ( ∏_{p | n} p ) / ( n! · n^n ).
```

This submission refutes the conjecture by showing that the two structural
assertions in it — the *kind of polynomial* and the *stated leading
coefficient* — are arithmetically incompatible. The argument is elementary and
unconditional, and is formalised in Lean 4 (core only). No claim is made here
about the actual value of `c(n, q)`; see the scope note below.

## The claim, quoted

> **Definition:** Let `c(n,q)` denote the number of subgroups of `GL_n(F_q)`
> whose order equals that of the commutator (derived) subgroup.
> **Conjecture (Higman PORC, commutator version):** `c(n,q)` is an
> integer-coefficient polynomial in `q` of degree `n²−n` with leading
> coefficient `(n!·n^{n})^{-1}·∏_{p|n} p`.

## The refutation

Write, in lowest terms,

```
LC(n) = a_n / b_n,    LC(n) = ( ∏_{p | n} p ) / ( n! · n^n ).
```

Because `rad(n) := ∏_{p|n} p` divides `n`, and `n | n^n | n! · n^n`, the
radical always divides the denominator. Hence `a_n = 1` and
`b_n = n! · n^n / rad(n)` for every `n ≥ 1`. The leading coefficient is
therefore a non-integer rational as soon as `b_n > 1`, which happens for every
`n ≥ 2`:

| `n` | degree `d = n²−n` | `LC(n)` | integer? |
|----:|------------------:|--------:|:--------:|
| 1 | 0  | `1`         | yes |
| 2 | 2  | `1/4`       | no  |
| 3 | 6  | `1/54`      | no  |
| 4 | 12 | `1/3072`    | no  |
| 5 | 20 | `1/75000`   | no  |
| 6 | 30 | `1/5598720` | no  |

For instance

```
LC(2) = 2 / (2! · 2²)   = 2/8       = 1/4,
LC(3) = 3 / (3! · 3³)   = 3/162     = 1/54,
LC(4) = 2 / (4! · 4⁴)   = 2/6144    = 1/3072,
LC(6) = 6 / (6! · 6⁶)   = 6/33592320 = 1/5598720.
```

### The integer-coefficient reading

Suppose `c(n,q) = a_d q^d + … + a_0` with all `a_j ∈ ℤ` and `d = n² − n`. The
leading coefficient `a_d` is then an integer, since it is one of the integer
coefficients. The conjecture also says `a_d = LC(n)`. Taking `n = 2` (so
`d = 2`, `LC(2) = 1/4`) would force the integer `a_2` to satisfy `4 · a_2 = 1`.
No integer does:

```
¬ ∃ a : ℤ,  4 · a = 1.
```

The same contradiction occurs at `n = 3` (`a_6 = 1/54`), `n = 4`
(`a_12 = 1/3072`), and at every `n ≥ 2`. Hence no integer-coefficient polynomial
of degree `n² − n` has the stated leading coefficient. **Contradiction.**

### The charitable “integer-valued” reading

Even if one weakens “integer-coefficient” to “integer-valued” (a common reading
for PORC formulas), the conjecture still fails. An integer-valued polynomial of
degree `d` written in the binomial basis
`P = Σ_k b_k · C(x,k)` with `b_k ∈ ℤ` has leading coefficient `b_d / d!`, so
necessarily

```
d! · (leading coefficient) ∈ ℤ.
```

For the stated degree `d = n² − n`:

* `n = 2`, `d = 2`:  `2! · LC(2) = 2 · 1/4 = 1/2 ∉ ℤ`;
* `n = 3`, `d = 6`:  `6! · LC(3) = 720 · 1/54 = 720/54 = 40/3 ∉ ℤ`.

So the integer-valued reading is impossible already at `n = 2` and `n = 3`.
The ambiguity between the two readings does not rescue the conjecture.

### Divisibility form (what Lean proves)

The arithmetic content used above is exactly:

```
¬ ∃ m : ℕ,  m · 4  = 1        -- LC(2) = 1/4 is not an integer
¬ ∃ m : ℕ,  m · 54 = 1        -- LC(3) = 1/54 is not an integer
¬ ∃ m : ℕ,  m · 2  = 1        -- 2! · LC(2) = 1/2 is not an integer
¬ ∃ m : ℕ,  m · 54 = 720      -- 6! · LC(3) = 40/3 is not an integer
¬ ∃ a : ℤ,  4 · a  = 1        -- ℤ-form of “1/4 is not an integer”
```

## Scope note (stated honestly)

The conjecture concerns a quantity `c(n,q)` — a count of certain subgroups of a
finite group — that **this submission does not otherwise analyse**. The
refutation is purely about the *stated leading coefficient* being arithmetically
impossible for the *stated kind of polynomial* (integer-coefficient, degree
`n² − n`). It is a self-contained inconsistency in the text of the conjecture,
independent of any group theory, and already visible at `n = 2`.

If the author intended a PORC constituent indexed by `q = p^f` (or by a residue
class of `q`), or a different normalisation of the leading coefficient, then the
text **as written** is still self-inconsistent: it demands an
integer-coefficient polynomial whose leading coefficient is the non-integer
rational `LC(n)`. Making the statement consistent requires changing at least one
of (i) the class of polynomials, (ii) the degree, or (iii) the normalisation.
None of these qualifications appears in the conjecture as filed.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document. |
| `main.tex` | LaTeX source of the disproof (standalone `article`; `amsmath`, `amssymb`, `amsthm`). |
| `build/main.pdf` | Compiled PDF (`tectonic --outdir build main.tex`). |
| `reproduce.py` | Python 3, standard library only: exact `Fraction` computation of `LC(n)` for `n = 1..12`, the integer and integer-valued tests, `PASS`/`FAIL`, exit 0 on pass. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake config; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`, no `axiom`, no `native_decide`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table and proof strategy for the formalisation. |

## Reproducing

Numerical check (dependency-free, runs in milliseconds):

```sh
python3 reproduce.py
```

It prints the table of `LC(n)` for `n = 1..12` with reduced numerator and
denominator, marks whether `LC(n)` is an integer, computes `d! · LC(n)` for
`d = n² − n`, asserts `LC(2) = 1/4`, `LC(3) = 1/54`, `LC(4) = 1/3072`,
`LC(6) = 1/5598720`, that `LC(n)` is a non-integer for all `2 ≤ n ≤ 12`, and
that `d! · LC(n) ∉ ℤ` at `n = 2, 3`. It ends with `PASS` (exit 0) or `FAIL`
(exit 1).

PDF:

```sh
mkdir -p build && tectonic --outdir build main.tex
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`Check.lean` prints the axioms of every theorem. All of them report only
`propext`; none reports `sorryAx` or `ofReduceBool`, and Mathlib is not imported.
The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`).

## Status against the submission rules

- **LaTeX source** — `main.tex`, standalone `article` using only `amsmath`,
  `amssymb`, `amsthm`, `geometry`, `booktabs`, `parskip`.
- **PDF document** — `build/main.pdf`, produced by
  `tectonic --outdir build main.tex` (tectonic 0.17.0).
- **Lean 4 project** — `lean4/`, with `lean-toolchain`, `lakefile.toml`,
  `Main.lean`, `Check.lean`, `README.md`. It builds with `lake build` and
  formalises the non-integrality of `LC(2)`, `LC(3)`, `LC(4)` and of
  `2! · LC(2)`, `6! · LC(3)`, collecting them in
  `conjecture_00000001192_false`.
