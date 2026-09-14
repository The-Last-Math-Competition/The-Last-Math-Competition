# Disproof of conjecture `00000008417`

**Verdict: FALSE.**

This submission disproves conjecture `00000008417` as stated. The witness is the
small Witt design `W_12 = S(5,6,12)`, a genuine `5-(12,6,1)` design with 132
blocks on 12 points. It exists **at `n = 12`**, and at `(t,k,n) = (5,6,12)` all
six classical divisibility conditions hold. Hence the existence threshold obeys
`n_0(5,6) ≤ 12`, which contradicts the filed lower bound `n_0(5,6) > 12`. In fact
there is **no divisibility obstruction at `n = 12`**. The refutation is
unconditional, elementary, and independently verified two ways, plus a
kernel-checked Lean 4 certificate.

## The conjecture, quoted verbatim

Quoted from `conjectures/00000008417.md`:

> **English.** Definition: A Steiner system S(t,k,n) is a design in which every
> t-element subset lies in exactly one block. Conjecture: S(t,k,n) exists if and
> only if the classical divisibility conditions hold and n is at least n_0(t,k);
> n_0(t,k) admits an explicit bound of type (kt)^{ct}, and the lower bound
> n_0(5,6) > 12 is given by a concrete divisibility obstruction. (explicit
> threshold for Steiner systems)
>
> **中文。** 定义：Steiner 系 S(t,k,n) 指每个 t 元子集含于恰一个区组的设计。猜想：
> S(t,k,n) 存在当且仅当经典整除条件满足且 n ≥ n₀(t,k)；n₀(t,k) ≤ (kt)^{ct} 型
> 显式界，且下界 n₀(5,6) > 12 由具体整除障碍给出。（Steiner 系显式阈值）

We read the conjecture as the conjunction of:

- **(C1)** *(existence criterion)* for all `t < k ≤ n`, `S(t,k,n)` exists iff the
  classical divisibility conditions hold and `n ≥ n_0(t,k)`;
- **(C2)** *(small-`n` lower bound)* `n_0(5,6) > 12`, and this bound is "given by
  a concrete divisibility obstruction".

## The design and its uniqueness

`W_12 = S(5,6,12)` is a `5-(12,6,1)` design: 132 six-element blocks on the 12
point set `{0,…,11}` such that every one of the `C(12,5) = 792` five-subsets is
contained in exactly one block. It is often described as
`W_12 = {0,…,10} ∪ {∞}` with the blocks being the images of a hexad under the
Mathieu group `M_12`.

The design is classically **unique up to isomorphism**, with automorphism group
`M_12` of order `95040`. `reproduce.py` confirms this symmetry computationally by
enumerating **all 95040 automorphisms** of the constructed design.

Combinatorial invariants of the constructed design (verified exhaustively):

- the `C(132,2) = 8646` block pairs intersect in `0,2,3,4` points with
  multiplicities `66, 2970, 2640, 2970` (intersections of size `1` or `5` never
  occur);
- each block meets the others in `i` points with multiplicities
  `1, 0, 45, 40, 45, 0, 1` for `i = 0,…,6` (same profile for every block);
- total incidences `132 · 6 = 792 = C(12,5)`.

## The six divisibility conditions at `(5,6,12)`

For an `S(t,k,n)` the classical conditions are
`λ_i = C(n−i, t−i) / C(k−i, t−i) ∈ ℤ` for `i = 0,…,t`. At `(5,6,12)`:

| `i` | exact identity | quotient `λ_i` |
|:---:|:---------------|:--------------:|
| 0 | `792 = 132 · 6` | `132` |
| 1 | `330 = 66 · 5`  | `66`  |
| 2 | `120 = 30 · 4`  | `30`  |
| 3 | `36 = 12 · 3`   | `12`  |
| 4 | `8 = 4 · 2`     | `4`   |
| 5 | `1 = 1 · 1`     | `1`   |

All six quotients are integers. There is **no divisibility obstruction at
`n = 12`** — directly contradicting the claim that the bound `n_0(5,6) > 12` is
supplied by one.

## The logical dichotomy

The conjecture is a conjunction, and no reading makes both clauses true.

**Theorem.** Let `n_0(5,6)` be the threshold appearing in (C1). Then
(i) if (C1) holds then `n_0(5,6) ≤ 12`, so (C2) is false; and
(ii) if (C2) holds then (C1) is false. Hence (C1) ∧ (C2) is false under every
reading.

*Proof.* An `S(5,6,12)` exists and the six divisibility conditions hold at
`n = 12`.

(i) Assume (C1). At `(t,k,n) = (5,6,12)`, (C1) says
`(S(5,6,12) exists) ⟺ (divisibility holds at (5,6,12) and 12 ≥ n_0(5,6))`.
The left side is true and the divisibility conjunct is true, so the equivalence
forces `12 ≥ n_0(5,6)`, i.e. `n_0(5,6) ≤ 12`. Thus the literal statement
`n_0(5,6) > 12` is false.

(ii) Assume (C2), i.e. `n_0(5,6) > 12`. At `(5,6,12)` divisibility holds but
`12 ≥ n_0(5,6)` fails, so the right side of (C1) is false while the left side is
true. The asserted "if and only if" is false.

Either way the conjunction fails. This holds whether `n_0(t,k)` is read as the
exact least admissible `n`, as any threshold function making (C1) true, or as the
explicit `(kt)^{ct}` bound of the conjecture: any such quantity is forced by (C1)
to satisfy `n_0(5,6) ≤ 12`. ∎

## The two independent constructions and their isomorphism

Both constructions were verified **exhaustively** over all 792 five-subsets.

1. **Exact cover / backtracking.** Columns are the 792 five-subsets, rows the
   `C(12,6) = 924` six-subsets; selecting a row covers its `C(6,5) = 6`
   five-subsets. An Algorithm X search with a minimum-remaining-values heuristic
   selects 132 rows, which the script confirms cover every five-subset exactly
   once. The resulting 132 blocks are listed as 12-bit masks in
   `lean4/Main.lean` (bit-identical to the script's output). SHA-256 of the
   canonical block list:
   `6b2ab5e73e9e8a43a8cbc13666083805c5613f5b18915dc8a20d3064cb5eb567`.
2. **Extended ternary Golay code `[12,6,6]`.** Over `𝔽_3` this code has 729
   codewords with weight distribution `A_0 = 1`, `A_6 = 264`, `A_9 = 440`,
   `A_12 = 24`. Its 264 weight-6 words split into 132 opposite pairs `{±c}`,
   giving 132 distinct supports, which also cover every five-subset exactly once.

**The two designs are isomorphic.** An explicit point permutation
`p = (0,1,2,3,4,11,7,9,8,6,5,10)` maps the exact-cover design onto the Golay
design; the script verifies the relabelled block set equals the Golay block set
exactly. Both are `W_12`.

## Threshold context

In every small case the first admissible proper value of `n` is attained, and the
extremal examples are exactly the Witt designs.

| `(t,k)` | first admissible `n` | design | name |
|:-------:|:--------------------:|:-------|:-----|
| (2,3) | 7  | `S(2,3,7) = PG(2,2)` | Fano plane |
| (3,4) | 8  | `S(3,4,8) = AG(3,2)` | affine geometry |
| (4,5) | 11 | `S(4,5,11)` | Witt design `W_11` |
| (5,6) | 12 | `S(5,6,12)` | Witt design `W_12` |
| (5,8) | 24 | `S(5,8,24)` | Witt design `W_24` |

The `(5,6)` row is decisive: divisibility holds at `n = 12` and the design
exists there, so the threshold satisfies `n_0(5,6) ≤ 12`.

## Scope note

- The general large-`n` criterion "divisibility implies existence for
  `n ≥ n_0(t,k)`" is essentially **Keevash's theorem**. That theorem is
  non-effective and there is no explicit `(kt)^{ct}` threshold in the literature.
  **This submission does not dispute the large-`n` existence direction.**
- The submission targets the definite, false conjunct `n_0(5,6) > 12` (and the
  accompanying "concrete divisibility obstruction"). At `n = 12` the divisibility
  conditions hold and the design exists, so no lower bound above 12 can be
  correct for `(5,6)`, and no divisibility obstruction at `n = 12` exists. This
  is a finite, verified, unconditional refutation.
- Uniqueness of `W_12` and `|Aut(W_12)| = 95040` are classical and are **not
  needed** for the refutation (one design suffices); they are reported for
  context and checked computationally.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, design and uniqueness, divisibility table, dichotomy, constructions, threshold table, scope note, reproduction, rule-3 status. |
| `main.tex` | LaTeX source (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (73 KiB). |
| `reproduce.py` | Python 3 standard library only: divisibility quotients, exact-cover construction, exhaustive coverage check, canonical SHA-256, independent Golay construction, isomorphism, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, `name = "tlmc8417"`, no dependencies. |
| `lean4/Main.lean` | Core Lean only (`import Std`, no Mathlib, no `sorry`): the 132 masks, the exact-cover theorem, the six divisibility identities, `exists_S5612`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, build time, axiom audit, scope note. |

## Reproducing

Python (standard library only, ~64 s; the automorphism enumeration dominates):

```sh
python3 reproduce.py
```

It prints the six divisibility quotients, the 132-block design, the canonical
SHA-256, the invariants, an explicit relabelling isomorphism, and
`|Aut| = 95040`, then `PASS` with exit `0` exactly when every check holds.

LaTeX document:

```sh
mkdir -p build && tectonic --outdir build main.tex
```

Lean 4 project (from-scratch build ≈63 s):

```sh
cd lean4
lake build                     # rc 0, ~63 s wall
lake env lean Check.lean       # axiom audit
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document, and
a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf` (non-empty, 73 KiB).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (library `Main`,
  `name = "tlmc8417"`), `Main.lean`, `Check.lean`, and `lean4/README.md`. It
  formalises that the 132 explicit 12-bit masks form a `5-(12,6,1)` design
  (`every_five_in_exactly_one_block`, `witt_is_design`, `exists_S5612`), the six
  divisibility identities, and their conjunction. It uses core Lean only (no
  Mathlib) and contains no `sorry`; the audit reports only `propext` — no
  `sorryAx`, and no `Lean.ofReduceBool` (the fully kernel-checked `decide`
  variant is used, not `native_decide`).
