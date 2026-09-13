# Disproof of conjecture `00000003837`

**Verdict: FALSE.**

This submission disproves conjecture `00000003837` as stated. The refutation is
unconditional and elementary. The conjecture's first clause ("the number of
fixed points of `*` is always odd") fails already in the smallest possible case,
type `A₁` with `λ = ω₁`: the crystal `B(ω₁)` has two elements and the star
involution has **0** fixed points, which is even. The second clause ("when
`λ = −w₀λ` the number of fixed points is at least 3") also fails there, since
`0 < 3`; moreover in type `A₁` the condition `λ = −w₀λ` holds for **every** `λ`,
and the fixed-point count over all of type `A₁` is at most `1`.

## The conjecture

Quoted verbatim from `conjectures/00000003837.md`:

> **English.** Definition: The star involution * denotes the crystal involution
> reversing all simple arrow directions, always existing in finite type.
> Conjecture: The number of fixed points of * in B(λ) is always odd, and when
> λ = −w₀λ the number of fixed points is at least 3. (star fixed point parity)
>
> **中文。** 定义：星对合 * 指同时反转所有简单箭头方向所得的晶体对合,有限型上恒存在。猜想：B(λ) 中 * 的不动点个数恒为奇数,且当 λ = −w₀λ 时不动点个数不少于 3。（星不动点奇偶）

The claim has two clauses:

1. **Parity clause.** For every dominant integral weight `λ` in finite type, the
   number of fixed points of the star involution `*` on `B(λ)` is odd.
2. **Three clause.** Whenever `λ = −w₀λ`, that number is at least `3`.

Both are false, and they fail in the same minimal example.

## The elementary parity lemma

**Lemma.** Let `σ` be an involution of a finite set `X`. Then the number of
fixed points of `σ` satisfies

```
#Fix(σ) ≡ |X|  (mod 2).
```

*Proof.* Every non-fixed point `x` lies in a 2-cycle `{x, σ(x)}` with
`σ(x) ≠ x`, and these 2-cycles partition `X ∖ Fix(σ)`. Hence
`|X| − #Fix(σ)` is even, i.e. `#Fix(σ) ≡ |X| (mod 2)`. ∎

Since `|B(λ)| = dim V(λ)`, the correct general congruence is

```
#Fix(*)  ≡  |B(λ)|  =  dim V(λ)   (mod 2).
```

So the parity clause could only ever hold for those `λ` with `dim V(λ)` odd; as
an *unconditional* assertion about all `λ` it is false. Applying the lemma to
`B(ω₁)`, which has `|B(ω₁)| = 2` elements, already forces `#Fix(*)` to be even.

## The counterexample: type `A₁`, `λ = ω₁`

In type `A₁` (i.e. `sl₂`), take `λ = ω₁`. The crystal is

```
B(ω₁) = { u₊ , u₋ },      wt(u₊) = +1,   wt(u₋) = −1,
```

with exactly one arrow `f₁ : u₊ ↦ u₋` (and `f₁ u₋ = 0`, `e₁ u₋ = u₊`,
`e₁ u₊ = 0`). The star involution reverses all arrows, so it must send the top
element to the bottom element and vice versa:

```
* (u₊) = u₋ ,      * (u₋) = u₊ .
```

This is the only arrow-reversing involution of a 2-element crystal (see the
uniqueness discussion below), so it is forced. It has **no fixed point**:

```
#Fix(*) = 0 .
```

Now:

- `0` is **even**, so the parity clause "always odd" is contradicted;
- `0 < 3`, so the three clause is contradicted;
- and `λ = −w₀λ` **does** hold for `λ = ω₁`: in type `A₁` the longest element
  `w₀ = s₁` acts on the weight lattice by `−1`, so `−w₀` acts as the identity
  and `−w₀λ = λ` for every `λ`. Hence the hypothesis of the three clause is
  satisfied and its conclusion still fails.

This is not a boundary or degeneracy artefact: the same `λ = ω₁` is the
simplest non-trivial dominant weight in the simplest finite type.

## The general family `B(kω₁)` and the table

More generally `B(kω₁)` is the `(k+1)`-element chain with weights

```
k, k−2, …, −k .
```

Its unique arrow-reversing involution is `j ↦ k − j` (positions `0,…,k` from the
top), which negates weights. Its fixed points are exactly the elements of weight
`0`; there is one such element when `k` is even and none when `k` is odd. Thus

```
#Fix(*)  =  1   if k is even,
            0   if k is odd.
```

For `k = 1, …, 5`:

| `k` | `λ` | weights of `B(kω₁)` | `|B(kω₁)|` | `#Fix(*)` | parity | `#Fix ≥ 3`? |
|----:|:----|:--------------------|:----------:|:---------:|:------:|:-----------:|
| 1 | `ω₁`  | `1, −1`                | 2 | 0 | even | no (`0 < 3`) |
| 2 | `2ω₁` | `2, 0, −2`             | 3 | 1 | odd  | no (`1 < 3`) |
| 3 | `3ω₁` | `3, 1, −1, −3`         | 4 | 0 | even | no (`0 < 3`) |
| 4 | `4ω₁` | `4, 2, 0, −2, −4`      | 5 | 1 | odd  | no (`1 < 3`) |
| 5 | `5ω₁` | `5, 3, 1, −1, −3, −5`  | 6 | 0 | even | no (`0 < 3`) |

Note that in the `k = 2` row the crystal has `3` elements (odd cardinality) and
the fixed-point count is `1`, which is odd — so the parity lemma is respected —
but `1 < 3`. That is why the three clause is not merely a parity artefact.

## `≥ 3` fails for every `λ` in type `A₁`

From the closed form above, over all `k ≥ 1` the fixed-point count of the star on
`B(kω₁)` is either `0` or `1`. Hence

```
max over all B(kω₁) of #Fix(*)  =  1  <  3.
```

So the clause "when `λ = −w₀λ` the number of fixed points is at least `3`" fails
for **every** dominant weight `λ` in type `A₁` — and since in type `A₁` one has
`−w₀ = id`, the hypothesis `λ = −w₀λ` holds for every one of them. The failure
is therefore not confined to the parity clause or to a single exceptional `λ`.
The parity clause itself holds precisely for the even `k` (where `dim V(kω₁) =
k+1` is odd), in accordance with the lemma — again only as a tautology for a
restricted set of `λ`, not as the unconditional claim.

## Convention robustness

One might try to rescue the conjecture by redefining `*` (for instance by a
different weight convention). This is impossible.

1. **Any involution of a 2-element set has 0 or 2 fixed points** — both even —
   because the identity fixes both elements and the swap fixes none. So no
   involution of `B(ω₁)` whatsoever has an odd fixed-point count. This is
   formalised as `involution_fixedCount_even` and reproduced by `reproduce.py`
   (which enumerates all involutions of `{0,1}`).
2. **The arrow-reversing involution of `B(ω₁)` is unique.** The requirement
   `f₁ ∘ σ = σ ∘ e₁` on `B(ω₁)` forces `σ(u₊) = u₋`, and then the involution law
   forces `σ(u₋) = u₊`; so `σ` must be the swap. Formalised as
   `arrow_reversing_involution_eq_star` and checked exhaustively in
   `reproduce.py`. Hence every faithful convention for `*` on `B(ω₁)` agrees
   with the one used here, and the value `#Fix(*) = 0` is convention-independent.
3. **The weight-preserving alternative does not exist.** There is no involution
   of `B(ω₁)` that both reverses the arrow and preserves weights (the swap
   negates them). Formalised as `no_weight_preserving_arrow_reversal`. So one
   cannot tweak the weight condition to manufacture a fixed point.

Together these kill the only avenues for repairing the claim in this example.

## Literature context (stated as context, not as proof)

The genuine results surrounding the star involution are **not** parity theorems.
The relevant theorem is Stembridge's / Berenstein–Kirillov's statement that the
number of **self-evacuating tableaux** of a shape equals the number of **domino
tableaux** of that shape (Stembridge, *Duke Math. J.* **82** (1996);
Berenstein–Kirillov, *Discrete Math.* **225** (2000), and the references
therein). That is a bijective/equinumerosity statement about evacuation and
domino tableaux; it says nothing of the form "#Fix(*) is odd". The correct
general congruence in this circle of ideas is the elementary one proved above,

```
#Fix(*) ≡ dim V(λ) (mod 2),
```

which follows from the 2-cycle pairing and is not the conjecture's claim.
The conjecture reads as a garbled rendering of these results: the parity clause
appears to confuse "`dim V(λ)` odd" with "always odd", and the three clause has
no counterpart in the literature.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture, parity lemma, counterexample, table, convention robustness, literature context, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic main.tex` (the artifact is placed in `build/`). |
| `reproduce.py` | Python 3 (standard library only) reproduction: models `B(kω₁)`, enumerates the arrow-reversing involution, counts fixed points for `k = 1..10`, checks the parity lemma and the convention-robustness facts; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; package `tlmc3837`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, faithfulness note, and scope of the formalisation. |

## Reproducing

Python (dependency-free, runs in under a second):

```sh
python3 reproduce.py
```

It models `B(kω₁)` for `k = 1, …, 10`, verifies that `j ↦ k − j` is an
arrow-reversing involution negating weights, counts its fixed points, asserts
that the count is even for every odd `k` (in particular `k = 1` gives `0`),
asserts `0 < 3`, checks the parity lemma `#Fix ≡ |B(kω₁)| (mod 2)`, and
exhaustively verifies the convention-robustness facts. It prints `PASS` and
exits `0` exactly when every check holds; a `FAIL` (non-zero exit status) means
a claimed fact did not verify.

LaTeX document:

```sh
tectonic --outdir build main.tex      # writes build/main.pdf directly
# equivalently: tectonic main.tex      # writes main.pdf, then place it in build/
```

The submission artifact is `build/main.pdf` (non-empty, 5 pages).

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` that uses
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `booktabs`, `parskip`, and (only
  to typeset the Chinese statement of the conjecture) `xeCJK` with the macOS
  font `PingFang SC`. It compiles with `tectonic main.tex` without errors, and
  the bilingual quotation renders correctly.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex` (the same location as the template
  submission).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (package `tlmc3837`), `Main.lean`,
  `Check.lean`, and a `README.md`. It formalises the two-element `A₁` crystal
  `B(ω₁)`, the star involution as the forced arrow-reversing swap, its involution
  and weight-negation properties, the vanishing fixed-point count, and the
  robustness lemmas (`involution_fixedCount_even`,
  `involution_fixedCount_lt_three`, `arrow_reversing_involution_eq_star`,
  `no_weight_preserving_arrow_reversal`), packaged as
  `conjecture_00000003837_false`. It uses core Lean only, contains no `sorry`,
  and `lake env lean Check.lean` reports only `propext` and `Quot.sound` for the
  theorem packages — in particular no `sorryAx` and no `Lean.ofReduceBool`.
