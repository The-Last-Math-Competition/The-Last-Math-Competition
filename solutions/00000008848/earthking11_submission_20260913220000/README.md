# Disproof of conjecture `00000008848`

**Verdict: FALSE.**

This submission disproves conjecture `00000008848` as stated. The conjecture
has two clauses, and each fails independently:

- **Clause (a)** ("minimal and maximal fixed points of order-preserving maps
  always exist") fails on the totally ordered set `ℤ`: the shift `f(x) = x + 1`
  is order-preserving and has no fixed point at all; and the identity map is
  order-preserving with fixed-point set `ℤ`, which has neither a least nor a
  greatest element.
- **Clause (b)** ("monotone iterations of the sub/supersolution method
  approximate them in countably many steps") fails **even on a complete
  lattice**: on `ω₁ + 1` the map `f(α) = α + 1` for `α < ω₁`,
  `f(ω₁) = ω₁`, is order-preserving with unique fixed point `ω₁`, and the
  monotone iteration from the subsolution `0` reaches it only at stage `ω₁`,
  i.e. in **uncountably** many steps.

The conjunction is false under every reading. An honest caveat, stated
prominently below: the file specifies **no poset**, so a charitable reading
that adds "complete lattice" makes clause (a) the Knaster–Tarski theorem and
puts the `ℤ` witnesses out of scope; under that reading the disproof of the
conjunction rests on clause (b).

## The conjecture

Quoted verbatim from `conjectures/00000008848.md` (both languages, as filed):

> **English.** Definition: Fixed points of order-preserving maps. Conjecture:
> Minimal and maximal fixed points of order-preserving maps always exist; and
> monotone iterations of the sub/supersolution method approximate them in
> countably many steps. (order-preserving sub/supersolution iteration)
>
> **中文。** 定义：保序映射的不动点。猜想：保序映射的最小与最大不动点恒存在；
> 由上下解方法的单调迭代在可数步内逼近。（保序上下解迭代）

**The central observation: no poset is specified, and no sub/supersolution
hypothesis is stated for the first clause.** The file says only
"order-preserving maps", with no requirement that the underlying ordered set be
a complete lattice, a complete partial order, a lattice with a bottom, or even
bounded; and it attaches no existence-of-a-fixed-point or subsolution/
supersolution hypothesis to clause (a). Read literally, clause (a) therefore
quantifies over **all** order-preserving self-maps of **all** ordered sets. In
particular `ℤ` with its usual order is an admissible domain. This is what makes
the elementary `ℤ` counterexamples decisive.

Two further hypotheses are silently absent:

1. **No continuity hypothesis** (no sup-continuity, no Scott continuity, no
   preservation of directed suprema, no compactness) is stated, which is what
   clause (b)'s "countably many steps" would require.
2. **No fixed-point-existence hypothesis** for clause (a), so the shift-map
   witness is legitimate; and even if one grants that a fixed point exists, the
   identity-map witness still refutes the claim.

## The counterexamples

### Clause (a): the shift map on `ℤ`

Let `f : ℤ → ℤ`, `f(x) = x + 1`.

- **Order-preserving:** if `a ≤ b` then `f(a) = a + 1 ≤ b + 1 = f(b)`.
- **No fixed point:** `f(x) = x` would say `x + 1 = x`, i.e. `1 = 0`, a
  contradiction.

So `f` is an order-preserving self-map of the ordered set `ℤ` with **no fixed
point whatsoever**; hence no minimal and no maximal fixed point exists. Clause
(a) fails.

### Clause (a), non-vacuous version: the identity map on `ℤ`

Let `id : ℤ → ℤ`.

- **Order-preserving:** if `a ≤ b` then `id(a) = a ≤ b = id(b)`.
- **Every point is fixed:** `id(y) = y` for all `y ∈ ℤ`.
- **No least fixed point:** if `m` were least, then `m − 1` is also fixed, so
  minimality gives `m ≤ m − 1`, i.e. after adding `1` and subtracting `m`,
  `1 ≤ 0`, false.
- **No greatest fixed point:** if `M` were greatest, then `M + 1` is also
  fixed, so maximality gives `M + 1 ≤ M`, i.e. `1 ≤ 0`, false.

This is the **primary witness** for clause (a), because it is non-vacuous: the
map genuinely has fixed points (all of them). It shows that even the repaired
statement "an order-preserving map that has at least one fixed point has a least
fixed point" is false.

### Clause (b): `ω₁ + 1` on a complete lattice

Let `ω₁` be the first uncountable ordinal and `L = ω₁ + 1 = {α : α ≤ ω₁}` with
the ordinal order; `L` is a **complete lattice** (least element `0`, greatest
element `ω₁`). Define

```
f(α) = α + 1   for α < ω₁,        f(ω₁) = ω₁.
```

- **Order-preserving:** if `α ≤ β < ω₁` then `α + 1 ≤ β + 1`; if `β = ω₁` then
  `f(β) = ω₁` is the top, so `f(α) ≤ f(β)`.
- **Unique fixed point:** for `α < ω₁`, `f(α) = α + 1 > α`; and
  `f(ω₁) = ω₁`. So the fixed-point set is the singleton `{ω₁}`, which is thus
  both the least and the greatest fixed point. The example is as non-degenerate
  as possible: the extremal fixed points coincide.
- **The iteration needs uncountably many steps.** Starting from the
  subsolution `u₀ = 0` (indeed `f(0) = 1 ≥ 0`) and iterating with suprema at
  limits, one proves by transfinite induction that `u_α = α` for every ordinal
  `α ≤ ω₁`. Hence `u_α = α < ω₁` for every **countable** ordinal `α`, so the
  iteration has not reached `ω₁` at any countable stage; the first stage at
  which it reaches the fixed point is `α = ω₁`, the first **uncountable**
  ordinal. Therefore the sub/supersolution iteration cannot reach the extremal
  fixed point in countably many steps.

The missing hypothesis is exposed by `f(ω) = ω + 1 ≠ ω = sup_{n<ω}(n + 1)`:
`f` is **not** sup-continuous. Had the file assumed that `f` preserves directed
suprema (Scott continuity), the iteration would converge at stage `ω`, i.e. in
countably many steps. The file states no such hypothesis, so clause (b) is
false even on a complete lattice.

### Why the conjunction is false under every reading

| Reading | Clause (a) | Clause (b) |
|:--------|:-----------|:-----------|
| Literal (no completeness; exactly as filed) | false, by the `ℤ` witnesses | false, by `ω₁ + 1` |
| Charitable (add "complete lattice") | **true** (Knaster–Tarski) | false, by `ω₁ + 1` |

In both rows the conjunction is false. Under the charitable reading the
disproof rests on clause (b).

## Honesty caveat (required disclosure)

**Because the file specifies no poset, a charitable complete-lattice reading
makes clause (a) a theorem and puts the `ℤ` witnesses out of scope.** Under that
reading:

- Clause (a) is true: Knaster–Tarski gives a least fixed point
  `inf{x : f(x) ≤ x}` and a greatest fixed point `sup{x : f(x) ≥ x}` for every
  order-preserving map of a complete lattice. The witnesses `f(x) = x + 1` and
  `id` on `ℤ` are **out of scope**, since `ℤ` is not a complete lattice
  (the subset `ℤ ⊆ ℤ` has no supremum). We do **not** claim clause (a) is false
  on complete lattices.
- Under that reading the disproof of the **conjunction** rests entirely on
  **clause (b)**, the `ω₁ + 1` counterexample.

We also state a second limitation honestly:

- **Core Lean has no ordinals or cardinals.** Clause (a) is fully formalised in
  `lean4/` (both witnesses, and the non-vacuous version), but clause (b) —
  which needs `ω₁` and transfinite recursion — **cannot** be stated in core
  Lean and is therefore argued in the LaTeX prose (`main.tex`) and in
  `reproduce.py`, not formalised. Mathlib, which does have ordinals, is not
  used (the project is core Lean only).

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, the no-poset observation, both `ℤ` witnesses, the `ω₁ + 1` argument, the reading caveat, file list, reproduction, and status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`; includes the clause-(b) `ω₁ + 1` argument in full. Compiles with `tectonic`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): verifies the shift map is fixed-point-free, that `id` on `ℤ` has no least/greatest fixed point (reporting the contradiction for any claimed `m`), and simulates the first finitely many stages of the `ω₁ + 1` iteration followed by the labelled transfinite argument. Prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc8848`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Clause-(a) formalisation in core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, and scope/reading caveat for the formalisation. |

## Reproducing

Python (dependency-free; a few seconds):

```sh
python3 reproduce.py
```

It prints `PASS` and exits `0` exactly when every check holds. A `FAIL`
(non-zero exit) means a claimed fact did not verify.

LaTeX document:

```sh
tectonic --outdir build main.tex     # writes build/main.pdf
# or, equivalently, plain
tectonic main.tex                    # writes ./main.pdf
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Formalisation summary

`lean4/Main.lean` (core Lean only) formalises clause (a) completely:

- `f : Int → Int := fun x => x + 1`, `f_mono`, `f_fixfree`
  (`∀ x, f x ≠ x`), `no_fixed_at_all`;
- `refutes_least_fixed_point` and `refutes_greatest_fixed_point`: the negated
  universals `¬ (∀ (α : Type) [LE α] (g : α → α), (∀ a b, a ≤ b → g a ≤ g b) →
  ∃ m, g m = m ∧ ∀ y, g y = y → m ≤ y)` (and the dual);
- `IsFixed`, `id_no_least_fixed`, `id_no_greatest_fixed`, and
  `refutes_least_fixed_point_with_fixpoint` /
  `refutes_greatest_fixed_point_with_fixpoint`: the **non-vacuous** version that
  assumes a fixed point exists, with `id` on `ℤ` as witness;
- `clause_a_false` and `clause_a_false_with_fixpoint`, packaging both halves.

`lake build` succeeds and `lake env lean Check.lean` reports the axioms of every
theorem with **no `sorryAx`**; the only axioms used are `propext` and
`Quot.sound`. Clause (b) is not formalised (no ordinals/cardinals in core Lean)
and is carried by `main.tex` and `reproduce.py`.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `booktabs`; it compiles with `tectonic`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex` (a non-empty PDF).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (project `tlmc8848`),
  `Main.lean`, `Check.lean`, and a `README.md`. It formalises clause (a) — both
  the literal and the non-vacuous witnesses — in core Lean only (no Mathlib,
  no `sorry`), and `lake env lean Check.lean` reports no `sorryAx` for any
  theorem. Clause (b) is argued in the LaTeX prose because core Lean has no
  ordinals; this limitation is disclosed in `lean4/README.md` and in
  `main.tex`.

**Verdict: the conjecture is FALSE.** Under the literal reading both clauses
fail; under the charitable complete-lattice reading clause (b) fails. The
conjunction is false under every reading.
