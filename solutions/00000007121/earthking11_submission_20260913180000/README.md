# Rule-3 disproof submission — conjecture `00000007121` (earthking11)

**Verdict: FALSE** (statement as written). Submitted 2026-09-13.

This directory contains a complete submission for conjecture
`00000007121`. It is a **disproof**: it argues the catalogue entry is false as
written, on two independent grounds, while being explicit about the character
of each ground and about a significant caveat.

## The statement, quoted exactly

From `conjectures/00000007121.md`:

> **English.** Definition: Convex polytopes as geometric bodies of finite
> halfspace intersections. Conjecture: The Hirsch conjecture's diameter upper
> bound of face count minus dimension holds, and the counterexample to the
> bound is the high-dimensional double configuration. (high-dimensional
> counterexample to the Hirsch bound)
>
> **中文。** 定义：凸多面体：有限半空间交的几何体。猜想：Hirsch 猜想：图直径的上界为面数减维数且界的反例为高维双重构型。（Hirsch 反例高维双构型直径上界）

## Ground 1 — as written, the conjunction is self-contradictory

The entry asserts that the Hirsch bound **holds** *and* that a
**counterexample** to it exists. Let

* `A` = "for every triple (dimension `d`, facets `f`, diameter `diam`),
  `diam ≤ f − d`" (the bound holds), and
* `B` = "there exist `d, f, diam` with `f − d < diam`" (a counterexample).

Over `Nat`, `f − d < diam` is the negation of `diam ≤ f − d`, so `B` is
exactly `¬A`. The statement is `A ∧ ¬A`, which is unsatisfiable. This is a
statement-level (logical) refutation and is **fully formalisable**; it is
formalised in core Lean 4 under `lean4/` (no Mathlib, no `sorry`, no axiom).

## Ground 2 — independently, the Hirsch bound is genuinely false

Santos (Annals of Mathematics **176** (2012), 383–412) constructed a convex
polytope of dimension 43 with 86 facets and graph diameter 44. Since
86 − 43 = 43 < 44, the Hirsch bound fails. The polynomial Hirsch conjecture
remains open.

**This is a literature result and cannot be reproduced locally.** Neither the
Lean development nor `reproduce.py` reproduces Santos's construction; the
Python script checks only the arithmetic 86 − 43 = 43 < 44 and says so
explicitly.

## Caveat (stated prominently, not swept aside)

The entry appears to be a **catalogue-style garbling** that names both a
conjecture and its disproof in a single sentence. Furthermore,
"high-dimensional double configuration" is **not** the standard name for
Santos's object — the standard notions are *Hirsch polytopes* / *spindles* and
the *Klee–Walkup* and *Santos* constructions. The "self-contradiction" of
Ground 1 is therefore arguably a **phrasing artefact** rather than a
substantive mathematical falsehood, even though it is a real consequence of
the text as written. This submission presents both grounds and lets the
maintainer judge; the logical reading is not overstated.

## Files

| Path | Role |
|---|---|
| `README.md` | This file. |
| `main.tex` | Standalone article (amsmath/amssymb/amsthm): quotes the statement, gives the logical contradiction, quotes Santos's counterexample with its numbers, states the caveat. |
| `main.pdf` | Build output: `tectonic --outdir build main.tex` → `build/main.pdf`. |
| `reproduce.py` | Stdlib-only checker: Santos arithmetic + logical analysis; PASS/FAIL; exit 0. Santos's construction is not reproduced. |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1` (exact). |
| `lean4/lakefile.toml` | Lake project `tlmc7121`, library `Main`. |
| `lean4/Main.lean` | Core Lean formalisation of the logical inconsistency only. |
| `lean4/Check.lean` | Statement + `#print axioms` audit. |
| `lean4/README.md` | Documents exactly what is and is not formalised. |

## How to verify

```sh
export PATH="/opt/homebrew/bin:$PATH"

# Python checker (stdlib only)
python3 reproduce.py

# Lean: build library, then audit axioms
cd lean4
lake build
lake env lean Check.lean

# LaTeX
cd ..
mkdir -p build
tectonic --outdir build main.tex   # -> build/main.pdf
```

`main.tex` loads `xeCJK` only to typeset the Chinese half of the verbatim
bilingual quote; it uses the macOS font `PingFang SC`. If that font is absent,
substitute any CJK-capable font in the `\setCJKmainfont{...}` line.

The Lean headline theorem is
`Hirsch7121.conjecture_00000007121_false`; `Check.lean` confirms it depends on
no axioms (in particular, no `sorryAx`).
