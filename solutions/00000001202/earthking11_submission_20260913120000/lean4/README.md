# Lean 4 formalisation (conjecture 00000001202)

Core Lean 4 only: `import Std`, no Mathlib, no `sorry`, no `axiom`,
no `native_decide`. Toolchain: `leanprover/lean4:v4.33.1` (pinned in
`lean-toolchain`).

## What is formalised

The file `Main.lean` formalises the **computable Sprague–Grundy
recurrence of the octal game `0.07`** and the **single refuting
instance `n = 4`**:

* `mex s` — smallest natural number not in the list `s` (fueled, so it is
  structurally recursive and reduces in the kernel).
* `look l i` — propext-free list indexing.
* `sgOf prev n` — one recurrence step
  `g(n) = mex{ g(a) XOR g(b) : a + b = n - 2 }`.
* `gList n` — the list `[g 0, …, g (n-1)]`, by structural recursion on `n`.
* `g n` — the SG value of a heap of `n` tokens, `look (gList (n+1)) n`.

The kernel reduces concrete instances, giving the counterexample:

| theorem | statement |
|---|---|
| `g4` | `g 4 = 2` |
| `g16` | `g 16 = 5` |
| `period12_fails_at_4` | `g 4 ≠ g 16` |
| `conjecture_00000001202_false` | `g 4 ≠ g 16 ∧ g 4 = 2 ∧ g 16 = 5` |

The last theorem is exactly the failure of the conjectured identity
`g(n+12) = g(n) for all n ≥ 4` at `n = 4`: since `g 16 = g (4+12) = 5`
and `g 4 = 2`, the identity is false.

## What is *not* formalised here

The Lean file deliberately proves only the **specific refuting instance
`n = 4`** and the computation of `g` at the two points needed. It does
**not** prove any statement about the eventual behaviour of the whole
sequence. In particular, the true eventual period and pre-period are
established by exhaustive computation in `../reproduce.py`:

* standard reading `0.07` (Dawson's Kayles): eventual **period 34** with
  **pre-period 53** (not period 12 / pre-period 4);
* prose reading “removes 1 or 2 tokens” = `0.77` (Kayles): eventual
  **period 12** — as claimed — but **pre-period 71**, so the asserted
  identity `g(n+12) = g(n) for all n ≥ 4` still fails (first at `n = 10`).

Formally proving those eventual-period statements would require a
different (non-computational) argument and is outside the scope of this
formalisation.

## Build and audit

```sh
cd lean4
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for each theorem. The output contains
**no `sorryAx` and no `ofReduceBool`**. Each theorem depends only on
`propext`, which is a standard Lean core axiom (it enters through
`Nat.xor`, the nim-sum used in the recurrence) and is not among the
prohibited constructs.
