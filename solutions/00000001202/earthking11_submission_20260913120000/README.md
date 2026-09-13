# Submission for conjecture 00000001202 — REFUTED (verdict: FALSE)

**Conjecture (conjectures/00000001202.md).** The Sprague–Grundy sequence
of the octal game `0.07` is eventually periodic with period 12 and
pre-period length 4; i.e. `g(n+12) = g(n)` for all `n ≥ 4`.

**Verdict: FALSE.** The asserted identity fails under *both* natural
readings of the ambiguous definition.

## Readings and counterexamples

The conjecture's own prose ("each move removes 1 or 2 tokens") does not
match the standard octal code `0.07` (digits `d₁ = 0`, `d₂ = 7`, i.e. a
move removes *exactly two* tokens). Both must be checked.

| reading | recurrence | first failure of `g(n+12)=g(n)`, `n≥4` | true period / pre-period |
|---|---|---|---|
| **A. standard `0.07`** (Dawson's Kayles) | `g(n) = mex{ g(a) XOR g(b) : a+b = n−2 }` | `n = 4`: `g(4)=2`, `g(16)=5` | **34 / 53** |
| **B. prose "1 or 2" = `0.77`** (Kayles) | `g(n) = mex( {g(a)XOR g(b): a+b=n−1} ∪ {a+b=n−2} )` | `n = 10`: `g(10)=2`, `g(22)=6` | 12 / **71** |

*Reading A.* `g` begins `0, 0, 1, 1, 2, 0, 3, 1, 1, 0, 3, 3, 2, 2, 4, 0, 5, 2, …`.
The claim fails immediately at `n = 4`: `g(4)=2` but `g(4+12)=g(16)=5`.
The conjecture is therefore false as stated. Its "period 12" is wrong for
this game; the true eventual period is 34 with pre-period 53.

*Reading B.* The period 12 is in fact correct here, but the pre-period is
71, not 4, so the identity `g(n+12)=g(n) for all n ≥ 4` still fails
(first at `n = 10`: `g(10)=2`, `g(22)=6`).

Hence the claim fails under **both** readings.

## Files

```
.
├── README.md              this file
├── main.tex               standalone article (amsmath/amssymb/amsthm)
├── reproduce.py           stdlib-only numeric reproduction of both readings
├── build/
│   └── main.pdf           compiled article
└── lean4/
    ├── lean-toolchain     leanprover/lean4:v4.33.1
    ├── lakefile.toml      package tlmc1202
    ├── Main.lean          computable SG recurrence + n=4 refutation
    ├── Check.lean         #print axioms audit
    └── README.md          scope of the formalisation
```

## Reproduce

```sh
# numeric refutation (both readings, n up to 1000), exits 0
python3 reproduce.py

# formal refutation (core Lean 4, no Mathlib)
export PATH="/opt/homebrew/bin:$HOME/.elan/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean

# article
cd ..
tectonic --outdir build main.tex     # -> build/main.pdf
```

## Formal verification

`lean4/Main.lean` defines a fueled `mex`, a propext-free list lookup, the
computable recurrence `g n = mex{ g a XOR g b : a+b+2 = n }` by
structural recursion, and proves by kernel evaluation

* `g4 : g 4 = 2`
* `g16 : g 16 = 5`
* `period12_fails_at_4 : g 4 ≠ g 16`
* `conjecture_00000001202_false : g 4 ≠ g 16 ∧ g 4 = 2 ∧ g 16 = 5`

`Check.lean` (`#print axioms` per theorem) shows **no `sorryAx` and no
`ofReduceBool`**. Each theorem depends only on `propext`, a standard Lean
core axiom introduced by `Nat.xor` (the nim-sum), not on any user axiom.

The Lean file formalises the concrete refuting instance `n = 4` and the
computation of `g`; the full eventual period 34 / pre-period 53 and the
reading-B data (period 12 / pre-period 71) are established by exhaustive
computation in `reproduce.py` (see `lean4/README.md`).
