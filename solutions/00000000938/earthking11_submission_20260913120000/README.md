# Rule-3 disproof of conjecture 00000000938

**Verdict: FALSE.** The claim that the Banach--Mazur distance between
`l1^n` and `linf^n` "is exactly `sqrt(n)` (the Goldstine ratio)" is refuted
already at `n = 2`.

## The claim under test

From `conjectures/00000000938.md`:

> the distance between `l1^n` and `linf^n` is exactly `sqrt(n)` (the Goldstine
> ratio)

The text places no restriction on `n` and gives no asymptotic qualifier, so it
asserts an exact identity for all `n`. This submission refutes that sentence.

## The counterexample

Define the linear map `T(x1, x2) = (x1 + x2, x1 - x2)`. For every `x`,

```
||T x||_inf = max(|x1 + x2|, |x1 - x2|) = |x1| + |x2| = ||x||_1
```

(the key identity `max(|a+b|, |a-b|) = |a| + |b|`). Hence `T` is a bijective
linear **isometry** from `l1^2` onto `linf^2`:

* it maps the `l1^2` unit ball (a diamond with vertices `(±1,0), (0,±1)`) onto
  the `linf^2` unit ball (a square with corners `(±1,±1)`);
* `||T|| = ||T^{-1}|| = 1`, so `d(l1^2, linf^2) = 1`.

Since `1^2 = 1 != 2 = (sqrt 2)^2`, the true value `1` differs from the claimed
`sqrt(2) ≈ 1.41421`. The sentence fails at `n = 2`.

## The correct quantity

`sqrt(n)` is the Goldstine ratio for the **other** pairs:

```
d(l1^n, l2^n) = sqrt(n),   d(l2^n, linf^n) = sqrt(n).
```

By contrast `d(l1^n, linf^n)` is of order `n`: there are absolute constants
`c, C > 0` with `c*n <= d(l1^n, linf^n) <= C*n` (the endpoint `p=1, q=inf` of
the classical estimate `d(lp^n, lq^n) ~ n^{1/p - 1/q}`). So `sqrt(n)` is the
wrong order of magnitude, not merely an off-by-a-constant error. The
conjecture's sentence is not marked "asymptotic", and even the asymptotic
reading would be false.

## Contents

| Path | Purpose |
| --- | --- |
| `main.tex` | Standalone article: definitions, isometry, `n=2` counterexample, correct-order remark. |
| `reproduce.py` | Stdlib-only numerical check over all integer vectors in `[-25,25]^2`, vertex check, `d = 1` vs `sqrt(2)`. PASS/FAIL, exit 0. |
| `lean4/` | Core-Lean formalisation (no Mathlib, no `sorry`). |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake project `tlmc938`, target `Main`. |
| `lean4/Main.lean` | The isometry identity, `T`, vertex mapping, and `1^2 != 2`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Build and audit instructions. |

## Reproduction

```sh
# Numerical check
python3 reproduce.py

# Formal check (Lean 4.33.1, install-free if the toolchain is present)
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean

# PDF
tectonic --outdir build main.tex   # -> build/main.pdf
```

Expected: `reproduce.py` prints `OVERALL: PASS` and exits 0; `lake build`
succeeds; the axiom audit shows only `propext` and `Quot.sound` (and possibly
`Classical.choice`), never `sorryAx` or `Lean.ofReduceBool`.

## Honest scope

This submission refutes **only** the `l1^n`--`linf^n` sentence of conjecture
00000000938. The conjecture's other assertions (about the asymptotic diameter
`d_n`, the limit `d_n/n -> 1`, and the mixed-norm space attaining the diameter)
are not addressed here.
