# Submission: refutation of conjecture 00000004007

**Conjecture (quoted).** Definition: The p-variation is the p-th root of the
supremum over partitions of the sum of p-th powers of the increments.
Conjecture: The p-variation satisfies the optimal subadditivity inequality
`‖X+Y‖ ≤ (‖X‖^q + ‖Y‖^q)^{1/q}`, where q is the conjugate exponent of p, and
the inequality cannot be enlarged. (optimal subadditivity of p-variation)

**Verdict: FALSE.**

## Summary of the refutation

The `p`-variation is the `p`-th root of a supremum, hence homogeneous of
degree 1:
```
‖aX‖ = |a| · ‖X‖ .
```
Take any non-zero path and put `Y = X`.  Then the two sides of the claimed
inequality are
* LHS `= ‖X+Y‖ = ‖2X‖ = 2 ‖X‖`, and
* RHS `= (‖X‖^q + ‖X‖^q)^{1/q} = 2^{1/q} ‖X‖`.

For the conjugate exponent, `q = p/(p-1) > 1` for every finite `p > 1`, so
`2 > 2^{1/q}` and the inequality fails.  Equivalently, at `X = Y ≠ 0` the
claim would require `2 ≤ 2^{1/q}`, i.e. `2^q ≤ 2`, which is false for every
`q > 1`.

For a two-point unit-step path (`‖X‖ = 1`) the numbers are:

| `p`  | `q = p/(p-1)` | LHS `= ‖X+Y‖` | RHS `= 2^{1/q}` |
|------|---------------|---------------|-----------------|
| 3/2  | 3             | 2             | 1.2599…         |
| 2    | 2             | 2             | 1.4142…         |
| 3    | 3/2           | 2             | 1.5874…         |
| 4    | 4/3           | 2             | 1.6818…         |
| 10   | 10/9          | 2             | 1.8661…         |

The failure is elementary and is caused precisely by the degree-one
homogeneity; that is why the stated inequality cannot be correct and cannot
be "enlarged".

The same conclusion holds in both normalisations and in the limit:
* **Raw-supremum reading** (if one ignores the stated root): `‖2X‖ = 2^p ‖X‖`
  against RHS `2^{1/q} ‖X‖`, which fails a fortiori (e.g. `p = 2`: `4` vs
  `1.4142`).
* **Limit case `p = 1`** (`q = ∞`): `X = Y` gives `2 ‖X‖ > ‖X‖ = max(‖X‖,‖Y‖)`.

## Files

| Path | Description |
|------|-------------|
| `README.md` | this file |
| `main.tex` | standalone article: definition, homogeneity lemma, the `X = Y` refutation, table of values, raw-supremum and `p = 1` cases; compiled to `build/main.pdf` |
| `reproduce.py` | stdlib-only exact-arithmetic verification (`fractions`): `‖X‖`, `‖X+Y‖`, claimed RHS for `p = 3/2, 2, 3, 4, 10`; raw-supremum reading; `p = 1` limit; prints PASS and exits 0 |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1` |
| `lean4/lakefile.toml` | Lake project `tlmc4007` |
| `lean4/Main.lean` | core-Lean formalisation of the arithmetic core (no Mathlib, no `sorry`, no `axiom`, no `native_decide`, no `ℝ`) |
| `lean4/Check.lean` | `import Main` + `#print axioms` for each theorem |
| `lean4/README.md` | precise scope of the Lean formalisation |
| `build/main.pdf` | compiled article |

## Reproduce

```bash
# exact-arithmetic verification (stdlib only)
python3 reproduce.py

# Lean formalisation
export PATH="/opt/homebrew/bin:$PATH"
cd lean4 && lake build
lake env lean Check.lean

# article
export PATH="/opt/homebrew/bin:$PATH"
mkdir -p build && tectonic --outdir build main.tex
```

## Formalisation scope

The Lean file formalises the **arithmetic core** of the obstruction only.  It
proves, in core Lean 4 (`Nat` only, since core Lean has no `ℝ` and `decide`
cannot reduce `Rat` operations):

* `q_eq_two_fails` — `¬ (2^2 ≤ 2)`, the case `p = 2` (`q = 2`), by `decide`.
* `q_eq_two` — `2^2 = 4`, by `decide`.
* `q_eq_three_halves_fails` — `¬ (2^3 ≤ 2^2)`, the case `p = 3` (`q = 3/2`;
  `2^{3/2} ≤ 2 ⟺ 2^3 ≤ 2^2`), by `decide`.
* `pow_two_gt_two` — `∀ q : Nat, 1 < q → 2 < 2^q`, the general fact behind
  `2^q ≤ 2` being false for `q > 1`, proved by induction.
* `conjecture_00000004007_false` — collects the two instances and the general
  fact, with a comment explaining that homogeneity reduces the conjecture to
  precisely these false inequalities.

The p-variation itself (a real-valued functional of a path), the homogeneity
`‖aX‖ = |a| ‖X‖`, and the reduction `X = Y` of the conjecture to `2^q ≤ 2`
are **not** formalised in Lean (no `ℝ` in core Lean).  They are stated and
proved in `main.tex` and checked with exact rational arithmetic in
`reproduce.py`; see `lean4/README.md`.

## Uncertainty

The refutation is unconditional and elementary: the counterexample `X = Y`
is non-zero and the failure follows from degree-one homogeneity and `q > 1`.
Verified by the project owner.  The only limitation is that the real-valued
p-variation is argued on paper / verified numerically rather than formalised
in Lean, since core Lean has no real numbers; the formalised arithmetic
inequalities `2^q ≤ 2` are exactly the content that the obstruction reduces
to.
