# Submission: refutation of conjecture 00000000277

**Conjecture (quoted).** Definition: `M(T)` is the maximum multiplicity of a
Laplace eigenvalue on a planar flat torus `T = C/Λ`, and `M` its supremum over
all flat tori. Conjecture: `M = 6` (6 is known to be attainable, and upper
bounds ≥ 6 are constrained by congruence structure); and multiplicity six is
attained only on the lattice torus with maximal automorphism group of order
thirty-two.

**Verdict: FALSE** (verified by the project owner), under **both** readings of
`M`.

## Summary of the refutation

On a flat torus `R²/Λ` the Laplace eigenvalues are `4π²|k|²` for `k` in the
dual lattice `Λ*`, and the multiplicity of `4π²N` is the number of dual
vectors of squared length `N`.

* **Literal reading (maximum over all eigenvalues).** On the square torus
  `Λ = Z² = Z[i]` the dual lattice is `Z²`, so the multiplicity of the
  eigenvalue `4π²N` is `r₂(N)`, the number of representations of `N` as a sum
  of two squares. Jacobi's theorem gives `r₂(N) = 4(d₁(N) − d₃(N))`, and for
  `N = 5^k` (all divisors `≡ 1 mod 4`) this is `r₂(5^k) = 4(k+1) → ∞`. The
  explicit values are

  | k | N = 5^k | r₂(N) = 4(k+1) |
  |---|---------|-----------------|
  | 0 | 1       | 4               |
  | 1 | 5       | 8               |
  | 2 | 25      | **12**          |
  | 3 | 125     | 16              |
  | 4 | 625     | 20              |
  | 5 | 3125    | 24              |

  So the multiplicity is unbounded and `M = ∞`, not `6`. The decisive witness
  is `r₂(25) = 12 > 6`: the square torus already has an eigenvalue
  `4π²·25` of multiplicity 12.

* **The order-thirty-two clause is impossible under either reading.** A
  rotation preserving a planar lattice has finite order `n` only if
  `2cos(2π/n) ∈ Z` (it is the trace of an integer matrix), which forces
  `n ∈ {1,2,3,4,6}` (crystallographic restriction). Hence the largest possible
  automorphism-group order of a planar lattice is `12` (the dihedral group of
  order 12 for the hexagonal lattice) — never `32`. There is no
  "order-thirty-two lattice torus".

## Honest qualification

If `M` had been intended as the multiplicity of the **first non-zero**
eigenvalue only, then `6` **is** correct: it is attained by the hexagonal
(triangular) lattice (two-dimensional kissing number 6). But the order-32
clause is impossible under both readings, and the unboundedness argument
applies to the literal reading (maximum over all eigenvalues). Therefore the
statement is false **as written**.

## Files

| Path | Description |
|------|-------------|
| `README.md` | this file |
| `main.tex` | standalone article: flat-torus spectral setup, `r₂` computation, unboundedness, crystallographic restriction, honest first-eigenvalue note; compiled to `build/main.pdf` |
| `reproduce.py` | stdlib-only exact check of `r₂(5^k) = 4(k+1)` for `k = 0..5`, the square/hexagonal first-eigenvalue multiplicities, `12 > 6`, and the crystallographic restriction; prints PASS and exits 0 |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1` |
| `lean4/lakefile.toml` | Lake project `tlmc277` |
| `lean4/Main.lean` | core-Lean formalisation of the `r₂` counts and a limited trace obstruction to order 32 (no Mathlib, no `sorry`, no `axiom`, no `native_decide`) |
| `lean4/Check.lean` | `import Main` + `#print axioms` for each theorem |
| `lean4/README.md` | precise scope of the Lean formalisation |

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

The Lean file formalises, in core Lean (`import Std`, no Mathlib):

* `r2 1 = 4`, `r2 5 = 8`, `r2 25 = 12`, `r2 125 = 16`;
* `multiplicity_exceeds_six : 6 < r2 25`, the decisive witness;
* `trace_constraint_of_order_thirtytwo`, an exact integer Chebyshev-recurrence
  statement showing that the order-32 relation forces the trace into
  `{-2, 0, 2}` within the geometrically allowed range `[-2, 2]`;
* `conjecture_00000000277_false`, collecting the above.

**Not** formalised in Lean (documented in `main.tex` and `lean4/README.md`):
the analytic eigenvalue–multiplicity correspondence `4π²N ↔ r₂(N)`, Jacobi's
two-square formula, the identification of traces `-2, 0, 2` with rotations of
order dividing 4, the full crystallographic restriction (needs `ℝ`/`ℂ`), and
the unboundedness conclusion.

## Axiom audit

```
'Tlmc277.r2_1' does not depend on any axioms
'Tlmc277.r2_5' does not depend on any axioms
'Tlmc277.r2_25' does not depend on any axioms
'Tlmc277.r2_125' does not depend on any axioms
'Tlmc277.multiplicity_exceeds_six' does not depend on any axioms
'Tlmc277.trace_constraint_of_order_thirtytwo' depends on axioms: [propext, Quot.sound]
'Tlmc277.conjecture_00000000277_false' depends on axioms: [propext, Quot.sound]
```

No `sorryAx` and no `Lean.ofReduceBool` (`ofReduceBool`).

## Uncertainty

* None about the verdict: the square-torus computation `r₂(25) = 12` is exact
  and kernel-checked, and the crystallographic restriction is classical.
* The only interpretive caveat is the intended meaning of `M` (all eigenvalues
  vs. first eigenvalue); this submission refutes the statement under both
  readings, and states explicitly where the value `6` is correct.
