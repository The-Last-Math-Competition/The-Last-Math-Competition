# Conjecture 00000007788: disproof in dimension two

The source samples points uniformly from the solid body. For independent uniform samples in the Euclidean unit disk, this project proves that the expected volume deficit satisfies

`deficit N ≥ 1 / (4 * ((N : ℝ) + 1))`.

Consequently `N² * deficit N → +∞`. It cannot have the conjectured asymptotic form `c * N^(-2)` for any positive finite constant `c`. The disproof refutes the necessary ball assertion at dimension two; it does not reinterpret the separate constant-ratio or simplex clauses.

## Contents

- `Conjecture7788.lean`: exact disk, normalized Lebesgue law, independent product sample law, actual random convex-hull area, measurability and integrability, expected-volume correspondence, lower bound, and final contradiction.
- `Conjecture7788/HullMeasurable.lean`: finite-hull membership is closed in the joint sample/point variables; its section volume is measurable.
- `Conjecture7788/GenericRate.lean`: generic analytic consequences of the reciprocal-linear lower bound, including literal real-power asymptotic inequivalence.
- `Audit.lean` and `DECLARATIONS.txt`: types and axiom inspections for all 40 named authored declarations, including definitions and probability instances.
- `MATHEMATICAL_NOTES.md`: complete proof and source correspondence.
- `verify.py`: offline reproducibility checks; `SOURCE_HASHES.json`: frozen source hashes; `validation/`: raw per-command results and machine-readable summary.

## Reproduce

Use Lean **4.19.0** and the **exact nine Git revisions** in `lake-manifest.json`, including Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Prepare these ordinary dependencies and their stock caches through Lake before offline verification. Place the matching `lake`/`lean` executables on `PATH`, then run:

```text
python3 verify.py
```

The script verifies frozen source hashes, toolchain version, all nine dependency revisions and clean worktrees. It removes only this project's `.lake/build`, then performs a clean authored build, replays every authored Lean source with `-DwarningAsError=true`, and checks that every declared result uses only `propext`, `Classical.choice`, and `Quot.sound`. Each command's exact arguments, status, stdout, and stderr are recorded under `validation/`. Dependency sources and caches are never removed or edited.

There are no numerical simulations, enumeration certificates, custom axioms, proof placeholders, or native-decision bypasses. All mathematical work is symbolic. The verification script is infrastructure, not an auxiliary mathematical computation.

This packet is research/review material. LaTeX/PDF preparation and publication are coordinated separately.
