# Conjecture 00000001569: disproof

The original permits collinear point sets. The `n` points `(0,0), ..., (n-1,0)` determine at most two ordinary unsigned Euclidean angle values. For every real linear-loss constant `C` and every threshold `N`, a sufficiently large member of this family has fewer than `n² - Cn` distinct angles. This refutes the uniform lower-bound clause and therefore the stated conjunction. The submission does not assign an invented meaning to the additional lattice-attainment phrase.

Read `ORIGINAL.md` for the complete bilingual statement, and `report.pdf` or its matching `report.tex` for the argument and conventions. `lean/Solution.lean` contains the mathematical definitions and proofs, including the exact angle-set membership correspondence and the full asymptotic negation.

## Reproduce verification

Use Lean **4.19.0**. `lean/lean-toolchain` and `lean/lake-manifest.json` pin the compiler and all nine standard-library dependencies, including Mathlib v4.19.0. Python verification requires only Python 3's standard library.

From this submission directory, prepare the standard dependency cache:

```sh
cd lean
lake exe cache get
cd ..
```

Then rebuild in an isolated fresh project and audit every declaration owned by the mathematical module:

```sh
python3 verify.py --output /tmp/tlmc1569-verification
python3 test_verify.py --compiled-controls --output /tmp/tlmc1569-controls
```

Each output directory must be new. To use an existing installation, add `--lake /path/to/lean-4.19.0/bin/lake --dependency-root /path/to/pinned/packages` to both commands. The dependency directory must contain the nine exact clean Git checkouts and their Lean 4.19.0 build cache. The verifier itself performs no downloads.

The runner checks exact frozen source identities, clean dependency revisions before and after execution, a fresh complete project build, and direct source replay with warnings treated as errors. It inspects every compiled mathematical declaration and traverses the transitive type and value dependencies, including theorem proof values. The only permitted proof axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The controls deliberately introduce invalid temporary fixtures to confirm that defects are rejected; those fixtures are not part of the mathematical project.

The proof is deductive. No auxiliary numerical computation is required to establish its conclusions. `VERIFICATION.md` records the actual local validation and independent semantic review. These checks do not imply maintainer acceptance.
