# Proof of conjecture 00000000347

This submission proves the existence of a transcendental real whose ordinary continued-fraction partial quotients form a Sturmian word: exactly `n + 1` distinct contiguous factors of every positive length `n`.

The source leaves the first index implicit. Both conventions are proved, using reciprocal witnesses:

- `SturmianCF.conjecture00000000347` counts the fractional word `a₁, a₂, …` of a real with integer part zero.
- `SturmianCF.conjecture00000000347_including_integer_part` counts the entire word `a₀, a₁, …` of its reciprocal.

Each theorem states transcendence, positive remainders at every step of the actual floor-and-invert algorithm, partial quotients in `{1, 2}`, and finite factor sets of cardinality `n + 1`. The result is existential; it does not name a specific transcendental slope.

## Argument and files

`report.tex` and the matching `report.pdf` contain the full argument. Irrational slopes produce injectively distinct mechanical words. A finite-word argument proves exact Sturmian complexity. A contraction constructs their ordinary continued-fraction reals and recovers their digits from the actual algorithm. This gives an uncountable family, so countability of algebraic reals supplies a transcendental member.

`ORIGINAL.md` is the exact bilingual conjecture. The `lean/` directory contains the complete pinned Lean project, the author's replay script, and the independent verification harness. The `verification/` directory contains source-bound author, semantic, build, dependency, and PDF records. Historical failed attempts and deliberately invalid verification controls are evidence, not active proof modules.

## Reproduce

Use Lean 4.19.0. Mathlib and its dependencies are pinned in `lean/lake-manifest.json`; Mathlib's revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

For an ordinary build, from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true AxiomAudit.lean
```

For the complete isolated verification, use a new work directory outside this submission:

```sh
python3 lean/verify.py --lean-bin /path/to/lean-4.19.0/bin \
  --work-dir /path/to/new-verification-directory
```

An existing stock checkout/cache at the pinned revision can be supplied with `--stock-mathlib /path/to/mathlib`. The verifier copies it privately, verifies its tracked sources against the pinned Git blobs before and after the build, and records reused compiled dependencies. It does not claim to rebuild all of Mathlib.

The full verifier builds every submitted Lean module, replays them with warnings treated as errors, audits all mathematical declarations and their dependency closures, checks its rejection controls, and executes the author's replay script. No numerical computation or external computational assumption is needed for the mathematics.

## Review status

Author checks, independent semantic review, isolated engineering verification, and a second build from the packaged sources are recorded separately. These are contributor-side checks; maintainer acceptance is not claimed. The historical public-eligibility observations have explicit scope and time bounds in `verification/eligibility.json`.
