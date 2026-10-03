# Conjecture 00000008435: disproof submission

Four successive derivations of symmetric designs.

Submitter: **gaochengzhecpu**. AI-assisted with Codex; draft for mathematical review.

## Scope

The source does not exclude complete complement-of-singleton designs. Both block and point derivations agree in this example.

Read `proof.pdf` for the complete ordinary proof, explicit assumptions and the correspondence to `Main.lean`. The LaTeX source is `proof.tex`. This submission preserves the locally reviewed source and PDF byte for byte; their draft labels do not imply organizer acceptance.

## Reproduce

Use Lean **4.19.0**, then run in this directory:

```text
lake build
```

Only Lean's bundled standard libraries are needed; there is no Mathlib dependency. The Lake configuration treats warnings as errors. Principal declarations print their axiom dependencies. Local checks found no `sorry`, `admit`, `native_decide` or added axioms; only standard Lean foundational axioms occur. `lean-verification.txt` records the successful local build.

Rebuild the PDF with `tectonic proof.tex` (or a standard LaTeX toolchain).

## Provenance and local validation

Original statement: [conjecture 00000008435](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008435.md). An unchanged bilingual copy is included as `SOURCE.md`.

Lean compilation, exact source correspondence, AI cross-review, and rendered-PDF inspection were completed locally. The source hashes in `verification.json` identify the checked artifacts. This is a draft submission, not an official review or an accepted result.

Immediately before preparing this submission, official metadata did not mark this conjecture solved, and no matching conjecture number was found in the titles or bodies of the 298 public PRs checked at 2026-10-03T13:15:11.955212+00:00. This limited check is not a claim of mathematical novelty or priority.
