# Conjecture 00000000214: disproof

For the actual integer-partition count `p(n) = Fintype.card (Nat.Partition n)`, the formal project proves

`¬ ∃ N : ℕ, ∀ n ≥ N, log p(n+3) - 3*log p(n+2) + 3*log p(n+1) - log p(n) < 0`.

In fact, strictly positive third differences occur arbitrarily far out. The standard backward convention is also covered by shifting the index by three. The source's undefined “convexification layer” receives no invented definition; the necessary eventual-negativity assertion is refuted directly.

The proof uses an injection encoding actual partitions to obtain an elementary counting bound, then a generic real-sequence argument. There are no numerical auxiliary computations or partition asymptotic formulas.

## Contents

- `report.tex` and `report.pdf`: readable mathematical argument and formal correspondence.
- `TLMC214/PartitionBounds.lean`: actual partition definitions, lower bound, injective finite encoding and upper bound.
- `TLMC214/Growth.lean`: nonnegativity, unboundedness and absence of a positive affine lower bound for the partition logarithm.
- `TLMC214/Sequence.lean`: generic sequence theorem.
- `TLMC214/Disproof.lean`: concrete capstones `disproof`, `positive_arbitrarily_late`, and `backward_disproof`.
- `CheckAxioms.lean`: theorem and foundational axiom audit.
- `source/`: exact bilingual statement and the supplied repository rules.
- `evidence/`: retained command outputs, failed attempts and source snapshots; see `PROVENANCE.md`.

## Reproduce

Install the Lean toolchain selected by `lean-toolchain` using the normal Lean/elan tooling. From this folder, run:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true TLMC214/PartitionBounds.lean
lake env lean -DwarningAsError=true TLMC214/Sequence.lean
lake env lean -DwarningAsError=true TLMC214/Growth.lean
lake env lean -DwarningAsError=true TLMC214/Disproof.lean
lake env lean -DwarningAsError=true TLMC214.lean
lake env lean -DwarningAsError=true CheckAxioms.lean
```

The committed manifest pins every dependency; keep it when reproducing the build. `lakefile.lean` also pins Mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0), and `lean-toolchain` pins Lean 4.19.0. The project has no machine-local path dependencies. The author's local verification used a private copy of the unchanged pinned stock package tree, leaving the stock cache untouched; its disposable `.lake` directory is not a submission artifact.

The axiom output for each capstone should list only `[propext, Classical.choice, Quot.sound]`. Warnings are errors for the project, and the commands above independently replay each source file. The report is a standalone LaTeX document; compile `report.tex` with a standard LaTeX toolchain or the built-in editor compiler.

## Scope

The conclusion addresses the full eventual quantifier on actual partitions. It does not supply an explicit threshold, prove eventual positivity, assume log-concavity, or claim maintainer acceptance. Full publication eligibility is checked separately by the submitting workflow.

## Independent checks

`independent-review/REVIEW.txt` contains a separate full mathematical and bilingual-source review. `parent-verification/` records the final report compilation, visual inspection of all four PDF pages, and the submitting contributor's checks. The mathematical modules are unchanged from the independently built author package. The report's only subsequent edit splits two long definitions into separate display lines.

Historical failed attempts in `evidence/` are provenance, not imports or build targets. Their `.lean.txt` snapshots must not be substituted for the current `TLMC214/` sources. `parent-verification/author-SHA256SUMS.json` records the original author handoff; the top-level `SHA256SUMS.json` covers the final assembled submission.

`verification/README.md` documents the independent build, the full declaration audit, the negative controls, preserved failures, and the complete offline replay scripts. Its evidence archive excludes dependency/build copies. Normal portable Lean commands are listed above; the optional full offline harness uses a supplied stock library on macOS.
