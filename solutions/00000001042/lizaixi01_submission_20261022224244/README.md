# Conjecture 00000001042: exact affine variance

This submission disproves the fixed-degree, growing-field interpretation of the conjecture, using d=1. The source does not specify a limiting regime; this submission does not assert a conclusion for a different d-to-infinity regime.

For every finite field of size q, a uniform polynomial of degree at most one has value-set variance (q-1)^3/q^2. The normalized variance tends to 1 along prime fields, contradicting the proposed 1-1/e. All counting, the finite-polynomial enumeration, variance and asymptotic comparison are formalized in Lean.

## Reproduce

Install Lean via elan, then from `lean/`:

```sh
lake exe cache get
bash verify.sh
```

The checked-in manifest pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, and all transitive Git revisions. The cache command is an optional public Mathlib build cache. `lake build +Main` compiles the complete proof; `Check.lean` prints transitive axiom dependencies; `leanchecker --fresh Main` rechecks the imported proof environment with the official Lean kernel. It is not an independently implemented kernel.

From this directory, compile the report with `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice. The committed PDF was rendered and both pages visually inspected.

## Previous submission

PR155, https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/155, was closed unmerged because its Lean proof checked only q=101, while its general formula and limiting comparison were not formalized. We credit its mathematical observation. This package proves both missing general steps and discloses the interpretation. See the report and maintainer review https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/155#issuecomment-5951812972.

## Provenance and evidence

The source statement is preserved in SOURCE.md at upstream commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. Mathematical authoring and report preparation used OpenAI Codex; a separate supervising Codex agent read the full source for semantic review. This is AI review, not human certification. The proof contains no admitted steps, native decision shortcuts, or new axioms. Evidence receipts bind the checked source SHA256 to commands and logs. Organizer review remains pending.
