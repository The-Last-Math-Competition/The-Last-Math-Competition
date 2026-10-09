# Disproof of Conjecture 00000007914

The asserted asymptotic for the k-th covolume is incompatible with finite ranks in a nonnegative real spectrum: the first two ranks give 0 <= v_1 < v_2 <= v_k for k >= 2, while the literal comparison function tends to zero. The proof allows zero limit values and every fixed real constant, and covers ordinary limits, closure selections, and finite liminf. This disproves the conjunction without a separate triangle-group classification.

- `conjecture.md`: exact original English and Chinese statement.
- `proof.tex` / `proof.pdf`: full mathematical argument and source correspondence.
- `lean/`: complete Lean 4.19.0 project, pinned Mathlib v4.19.0, audit and portable verifier.
- `SEMANTIC_REVIEW.md`: independent local mathematical review, with final layout check.
- `VERIFICATION.md` and `verification/`: reproducibility scope and full local validation records.

## Reproduce

With Python 3, Git, and Lean's elan/Lake tooling installed:

```sh
cd lean
lake exe cache get
python3 verify.py
```

See `lean/VERIFY.md` for exact checks. The verifier regenerates only this project's build cache, retains stock dependency caches, and writes new logs inside ignored `.lake/verification/`. It checks source hashes, all twelve theorem types and axiom reports, strict replay, and all nine pinned dependency revisions.

Compile the report with a standard LaTeX installation (`pdflatex proof.tex`, twice), or `tectonic proof.tex`. The checked PDF was exported with Tectonic and inspected on every page. No auxiliary numerical computation is required. All checks recorded here are local verification; maintainer acceptance is separate.
