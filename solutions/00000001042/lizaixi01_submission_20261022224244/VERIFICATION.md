# Verification record

The exact submitted Main.lean passed Lean 4.33.0 in a separate Linux project. Every dependency source was checked out at the manifest-pinned Git commit. Public dependency build artifacts were reused; the root Main artifact did not exist before the build. No earlier candidate Main artifact was copied.

- `lake build +Main`: exit 0, 1947 dependency jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0. All nine audited declarations depend only on propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 281.9655 seconds. This is an official Lean kernel replay, not a second independent implementation.
- LaTeX compiled successfully. Final PDF has two pages; both were rendered and visually inspected.
- A separate supervising Codex agent read the complete Main.lean and original source. It confirmed the exact fixed-d=1 scope and all finite-field/variance/limit bridges. This is an AI semantic review.

Structured receipts and exact source hashes are in evidence/. No external numerical computation is needed. SOURCE.md is the verbatim bilingual source.
