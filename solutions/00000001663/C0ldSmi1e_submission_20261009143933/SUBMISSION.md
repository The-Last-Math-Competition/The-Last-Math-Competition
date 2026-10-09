# Submission for conjecture 00000001663

This package disproves the complete **literal strengthened conjunction**. Its added same-deck lower bound fails when the empty graph on three vertices is paired with itself: the decks agree and edit distance is zero. **It does not prove or disprove classical Kelly–Ulam reconstruction**, nor a different assertion with an added nonisomorphism hypothesis.

Read `solution.pdf` and its matching `solution.tex` for the complete mathematical report. `REPORT.md` is the independent mathematical author's detailed account. `VERIFICATION.md` provides the exact validation results, strict recorded-environment replay, and ordinary pinned-source build commands for other platforms.

The Lean project is in this folder. Its roots are `Conjecture1663.lean` and `Verification.lean`. Run the commands in `VERIFICATION.md`; no dependency or toolchain update is needed. `source/ORIGINAL.md` preserves the exact bilingual conjecture. Changes to the repository are confined to this personal submission folder.

## Evidence boundaries

`evidence/DELIVERABLE_HASHES.json` is the frozen author's 91-file sub-bundle inventory, excluding that inventory itself. It does not claim to inventory later root packaging additions. The author-stage README and EXPORT record that handoff. The final package inventory is `PACKAGE_SHA256SUMS.json`, excluding only itself.

`evidence/pdf/` records the successful editor compilation, matching PDF export and visual inspection. Independent review records describe exactly which sources, logs and PDF bytes were examined. Review harnesses and recorded absolute paths under `evidence/` describe those recorded runs; use the top-level `scripts/` commands for reproduction. Local verification and independent agent reviews are distinct from maintainer acceptance.

The replay retains only small owned compiled files in archived evidence workspaces so their receipts remain checkable. These are never substituted for a fresh build: a new replay creates a new owned workspace. External dependency caches are excluded. Cache reuse, missing runtime sources, binary fingerprints and the limits of source-to-binary verification are documented explicitly.

## Regenerate the PDF

Using a standard TeX environment, compile `solution.tex` with `tectonic --keep-logs solution.tex` or a compatible LaTeX engine. The submitted export used Tectonic 0.17.0; the desktop editor compiler also succeeded. Re-render and visually inspect all pages after any report edit. PDF metadata may change between compilations, so compare the report content as well as build diagnostics.
