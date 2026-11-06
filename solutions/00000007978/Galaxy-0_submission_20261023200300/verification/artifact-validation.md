# Artifact and reproduction checks

2026-10-23 UTC. Six modules, 42 named theorems.

- Author fresh compile: all six passed --trust=0 -DwarningAsError=true, followed by leanchecker replay; see verification.log.
- Actual Lake build: all eight jobs passed; CouplingIndexed is an explicit default-library root, not an unbuilt extra file.
- Axiom audit: only propext, Classical.choice, Quot.sound.
- LaTeX compiled twice to four pages. All pages independently rendered and visually inspected; no clipping or overlap. Final PDF SHA256 f99f4dd73473691bd96d3ebdbc8dcc5646a4dde1147b338e4542fe44917fba50.
- build_pdf.sh was then executed from a fresh copy containing only the TeX and script, rebuilding its font map from installed system files. Output was four pages with text identical to the delivered PDF. No fonts or proprietary build binary are bundled.
- The independent-review directory is a nonauthor audit of all sources and mathematical coverage; the coauthor-review directory accurately discloses authorship of auxiliary counting/coupling modules.
- Kernel replay is Lean kernel replay, not a second implementation of Lean's trusted kernel. No benchmark test or approximate computation is treated as proof.
