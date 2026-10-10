# Validation

- Full `lake build` completed successfully with Lean 4.19.0 and pinned Mathlib (2864 targets).
- Six printed axiom audits, including strict log-convexity and the final characterization biconditional, contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The project contains no proof placeholders, native evaluation shortcut, unsafe declaration, or custom axiom.
- The mathematical objects are Mathlib's actual `Real.Gamma`, real logarithm, convexity, and strict convexity on the positive real domain. Library Bohr–Mollerup is a proved theorem; the rescaling and strictness arguments are supplied in this project.
- Existing Tectonic compiled the PDF after the built-in editor compiler returned its known platform-directory error. All three pages were rendered using Poppler and visually inspected; all text and equations are legible and unclipped.
- Only personal submission files are included; dependency caches and build outputs are excluded. Public dependency pins and the reproduction command are included.
