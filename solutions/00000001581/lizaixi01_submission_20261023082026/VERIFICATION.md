# Verification

The source passed a new root build in a separate pinned Lean 4.33.0 project; Main was newly compiled from this package. Dependency Git commits match the manifest.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all 57 named targets (32 theorems and 25 other definitions/abbreviations), including actual subtype equivalences and representations. Only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 303.7837 diagnostic WSL seconds. Official full kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually inspected by worker and separate supervising AI; no overfull boxes.
- Complete source semantics, exact scope, report and PDF reviewed by a separate supervising Codex agent.

Main SHA256: `a982847ac1979926e6c3ac333e33bf07037c9c9c22dd473a0652c81f327a5757`. Receipts bind source, commands, exits and log hashes. One bounded owned process group, CPU affinity 0,2; no owned residuals. This selective exposed production case is not a new experimental sample or an efficiency claim.

The actual standard PVI Cayley member has infinitely many genuine rational trace points, even with actual nonzero MvPolynomial partial derivative. The genuine four-punctured-sphere presentation maps to SL2(Q), and scalar-extended representations are pairwise not simultaneously SL2(C)-conjugate by actual trace invariance. Infinite/Cardinal.mk close the literal finite rational count obstruction, without an infinite Nat.card fallback. Conversely actual finite cubic/hyperbola fibers and quadratic-character sums prove q^2+1 for all finite fields of odd characteristic; ZMod 2 is directly counted, giving every prime p. The full affine finite count includes singular points. The standard Cantat-Loray model identification is cited; general RH/GIT and scheme-smoothness theorems are not re-proved. No formula for all other PVI parameters is asserted. Prior closed PR217's public direction and rejected object gap are explicitly attributed. Original bilingual source preserved. No sorry, native_decide or extra axiom. Organizer review pending.
