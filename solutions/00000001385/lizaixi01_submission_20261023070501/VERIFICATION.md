# Verification

The frozen source passed a new root build in a separate Lean4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit0, all32 named local declaration audits (17theorems plus15definitions/abbreviations/instances); only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit0, 478.9558 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at100dpi and visually checked by worker and supervising AI; no overfull boxes.
- Full proof, exact source scope, primary convention, report and PDF independently reviewed by a separate supervising Codex agent.

Main SHA256: `423209b9c982b1f82759d11061feb672e3732bed20ef3d9a43b4531fd880009e`. Structured receipts bind source, commands, exits and logs. One bounded owned process group at a time, CPUaffinity0,2. This selective production case is not an extra experimental sample.

The proof constructs actual probability Haar AddCircle1, identity measure-preserving involution, Lp-composition Koopman identity, true eigenspaces and closed real/modulus cutoff subspaces. It proves every actual HilbertBasis has cardinalaleph0 using actual Fourier coefficient countable supports and the infinite orthonormal family. The dimension-defining cardinality set is proved a nonempty singleton, not an empty-infimum fallback or assigned N. Actual cutoff dimensions at thresholds1 and2 arealeph0, contradicting the continuum jump by Cantor. All32 named declarations, including proof-bearing Fourier/isometry/basis constructions, are audited. Only the explicit threshold-function Hilbert-dimension reading is refuted; threshold2 is not a second spectral point, no Hamel or spectral-point-only sampling claim and no arbitrary complex order is assigned. Original bilingual source preserved. No sorry, native_decide or extra axiom. Organizer acceptance pending.
