# Verification

The frozen source passed a new root build in a separate pinned Lean 4.33.0 project. Main was newly compiled, and dependency Git commits match the manifest.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all 32 named targets (20 theorems, 11 definitions/abbreviations and the charTwo instance). Only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 326.2874 diagnostic WSL seconds. Full official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually inspected by worker and separate supervising AI; no overfull boxes.
- Complete source scope, algebraic/asymptotic proof, report and PDF reviewed by a separate supervising Codex agent.

Main SHA256: `612c2df266dea87bd53feb386a1687555078d284b280a48caccc26fc8dcaa198`. Receipts bind source, commands, exits and log hashes. One bounded owned process group, CPU affinity 0,2, no owned residuals. This selective production case is not an additional experimental sample or an efficiency claim.

The actual ring is F2[[X]], with true Krull dimension 1 and maximal ideal I=(X). The iterated Frobenius ideal map gives (X^(2^e)), proved contained in I. The actual R-module I/I^[2^e] is realized using its true comap denominator. Multiplication by X induces a real quotient linear equivalence from R/(X^k) to I/(X^(k+1)); transporting genuine DVR Module.length yields 2^e-1. Finite length is established before extracting a numerical value. The value is cofinally unbounded for all constants and cutoffs, not O(q^0), and has no finite coefficient limit under that normalization. The printed opposite quotient direction is invalid already at q=2, but the substantive proof addresses the natural correction. No field-vector dimension or the different quotient R/I^[q] replaces I/I^[q]. No general Newton-boundary or exact-leading-exponent theorem is claimed. Prior PR285 direction and missing real-object/asymptotic bridges are attributed and repaired. Full original bilingual source preserved. No sorry, native_decide or extra axiom. Organizer acceptance pending.
