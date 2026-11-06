# Verification

The frozen source passed a new root build in a separate pinned Lean 4.33.0 project. Main was newly compiled, and dependency Git commits match the manifest.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all 42 targets (39 explicit named declarations including 16 theorems and 2 interpretation instances, plus GroupSymbol.one/inv/mul). Only standard allowed axioms or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 186.9299 diagnostic WSL seconds. Full official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually inspected by worker and separate supervising AI; no overfull boxes.
- Complete source scope, model-theoretic proof, report and PDF reviewed by a separate supervising Codex agent.

Main SHA256: `f9cf57bb2c1795c6d3c4ab925311f7313927e5edf0a7df3fcb10e0e68549d18f`. Receipts bind source, commands, exits and log hashes. One bounded owned process group, CPU affinity 0,2, no owned residuals. This selective production case is not an additional experimental sample or an efficiency claim.

The actual group is S5, equipped with its real first-order identity, inverse and product symbols and actual named constants. The domain, unit, inverse graph and multiplication graph are genuine formulas with proved realization equivalences. Its actual complete theory contains a finite-cover sentence, so all its models are finite in any universe. Actual arbitrary-arity IP and full two-row singleton-x ICT patterns would inject the natural numbers into a finite tuple/model; both are impossible. Genuine Mathlib nonsolvability completes the source's unrestricted finite-case counterexample. The published dp-minimality pattern criterion is formalized, not a general numerical dp-rank function. No infinite-only, connected or virtual-solvability/nilpotence version is refuted. Full bilingual original source preserved, no earlier same-ID PR found. No sorry, native_decide or extra axiom; organizer acceptance pending.
