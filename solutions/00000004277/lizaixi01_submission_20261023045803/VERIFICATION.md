# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 1690 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-five transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 212.2153 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `48c094126caee556807f86552cdf28997e020d87db15a292853f6d462cca8827`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof uses the full standard height-characteristic quotient with strict preservation of infinity patterns and the standard representative order. A genuine Lattice instance and quotient meet/join formulas are verified. A real-indexed zero/infinity cut family is an uncountable actual chain, and its Zorn maximal-chain extension cannot be order-isomorphic to the countable printed ordered sum. The audit includes every theorem and all three proof-bearing instances. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
