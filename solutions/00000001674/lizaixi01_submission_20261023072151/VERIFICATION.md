# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, all 24 targets (12 theorems, other named local declarations, MinorModel, its constructor and five projections); only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 178.3739 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI; no overfull boxes.
- Full proof, exact source scope, primary convention, report and PDF independently reviewed by a separate supervising Codex agent.

Main SHA256: `ab4dd23b5c9e286f2c4da6494140f1bf1b067198eb920fd01b693e2699871bb5`. Structured receipts bind source, commands, exits and logs. One bounded owned process group at a time, CPU affinity 0,2. This selective production case is not an extra experimental sample.

The actual star with n leaves is a tree with n actual edges. The actual k-grid has two endpoint-disjoint edges for every k>=2. In any genuine branch-set model, their star cross-edge witnesses would force the unique center into two disjoint branch sets, a contradiction. Thus stars give arbitrary edge counts while excluding every such grid minor. The proof covers arbitrary finite real envelopes and asymptotic cutoffs, and explicitly negates a k-only bound over all actual finite graphs. It only refutes the source literal edge-count upper-bound premise, not the true treewidth theorem, vertex-count-dependent bounds or independent lower-bound existence. The primary-supported branch-set definition is used directly. Original bilingual source preserved. No sorry, native_decide or extra axiom. Organizer acceptance pending.
