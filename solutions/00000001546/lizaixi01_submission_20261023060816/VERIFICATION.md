# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, eleven transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 305.3791 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- The single PDF page rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `e82bf62c4f4373911643add0470a1d5c636a856a54dfa4ff5f87faac42ee6a70`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof refutes the printed necessary growth conjunction universally, without assigning actual geometric counts. Real square nonnegativity gives Csqrtlogx<=logx+C^2/4, hence x*exp(Csqrtlogx)<=exp(C^2/4)*x^2 for everyC andx>=1. Actual IsBigO transitivity, the Oinsideexph bridge and eventual equality transfer imply a quadratic bound for every candidate function. Norm bounds handle arbitrary real-valued functions, while one-sided bounds explicitly require nonnegativity and are specialized to natural counts. Absence of every polynomial upper bound is negated with witnessd2. No sharp halving/bisector-line theorem or denial of the compatible lower growth is asserted. Full original bilingual source preserved. No sorry, native_decide or additional axiom. Organizer acceptance is pending.
