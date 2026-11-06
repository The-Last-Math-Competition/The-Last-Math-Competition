# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, 2566 jobs, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, twenty-one transitive axiom audits; only propext, Classical.choice, Quot.sound.
- `lake env leanchecker --fresh Main`: exit 0, 385.7705 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI agent; no overfull boxes.
- Full formal chain, report and source scope independently reviewed by a separate supervising Codex agent.

Main SHA256: `3d139687f66adbe064ff0070627a11a8e1931d9e7d42d33a548e2f075a6f3621`. Structured receipts bind source, commands, exit codes and logs. The production runner uses the same bounded isolated process-group helper as the completed experiment; one heavy process at a time. This selective production case is not an additional experimental sample.

The proof uses actual EuclideanSpace real Fin2 and the literal printed map with constant second coordinate b. All positive iterates, actual omegaLimit sets of arbitrary initial sets, and the closure of the union of all actual singleton omegaLimits lie in a closed horizontal line. A genuine real-line isometry proves its Hausdorff dimension1. Every actual fully invariant compact set also lies there. Finite dimension and real toReal bounds are proved before the source real1.26 lower bound is negated. The usual map with b*x and independent Kaplan-Yorke or box-dimension claims are not treated. No sorry, native_decide or additional axiom is used. Organizer acceptance is pending.
