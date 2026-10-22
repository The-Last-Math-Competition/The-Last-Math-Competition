# Verification

The frozen source passed a new root build in a separate Lean 4.33.0 project. Every dependency Git commit in the task-owned public bank matches the manifest pin. Main was newly compiled from this package source.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0, all 17 named targets (13 theorems, three definitions and Star abbreviation); only propext, Classical.choice, Quot.sound, or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 200.8474 diagnostic WSL seconds. Official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually checked by worker and supervising AI; no overfull boxes.
- Full proof, exact source scope, report and PDF independently reviewed by a separate supervising Codex agent.

Main SHA256: `00013d4d12f45c66159de9d2b7e3c0740c432eaa3bdbc7d428c4f679c0a03c88`. Structured receipts bind source, commands, exits and logs. One bounded owned process group at a time, CPU affinity 0,2. This exposed selective production case is not an extra experimental sample.

Every actual finite star is a genuine tree. For arbitrary candidate graph growth functions, Mathlib IsBigO polynomial upper growth is proved equivalent to an explicit eventual envelope with real constants and natural cutoffs. The weak numerical super-polynomial predicate requires arbitrarily late violations of every polynomial bound, and for nonnegative functions is proved equivalent to absence of polynomial upper growth. The same constant, degree and cutoff close the contradiction. Theorems cover arbitrary finite star orders, all finite labelled graph assignments and natural-valued candidates. No growth value is assigned, and no actual configuration-space fundamental group or its growth is computed. No claim that tree motion groups are trivial is used. The original source's two growth clauses cannot both hold for any consistent actual assignment. Prior PR293's idea is attributed and its rejected bare-arithmetic gap is repaired; no separate corrected conjecture or sub-exponential classification is claimed. Original bilingual source preserved. No sorry, native_decide or extra axiom. Organizer acceptance pending.
