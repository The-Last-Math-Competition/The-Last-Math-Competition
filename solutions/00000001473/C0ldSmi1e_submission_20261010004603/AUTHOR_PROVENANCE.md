# Provenance and formalization scope

## Author boundary and permitted inputs

This author was assigned only conjecture 00000001473 and was not supplied a proposed witness, proof, solution route, or inherited mathematical helper. The counterexample and the mathematical/Lean development in this delivery were produced after reading the isolated original input bundle. The author did not read other conjectures, repository solutions, other agent outputs, selector files, task histories, pull requests, or external solutions. No external search was used. No subagent was spawned. The only source-code/library material inspected outside the two scratch workspaces was stock Lean/Mathlib dependency material used for ordinary proof development and revision verification.

The input bundle was `/private/tmp/tlmc1473-author-input`. Both English and Chinese statements occur in `conjectures/00000001473.md`. Both supplied rule files were read in full. The supplied SHA256 manifest was checked against these values:

| Input | SHA-256 |
| --- | --- |
| `SHA256SUMS.json` | `0f534b95af895ffe575cd78cad6407938bd5f8b4bae83100f6729a623e097c4d` |
| `conjectures/00000001473.md` | `bdceacf9b92330afb3ee49161d60a121e65ad4724d70bf332b76f7c843ba89d5` |
| `RULES.en.md` | `200d9a783c08a5edfd1b508e6942b3b851a63c726506291f6de6a59773f1163a` |
| `RULES.zh-CN.md` | `7c5b49bb84403feea1eb14d23d48491400c7749d58db345cd317231949a9e82b` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lake-manifest.json` | `56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637` |

`original-input/` preserves the complete bundle byte for byte. `input-verification.json` records an automated recheck. The Lean project copies the supplied toolchain and Lake manifest exactly; neither was regenerated or weakened.

All authored work was confined to `/private/tmp/tlmc1473-proof` and `/private/tmp/tlmc1473-author`. No repository content was edited, no pull request was created, and no external message was sent. The parent task handles eligibility research, report/PDF production, independent review, and any publication. Their outcomes are not certified here.

## Independent construction

The construction takes an integer first coordinate constrained by `2x >= 1` and propagates it by two equalities with multiplier 10. Its derivation did not use optimization-specific literature or an externally supplied example. The resulting gap is 50 in three coordinates. An explicit surplus coordinate gives equality standard form with four nonnegative coordinates and the same gap. The complete mathematics, all data, optima, and exact norm calculations are in `ARGUMENT.md`.

## Formalization coverage and limits

The formalization is of finite pure integer **linear** optimization. Every decision coordinate is integral in the integer problem, all finite inputs are integral, and the relaxation uses the very same rows and bounds over real coordinates. The finite feasible-row lists can contain equalities and inequalities; each domain has optional finite lower and upper bounds. Both objective coefficients and the objective constant are part of the data-magnitude calculation.

The four specified forms have either three or four decision coordinates. The feasible sets are unbounded rays with attained unique minima; “finite” here refers to finitely many coordinates and rows. There are no assumed upper bounds, and no omitted large finite bounds. The first three forms include unrestricted and nonnegative domains, and the fourth is equality-only nonnegative standard form. All four have separate formal certificates. The supplied source imposes no compactness requirement.

The formal optimum predicates quantify over every feasible point, not merely candidate points. No ties or arbitrary choices of optima are used. The relaxation optimum satisfies the standard extreme-point definition. The infinity norm is the existing Mathlib norm on `Fin n -> Real`, with its standard coordinate supremum interpretation. It is not a bespoke substitute distance. All finite input values enter the Delta definition. No determinant parameter is substituted for Delta.

The end result is the negation of the source's explicit universal upper bound. A restricted version requiring uniqueness and a relaxation vertex is also negated. The source is a conjunction with a separate sharpness assertion; `not_source_conjunction` uses the failure of its upper-bound conjunct. This delivery does not independently formalize or disprove every reading of the sharpness wording or any claim about a named literature constant. It does not claim that all encodings preserve the same parameters or distances. It checks four identified forms, with their own complete data and dimensions.

The only parameter to `not_source_conjunction` is an arbitrary proposition representing the separate sharpness clause. No truth of that proposition is assumed. The final upper-bound negation theorems themselves have no mathematical hypothesis.

## Stock library and toolchain

The executable directory was `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`. Actual version output is:

- `Lean (version 4.19.0, arm64-apple-darwin23.6.0, commit 6caaee842e94, Release)`
- `Lake version 5.0.0-6caaee8 (Lean version 4.19.0)`

Thus the Lean pin is 4.19.0; the bundled Lake executable self-reports version 5.0.0. This records the actual output rather than assuming the same numbering for Lean and Lake.

The stock Mathlib checkout was `/private/tmp/tlmc-standard-library-419/mathlib`, at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every package revision in the original manifest was separately verified, and `git diff --quiet HEAD --` succeeded in every package checkout. These results are preserved in `final-validation/verified-pins.json` and `final-validation/commands.json`. The local project used symlinks to those unmodified dependencies and their existing compiled stock library cache. A fresh local build means the authored project's `.lake/build` was removed and regenerated; it does not mean rebuilding all of Mathlib from source.

Direct imports are:

- `Mathlib.Analysis.Normed.Group.Constructions`: the finite product norm, `pi_norm_le_iff_of_nonneg`, and `norm_le_pi_norm`.
- `Mathlib.Data.Matrix.Notation`: finite-coordinate vector notation; underlying finite vector evaluation lemmas and `Fin.sum_univ_succ`.
- `Mathlib.Tactic`: proof-producing simplification, finite case analysis, linear/polynomial arithmetic, casts, integer arithmetic, and literal arithmetic tactics.

The proof uses `linarith`, `nlinarith`, `norm_num`, `omega`, `exact_mod_cast`, `fin_cases`, `simp`, extensionality, and ordinary order facts. The small input-maximum equalities use kernel-checked `decide`. There is no `sorry`, `admit`, `native_decide`, custom axiom, external optimization oracle, or opaque mathematical premise in the delivered proof.

## Preserved development and validation

`logs/` contains command records, complete returned diagnostics, and snapshots of every authored Lean file at each validation attempt. The snapshots are JSON data, including failed earlier versions; the active delivered Lean files are only the current `Proximity.lean`, `Audit.lean`, and `lakefile.lean`. The log filenames have gaps because the recorder counts both record and source-snapshot JSON files. Gaps do not represent deleted runs.

Recorded development outcomes are:

| Run | Outcome |
| --- | --- |
| 001 | Failed because the cache lacked the umbrella `Mathlib.olean`; changed to three available stock imports. |
| 003 | Failed on noncomputable real division and a conjunction pattern in the first feasible-set proof. |
| 005 | Feasible-set definitions, all four equivalences, and objectives passed. |
| 007 | Failed on simplification of literal vector coordinates 2 and 3 and matching norm lower bounds. |
| 009 | Complete four certificates and final negation theorems passed. |
| 011 | Added slack-map development failed on matching `1/2` against simplified `2⁻¹`. |
| 013 | Complete source including explicit equivalence maps passed. |
| 015 | Initial full Lake build passed. |
| 017 | Supplementary exact rational audit passed. |
| 019 | Complete final fresh-build validation, all source replays, theorem/axiom printout, and exact audit passed. |

Earlier read-only discovery commands and one missing-file lookup failure are recorded separately in `early-command-record.json`. That small record is reconstructed from the tool transcript; the build and proof diagnostics in `logs/` and `final-validation/` were captured directly by the command recorder.

The final validator first verified the original input pin files and all dependency revisions/cleanliness, then removed only the local authored build directory. `lake build` succeeded with warning-as-error configuration. `Audit.lean`, `Proximity.lean`, and `lakefile.lean` were each then replayed explicitly with `-DwarningAsError=true`, all exit 0. `Audit.lean` printed actual definition and theorem types and dependency lists. Its exact output is `final-validation/22.log`.

Every one of the four certificates and each final negation/conjunction theorem reports exactly the standard dependencies `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or additional axiom is present. The stock norm facts and normal real-number reasoning account for these standard Lean/Mathlib dependencies.

The supplementary `exact_audit.py` is self-contained standard-library Python, uses `fractions.Fraction`, and was executed successfully. It checks exact data magnitude, constraints and domains at the displayed optima, objectives, coordinate distances, and active linear systems. Global optimality and uniqueness are supplied by the Lean proof and the mathematical argument, not inferred from the script's finite point checks. `validate.py` is the reusable fresh-build driver. `run.py` in the author folder is the development recorder; its absolute scratch paths are intentional historical metadata, not a dependency of the Lean project.

The final freeze manifest covers every delivered source, supporting script, argument, provenance record, input copy, and validation log. Generated `.lake` build files, cached stock dependencies, and Python bytecode caches are not delivered mathematical sources and are excluded. The freeze manifest excludes only itself to avoid a self-hash. Its own SHA-256 is communicated separately. No authored files are edited after that freeze.
