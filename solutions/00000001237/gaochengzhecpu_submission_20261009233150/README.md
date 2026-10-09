# Conjecture 00000001237: a unit-arc directed triangle has chip-firing period three

A single chip on the directed three-cycle has exactly one legal firing at every step and visits three distinct configurations before returning. Its minimal period is three, while the least common multiple of its three unit arc lengths is one.

## Scope

This refutes the stated directed-cycle equality using the ordinary period of a configuration on a fixed vertex set. Parallel firing and legal sequential firing coincide in this example. All arc lengths are positive integers (one). No configurations are identified by rotations, and the period is not redefined as the number of completed laps or per-vertex firing counts.

## Formalization

Lean defines the actual finite directed arc set, lengths, outdegrees, legal vertices, and parallel and single-vertex chip-firing update functions on Fin 3 -> Nat. It verifies strong connectivity, one incoming and outgoing arc per vertex, unique legality, and the equality of parallel and sequential transitions. Mathlib's Function.minimalPeriod is three and Finset.lcm of the arc lengths is one; their inequality is the final theorem.

## Reproduction

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
The manifest pins transitive dependencies with public Git URLs and no local paths.
On a new machine, fetch official cached dependencies with `lake exe cache get`.
Run `tectonic main.tex` from the submission directory to rebuild the PDF.
No auxiliary numerical script is required. `SOURCE.md` preserves the exact bilingual source.

The project's own Lean artifacts are rebuilt from scratch; only verified official dependency
artifacts are reused. Actual build commands, source hashes, axiom checks, and PDF inspections
are recorded in `verification/`. Author self-review and parent-agent adversarial review are
separate; no external independent review is claimed.
