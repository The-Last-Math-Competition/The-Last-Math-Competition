# TLMC 00000004993: arithmetic inconsistency of the printed conjunction

The original statement says all attainable third Betti numbers are odd and the minimum attainable value is 1186. These two clauses are inconsistent for every set of natural numbers. The submission does not assume or construct a Spin(7) example, classify actual Betti numbers, or disprove any corrected statement.

## Reproduce

Use Lean 4.31.0 with its bundled `Std` library; there are no external dependencies. With the pinned toolchain on PATH, run `./verify.sh` from a source-only clean directory. It runs a Lake build, warnings-as-errors source compilation with `--trust=0`, prints all 10 named theorem axiom dependencies, and independently replays the compiled module with official `leanchecker`.

For the report, run `pdflatex -interaction=nonstopmode -halt-on-error solution.tex` twice in a complete TeX Live installation with AMS, geometry, Latin Modern and hyperref. The submitted PDF has two pages, both rendered and visually inspected. The author's minimal cloud TeX search paths required explicit local cache/font configuration; no system installation or security settings were changed.

## Formal contract

`IsOdd n` means `exists k : Nat, n = 2*k + 1`. `IsMinimum A m` includes both `A m` and the lower-bound condition. `TLMC4993.disproof` is universal over every predicate `A : Nat -> Prop`, so applies conservatively to the actual geometric attainability predicate, whatever it is. `geometric_form_impossible` also models attainability directly from an arbitrary object type, admissibility predicate and invariant maps.

Ten named theorems were audited. Only standard `propext` and `Quot.sound` occur; no extra/custom axioms, `sorry`, `native_decide`, or kernel bypass are used. Independent review is AI-assisted, not human or organizer acceptance. No new geometric discovery or accepted competition score is claimed.

Original bilingual source is in `original-statement.md`. `solution.tex` gives the complete mathematical argument and scope. Verification records are under `verification/`. Eligibility must be checked again immediately before publication; the saved earlier check is not a permanent guarantee.
