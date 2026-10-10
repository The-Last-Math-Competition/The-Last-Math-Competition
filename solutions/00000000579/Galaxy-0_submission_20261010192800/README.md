# Conjecture 00000000579 is false

The simple graph C4 gives P_M(t)=1+2t and P_(M*)(t)=1. The difference at t=1 is 2, while the chromatic polynomial has value 14 at -1. Thus no integer multiplier exists. The matroid-characteristic interpretation also has absolute value 14.

## Reproduce

Requires Lean 4.31.0, with only its bundled Std library. There are no Lake package dependencies.

- `lake build`
- `lean Submission/Basic.lean`
- `python3 verify.py` (standard library only)
- `bash build_pdf.sh` (TeX Live or an equivalent installation)

The optional first argument to build_pdf.sh is an existing format directory, for stripped-down TeX images that contain the TeX source tree but lack a searchable format/index. No installation or download is performed.

## Formal content

`Submission/Basic.lean` defines actual C4 edges and finite walks, proves four-step stabilization is equivalent to unbounded finite-walk connectivity, computes graphic rank from connected components, verifies the standard dual-rank formula and both matroid rank axioms, and encodes the defining KL recurrence on all loopless contraction/restriction intervals. Every coefficient degree is covered, including the arbitrary-degree tail through a symbolic theorem.

`graphic_counterexample` applies to any KL recurrence assignments for the actual graphic and dual rank functions. `counterexample_exists` supplies explicit assignments satisfying every recurrence, so the assumptions are nonvacuous. The normalized polynomials, not unused raw family entries, are determined at the witness. `chromatic_coefficients` checks the usual subset inclusion-exclusion polynomial; `chromatic_value` evaluates it at -1.

Main theorem dependencies printed by Lean are only propext, Classical.choice and Quot.sound. There are no added axioms, proof holes, native_decide calls, or external certificates. Python is supplementary, never trusted by Lean.

## Included files

- `report.tex`, `report.pdf`: complete mathematical proof and semantic mapping
- `Submission/Basic.lean`, `Submission.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: self-contained Lean project
- `build.log`: successful clean Lake build and printed axioms
- `verify.py`, `verification.log`: independent exact arithmetic checks
- `build_pdf.sh`, `pdf-build.txt`: PDF reproduction and successful build log
- `conjecture-source.md`, `provenance.md`: exact source statement and eligibility evidence

The main proof is a divisibility counterexample. It does not invent a meaning for the extra spanning-tree deletion-count description, because the weaker integer-divisibility claim already fails.
