# Disproof of conjecture 00000003980

Two distinct total propositional proof systems, defined by opposite tags on the same exhaustive truth-table certificates, have identical shortest proof lengths on every tautology. No formula family can separate them superpolynomially in either direction. This refutes the literal universal claim, even if a pair must contain different systems.

## Files

- `report.tex` and `report.pdf`: complete mathematical argument, concrete binary-token implementation, and explicit formalization boundary.
- `lean/Main.lean`: unbounded formula syntax and valuations; exhaustive-table semantics; sound and complete total decoders; token serialization length; minimum proof existence and uniqueness; distinct systems; length-preserving translations; both-direction nonseparation for every formula family.
- `lean/Costs.lean`: recursively metered list lookup, formula and table evaluation, shared-output table generation, and bit-doubling work; correctness and bounds; guard-dependent algorithmic work budget bounded by `13(N+1)^2`.
- `lean/Audit.lean`: transitive axiom audit of every theorem.
- `source.md`: original bilingual problem text.
- `independent.py`: independent token-parser, roundtrip, translation, invalid-input and guard checks. Run with Python 3.
- `verification/`: build, theorem audit, and independent kernel-replay logs.

## Reproduce

Install Lean 4.31.0 using the supplied `lean-toolchain`, then:

    cd lean
    lake build
    lake env lean -DwarningAsError=true Audit.lean
    lake env leanchecker Main
    lake env leanchecker Costs

No external Lean packages are needed. Only `Std` is imported. Every theorem uses at most `propext`, `Classical.choice`, and `Quot.sound`; no admissions, custom axioms or native-decide calls occur.

Build the report using `bash build_pdf.sh` with a regular TeX installation. The optional argument names a directory containing a prebuilt `pdflatex.fmt` for minimal images.

## Exact verification scope

The logical counterexample, genuine unbounded definitions, checking semantics, completeness and shortest-proof comparisons are kernel verified. The polynomial-time admissibility of the concrete algorithms is proved mathematically in the report, aided by kernel-verified recursive work bounds. Parsing correctness, serialization injectivity, four-bit conversion and bit/Turing implementation costs are not formalized as machine-execution theorems. The displayed quadratic budget bound is not an exact compiler runtime claim. This boundary is stated prominently in the report.

The Lean semantic-system record deliberately does not assert polynomial time. Refuting its universal assertion alone would not refute the original narrower domain. The original problem is refuted using the specific constructed systems plus the report's explicit polynomial-time implementation proof.

This is a prepared submission, not an official acceptance or a published pull request.
