# Verification record

## Lean

Environment: Lean 4.33.1, core Lean only; no Mathlib dependency.

Commands run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Both commands completed successfully. The source prints axiom dependencies for the integer-unit lemma, the contradiction at 2, and the conditional witness theorem. Each print lists only Lean's standard `propext`; there are no custom axioms, `sorry`, `native_decide`, or unproved obligations.

Scope: Lean proves that if a hypothetical witness with stretch factor 2 supplies an integer reciprocal for 2, contradiction follows. The `unitBridge` theorem parameter is explicit and is not declared as an axiom. Establishing that an actual pseudo-Anosov map supplies this bridge uses the published algebraic-unit theorem and the rational-algebraic-integer fact cited in the report; neither result nor the mapping-class-group definitions are formalized in Lean.

## PDF

`report.tex` compiled successfully with both the Codex desktop LaTeX compiler and Tectonic. Tectonic used a writable cache under `/private/tmp` because the default user cache is outside the workspace sandbox. The generated PDF is one A4 page. It was rendered with Poppler and visually inspected; text extraction confirmed the verdict, proof, Lean-scope disclosure, and references are present. No clipping, overlap, split bibliography, or unreadable text was observed.
