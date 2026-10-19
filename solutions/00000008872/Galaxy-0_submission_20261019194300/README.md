# TLMC 00000008872: zero and star defeat completeness

The zero game and star have atomic weight 0 and numerical component 0, yet have distinct normal-play outcomes and are not equivalent. Both satisfy standard all-smallness and the source's stronger immediate-number-options condition.

## Verification scope

The Lean 4.31.0 project models genuine finite short games, Conway comparison, disjunctive sums and canonical Nim heaps. It proves all positive dyadic bounds for the numerical component, stabilization of outcomes against sufficiently large heaps in every finite context, the exact contextual star-plus-heap identity, far-star equivalence to zero, and the counterexample. Atomic weight zero is represented by its standard defining far-star zero fiber; it is not stipulated by a lookup table. The entire general atomic-weight function/theory and the other conjecture clauses are not formalized.

The far-star definition is an eventual outcome equality for every fixed finite context. It does not assert a finite heap has the formal far-star idempotence property. The primary mathematical reference is Larsson–Nowakowski, arXiv:2007.03949v2, Section 5, Definitions 3–5 and Example 6.

## Reproduce

From `lean/`, with Lean 4.31.0 on PATH:

```
lake build
lake env lean -DwarningAsError=true Main.lean
lake env leanchecker Main
```

The final theorem audits are printed by Main.lean. Dependencies are only the standard Lean foundational axioms reported in the logs, not custom axioms. There is no sorry, native_decide, or kernel bypass.

- `solution.tex` / `solution.pdf`: complete mathematical argument and scope.
- `lean/`: portable source-only project; standard library only.
- `verification/`: real execution records and eligibility check.
- `independent-review.md`: separate pre-submission review, not maintainer acceptance.
- `source-conjecture.md`: original bilingual statement.

Compile the report with `bash build-pdf.sh` in a normal TeX Live installation containing Latin Modern and AMS fonts.
