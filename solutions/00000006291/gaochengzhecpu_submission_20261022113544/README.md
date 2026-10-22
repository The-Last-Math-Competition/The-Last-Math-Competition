# Disproof of conjecture 00000006291

The fields F₂ and F₃ are nonisomorphic von Neumann regular rings, yet both
scaled ordered Grothendieck groups are (Z, Z≥0, 1). This refutes the source's
claim that the zeroth group is a complete invariant of regular rings.
The positive cone and order unit are retained, so the example also works
when the proposed invariant is stronger than the abstract abelian group.

`SOURCE.md` is the exact bilingual source at upstream commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`. The current snapshot has no prior
PR or solution for this conjecture.

## Mathematical and formal scope

The Lean construction uses actual bundled finite-dimensional vector spaces
and linear equivalences between cross direct sums. It proves equality with
the stabilized relation allowing any common auxiliary module, constructs the
Grothendieck quotient, proves the dimension map bijective, verifies the group
operations on representatives, and proves the universal group-completion
property. It identifies the positive cone and compatible order, and identifies
the unit with the class of the field as its own module. It also proves the
finite-generation/projectivity and standard-basis bridges, not merely a
numerical assertion about ranks.

The theorem `Conjecture6291.fields_same_scaled_ordered_K0` constructs an
order-preserving additive isomorphism preserving the unit for every pair of
fields. `Conjecture6291.finite_fields_witness` packages regularity, the invariant
isomorphism, and absence of a ring isomorphism for F₂ and F₃.

The final theorem is:

```lean
theorem conjecture_6291_false : ¬ FieldCompleteness
```

Here `FieldCompleteness` quantifies over all pairs of fields, with regularity
and an isomorphism of scaled ordered K₀ groups as hypotheses and an actual
ring isomorphism as conclusion. This is a necessary restriction of the source's
general complete-invariant assertion. Lean does not construct K₀ for every
regular ring. The exact-sequence presentation of K₀ agrees with the direct-sum
presentation because projective exact sequences split; that presentation
equivalence is explained on paper rather than formalized. The source's other,
unspecified continuous-geometry clauses are not needed for the disproof.

No common coefficient field or special subclass of regular rings is assumed
in the source. A theorem imposing such additional hypotheses is outside the
claim refuted here.

## Reproduction and review

Use Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, as pinned by the public Git metadata.
In `lean/`, run:

```text
lake env lean -DwarningAsError=true Main.lean
lake build
```

Compile `main.tex` with Tectonic or another compatible LaTeX engine.
The author strict Lean check passes; the audited main/bridge theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. Review mode: agent development with parent adversarial
review; no external independent review. The coordinator performs the fresh
project build and PDF inspection before deciding whether to publish.
