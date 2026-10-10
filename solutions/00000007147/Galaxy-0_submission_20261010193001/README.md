# Counterexample to the face claim in conjecture 00000007147

The two-dimensional associahedron on four letters has 11 nonempty faces, or 12 with the empty face included. The four-leaf full binary trees, which underlie the corresponding Tamari lattice, number only 5. No bijection or face-poset isomorphism is possible. The corrected statement about the five vertices and Tamari order is true and is not disputed.

## Scope and semantic boundary

This is a formal finite **combinatorial** counterexample. The Lean definition of the associahedral face poset is the standard reverse-inclusion poset of pairwise noncrossing diagonal sets in a pentagon, with a separate bottom for the empty polytope face. The zero-diagonal set denotes the whole polytope, not the empty face.

The correspondence between this standard combinatorial model and faces of a geometric associahedron is cited in the report, not proved as a convex-geometric realization theorem in Lean. The report makes this boundary explicit. The Chinese source expressly mentions the face lattice; the submission targets its literal all-face claim. If “faces” were changed to “vertices,” that would be a different, true statement.

## What is kernel-checked

- Actual recursive full ordered binary trees, internal-node and leaf counts, and exhaustive tree enumeration for every node count.
- Every pentagon diagonal, encoded by endpoints, with exhaustive and nonredundant enumeration.
- A bijective bit-mask encoding of all subsets of the five diagonals.
- The strict endpoint-alternation crossing predicate, pairwise compatibility, and exhaustive face enumeration.
- Face counts by codimension `(1,5,5)`, total 11 and full total 12.
- Reverse-inclusion order laws and greatest element of the nonempty face poset.
- A proved finite pigeonhole lemma, then impossibility of an injection from nonempty faces into four-leaf binary trees. This excludes every possible poset isomorphism without presupposing a particular Tamari order implementation.
- Impossibility of maps with a left inverse from either nonempty or full face sets to those trees, plus both explicit count mismatches.

## Reproduce

Lean toolchain: `leanprover/lean4:v4.31.0`, no external dependencies.

    cd lean
    lake build
    lake env lean -DwarningAsError=true Main.lean

The build prints transitive axiom audits. Only `propext`, `Classical.choice` and `Quot.sound` occur. No `sorry`, `admit`, `native_decide`, custom axiom or external computational oracle is used.

From the submission directory:

    python3 reproduce.py
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The Python script uses only its standard library and is an independent, supplementary recomputation. It is not part of Lean's trusted proof.

## Contents

- `report.tex`, `report.pdf`: complete mathematical argument, scope, formal correspondence and references
- `lean/`: pinned self-contained Lean project
- `SOURCE.md`: exact bilingual source and verified source SHA
- `reproduce.py`: exhaustive independent enumeration
- `verification/`: build, axiom and independent-check records

## Eligibility and authorship

On 2026-10-10, current metadata for 00000007147 had both solved flags false. All-state PR searches by the full ID, short ID and “associahedra” returned no match; a Tamari search returned only unrelated conjecture 00000000458. Recheck immediately before publication. The source and metadata identities are recorded in `verification/eligibility.json`.

AI-assisted submission by Galaxy-0. The mathematical correction is classical; no claim of a new general associahedron result is made. Organizer acceptance is pending.
