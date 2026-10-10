# Independent review: conjecture 00000007147

Review completed 2026-10-10 UTC. Result: PASS for the explicitly scoped combinatorial counterexample.

## Checks performed

- Retrieved the exact bilingual conjecture from its GitHub source. The English parenthetical and Chinese text explicitly refer to the face lattice. The submission accurately distinguishes this literal reading from the standard true statement about vertices.
- Read every definition and proof in `lean/Main.lean` independently. The trees are actual recursively defined ordered full binary trees, not an assumed five-element placeholder. Exhaustive membership is proved for every internal-node count, and the internal-node/leaf relationship is proved.
- Verified the diagonal model uses all five genuine pentagon diagonals, with an exhaustive/injective endpoint enumeration. Strict alternating endpoints correctly encode crossing; shared endpoints do not count as crossing. Bit masks represent every subset without duplication.
- Verified that reverse inclusion, the whole-face zero mask, and the separately adjoined empty polytope face have the correct semantics. There are no dropped compatibility or exhaustiveness conditions.
- Independently ran Lean 4.31.0 with `-DwarningAsError=true` on the submitted `Main.lean`: exit 0.
- Independently ran `lake build`: success. Ran `reproduce.py`: success, with 11 nonempty faces, 12 full faces, 10 proper nonempty faces, and 5 four-leaf binary trees.
- Inspected the printed transitive axiom audits. Their union is exactly `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `implemented_by`, or `unsafe` declaration.
- The no-injection result is obtained from a proved finite-list pigeonhole argument. No enumeration of all maps and no untrusted external oracle is used. Defining the Tamari relation is unnecessary because the obstruction already holds for its underlying set, irrespective of order.
- Read the report source and extracted final PDF text. Inspected both rendered PDF pages visually: legible, no clipping or overlaps, citations and equations readable. Bibliographic title and exact conjecture link corrections are present.

## Scope and formalization boundary

The Lean proof concerns the standard combinatorial associahedron face model, the reverse-inclusion poset of noncrossing pentagon diagonal sets. It does not construct a convex geometric polytope or kernel-prove a geometric realization theorem. The cited identification with geometric associahedron faces is a mathematical semantic bridge, explicitly disclosed in the report and README. This is an acceptable boundary for the stated combinatorial counterexample; it must not be described as a fully formalized convex-geometric realization argument.

The informal source admits a possible intended vertex-only interpretation. This review validates the submitted refutation of its literal face-lattice reading, not a refutation of the corrected vertex statement. Organizer acceptance is not established by this review. Eligibility metadata and publication status were outside this independent mathematical review.

## Reviewed SHA-256 digests

- `lean/Main.lean`: `abb4e70ce50fea0558aa4b1a4a065fa094d5fa400a82dcb7212e35666e60231e`
- `report.tex`: `fd2f5d75fb2c88a22c4a835c27b96a99e1e57329325e0a8f3bf49f66841d2677`
- `report.pdf`: `09914973b91854e907a52422c8ebf12e5d89f4cb72fe86980e0b7b50f021ecf3`
