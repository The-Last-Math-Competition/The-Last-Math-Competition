# Disproof of Conjecture 00000002440

Actual third homotopy groups are abelian by the cube-loop Eckmann-Hilton argument. The entire defining diagram of an etale third homotopy pro-group therefore has an abelian-valued representative, excluding the proposed internally nonabelian group for any smooth variety.

## Scope

Refutes the requested internal noncommutativity universally, independent of finite pi1 or any Enriques-type construction. The standard etale homotopy-type, realization and homotopy-functor constructions are stated mathematical bridges outside Lean. The pro-group conclusion concerns an abelian-valued representative, not every arbitrary pro-isomorphic presentation. Nontrivial pi1 actions are separate from internal noncommutativity.

## Formalization

Lean uses actual Mathlib relative-boundary cube-loop homotopy groups of arbitrary actual pointed topological spaces, without a supplied group or commutativity hypothesis. It exposes genuine coordinate interchange and unit laws, and proves reversed concatenations are homotopic relative to the boundary. For any category-indexed diagram of those actual pi3 groups it constructs a CommGrp-valued diagram and a natural isomorphism of its forgetful image with the entire group diagram. This levelwise factorization, before inverse limits, supplies the universal obstruction. Additional theorems prove commutativity of actual surjective quotient images and normal quotients, and of genuine compatible-tuple inverse limits, covering profinite conventions. Moutand arXiv2312.08505v2 section2.1 supplies the standard definition of etale homotopy pro-groups; schemes, the etale functor, realization comparison and induced-map functor are not claimed formalized.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
