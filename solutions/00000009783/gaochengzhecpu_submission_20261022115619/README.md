# Disproof of conjecture 00000009783

The actual AF algebra C has only the closed ideals zero and C. Its
unique maximal ideal chain has one strict inclusion or two elements.
The standard constant identity system C=M_1(C) at every stage has a
Bratteli ray, with one vertex per level and one edge between neighboring
levels. There is a genuine path of length N for every natural N, so
the supremum of depths is infinite. This contradicts the source's
chain-depth equality under both chain-length conventions.

## Semantic scope

Both source languages explicitly make the chain-depth claim. AF has
its standard definition, which includes finite-dimensional algebras
via constant identity systems. Path depth means ordinary directed-path
length; counting vertices instead of edges preserves unboundedness.
No hereditary-subset/saturation convention or separate dimension-vector
stratification claim is used in this counterexample.

Blackadar's author-hosted Classification of C*-Algebras, sections
I.3.2.7-8, gives the standard partial-multiplicity definition of the
diagram. This paper builds the constant matrix-block system directly.

## Formalization

Lean uses Mathlib Complex with CommCStarAlgebra. ApproximatelyFinite
requires actual closed finite-dimensional StarSubalgebra stages,
monotonicity, and a dense union. The whole-algebra constant sequence
meets these requirements. Each actual stage is star-algebra equivalent
to M_1(C); the connecting StarAlgHom becomes the matrix identity.

The constant system has its universal direct-limit property for every
CStarAlgebra target and unital cocone, and also for every nonunital
CStarAlgebra target and nonunital cocone. Continuity is proved from
finite dimensionality. The diagram is an actual Quiver with Fin arrow
types, using multiplicity one computed from the identity's range.
Actual Quiver.Path objects have all finite lengths and their ENat
supremum is top.

ClosedIdeal is the subtype of actual Ideal objects with topologically
closed carriers. Lean proves it has two elements, proves every
IsMaxChain is all of it, and computes strict-inclusion chain supremum
one and element-count supremum two.

OneBlockDepthClause universally quantifies AF commutative CStarAlgebra
objects star-algebra isomorphic to C, which have the same constant
one-block presentation. The main theorem conjecture_9783_false negates
this necessary restriction of the source's universal claim. The element
convention is separately refuted. No general AF classification or
hereditary-ideal correspondence is claimed formalized.

## Reproduction and review

With Lean 4.19.0 and the public-Git pinned dependencies available:

```text
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Compile main.tex with Tectonic or a compatible LaTeX engine. Mathlib is
pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.

Author strict Lean passes with warnings treated as errors. Axiom reports
contain only propext, Classical.choice and Quot.sound. Fresh build,
native compiler and PDF review are coordinator-owned checks recorded
separately before publication. No sorry/admit/native_decide/custom
axiom/opaque declaration is used.

Developed by a delegated AI agent with a self-review; the coordinating
agent reviews it separately. No external independent review is claimed.
The source snapshot records no prior PR or solution; the coordinator
rechecks before publication.
