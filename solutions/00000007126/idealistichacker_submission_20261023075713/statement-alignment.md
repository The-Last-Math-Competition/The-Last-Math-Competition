# Statement Alignment: 00000007126

The exact original English and Chinese are in `source.md`. They concern
barycentric subdivision of polytopes, its flag property, and invariants from
original-face chain counting. They do not define a particular invariant or
assert that numeric counts completely classify the subdivision.

## Explicit Standard Combinatorial Reading

The domain is nonempty bounded convex polytopes. The combinatorial barycentric
subdivision is the order complex of the actual nonempty face poset, ordered by
inclusion. Full subdivision includes the whole polytope as a face; boundary
subdivision excludes it. Neither includes an empty face as a vertex. Both
conventions are covered rather than silently choosing one. This standard
incidence definition applies to nonsimplicial polyhedral complexes too; the
report gives actual primary references and does not rely on a software name
alone to justify the interpretation.

The enumerative invariant here is the f-vector under combinatorial isomorphism.
It is not a complete classifier, an original-polytope reconstruction algorithm
or a quantity preserved by performing subdivision. The complete chain-incidence
family describes the entire abstract complex, a richer object than its counts.

## Actual Definition Bridges

| Source concept | Actual Lean construction or proved bridge |
| --- | --- |
| Finite strict face chains | Finite totally ordered subsets; local `FiniteChain` is proved equivalent to Mathlib `IsChain` |
| Abstract subdivision | Actual `AbstractSimplicialComplex` with nonempty-chain faces and proved closure/singletons |
| One-skeleton | Actual simple comparability graph; two-element faces are exactly its edges |
| Flag property | Every nonempty finite clique is proved to be an actual face |
| Chain count | `chainFaceEquiv` is an actual face/chain equivalence, not an assumed formula |
| d-dimensional f-vector | Actual faces of cardinality d+1, explicitly connected to chains of d+1 elements |
| Actual original faces | `SetFacePoset` is the subtype of a finite family of actual `Set E` subsets, with inherited inclusion |
| Full versus boundary | Empty-set filter; `properFaceFamily` additionally removes the specified whole face; both flag/count theorems proved |
| Isomorphism invariance | `faceTransport` and inverse under actual order isomorphism; face-count/f-vector equality follows |

Chains have distinct elements, may skip face ranks and are not required to be
saturated. Length counts elements, not inequalities. No ordered-sequence
enumeration theorem or global linear order on the face poset is advertised.

## Scope Boundary

The Lean theorem is universal over actual finite families of subsets, a domain
more general than polytope face families. It does not assume those arbitrary
families are polytopal, or assume a deep closure/flag/count conclusion. Actual
bounded-polytope faces supply a special input under the disclosed standard
combinatorial definition. The correspondence and finiteness of the actual face
family are explained in the paper; the code does not define a separate geometric
Polytope type or advertise a formal geometric-face finiteness theorem.

No barycenter coordinates, affine-independence, geometric gluing or coverage
theorem is claimed to be implemented. Such a stronger geometric theorem would
need further correspondence proofs. The separate finite-original-vertex-set
helper is not used as an unproved vertex-set encoding of geometric faces.

All original conjecture files and organizer metadata remain untouched. Core
preflights and mathematical literature are not final frozen-package approval;
the exact full package/PDF/reproduction is independently reviewed before release.
