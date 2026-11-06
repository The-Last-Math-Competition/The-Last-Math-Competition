# Independent cross-review of 2440

**Verdict: PASS for the actual topological universal obstruction and the stated mathematical application to the standard étale homotopy pro-group. No defect requiring a frozen-source change was found.** The final paper must retain the explicit boundary: schemes, the étale homotopy-type construction, geometric realization, and their functorial comparison are not constructed in the supplied Lean file. It must not call the supplied result a complete Lean construction of étale homotopy theory.

Reviewer: the graph agent, separate from the 2440 author. No subagent was used. Only this cross-review file was written; frozen files were not modified.

## Materials and integrity

Read all 170 lines of `round5/drafts/00000002440/lean/Main.lean`, the exact bilingual source `round5/source/00000002440.md`, `round14/quantum/2440-status.json`, the complete subsequently available `2440-proof-and-review.md`, `check2440.py`, and the actual strict log. Also read the relevant original pinned Mathlib implementation, including `auxGroup`, `auxGroup_indep`, `mul_spec`, and `commGroup` in `Mathlib/Topology/Homotopy/HomotopyGroup.lean`.

Independently recomputed Main SHA256 is `40a0bf4691e533896eb1e47a13ac87e014738c87b3ba8f4b38372da105397736`, exactly the frozen value. The exact-source hash also matches the status record. The recorded strict and full-build exit codes are zero. The actual strict log contains eight axiom reports, each consisting only of `propext`, `Classical.choice`, and `Quot.sound`, and ends with exit zero. This review did not repeat the parent's independent fresh-build step.

## 1. Actual triple loops versus an assumed CommGroup

**PASS; not circular.** `BasedSpace` contains only a carrier, actual topology, and base point. It supplies no algebraic structure. `Pi3` is the actual Mathlib `HomotopyGroup.Pi 3`, and `CubeLoop3` is the actual `GenLoop (Fin 3)` type of based cube maps.

The proof does not merely postulate an unspecified commutative group and give it the name π₃. `actual_cube_interchange` applies the checked coordinate-concatenation interchange theorem to distinct coordinates 0 and 1. The two unitality theorems concern multiplication on the actual homotopy classes; there is no erroneous claim that concatenation with a constant loop is strictly an identity on parametrized maps before quotienting.

Although `actual_pi3_comm` is syntactically `mul_comm`, its CommGroup instance is derived, not a hypothesis. I checked its provenance in the pinned library. The implementation of `HomotopyGroup.commGroup` explicitly invokes `EckmannHilton.commGroup`, using the actual common constant-loop unit and actual coordinatewise `transAt_distrib` interchange identity after applying the genuine homotopy quotient. `auxGroup_indep` uses the same checked interchange argument. No axiom of higher-group commutativity is imported.

`actual_loops_commute_up_to_based_homotopy` also bridges the result back to the actual cube-loop representatives. Mathlib's `mul_spec` reverses the order of the named representatives relative to its group multiplication convention; the author's deliberate choices p=b,q=a and p=a,q=b handle that reversal correctly. Equality of the actual quotient classes is converted by `Quotient.exact` into the genuine based homotopy relation. This is stronger evidence than an unconnected abstract group computation.

## 2. The whole diagram, not just the inverse limit

**PASS.** Every object of `ThirdHomotopyDiagram` is the actual π₃ of a supplied actual pointed space. The input maps are group homomorphisms obeying identity and composition, with no commutativity field. Allowing arbitrary such homomorphisms is a strengthening: homomorphisms induced by pointed transition maps are included. It does not assume that an arbitrary group is a homotopy group.

`groupDiagram` is an actual functor to `Grp`. `abelianDiagram` has exactly the same actual carriers and maps but is an actual functor to `CommGrp`; its object structures come from the derived actual π₃ instances. `abelian_factorization` is an explicit natural isomorphism after forgetting commutativity, with identity underlying maps, actual inverses, and naturality proved. Thus the entire diagram has an abelian-valued representative. It is not inferred from a property of an inverse limit.

For a cofiltered index category, this diagram-level factorization gives the desired representative in the pro-category of abelian groups. The Lean source does not instantiate a `Pro` construction or export a theorem in a formal pro-category; passing from the displayed cofiltered functors and natural isomorphism to their pro-objects is a mathematical categorical interpretation, explicitly outside the encoded geometry. The concrete factorization itself is fully checked.

An essential scope caution is already correctly stated in the author's completed review: a pro-abelian object may have some other pro-isomorphic presentation with nonabelian stages. Therefore the existence of a nonabelian group at a stage of an arbitrary presentation is not an intrinsic nonabelianity criterion. `no_nonabelian_layer` applies to the supplied presentation by actual π₃ groups. The required intrinsic conclusion follows from the existence of the abelian-valued representative, not from an invalid claim about every possible presentation.

## 3. Étale homotopy/shape bridge and the original source

The exact source asks for noncommutativity of the internal group π₃^ét itself, alongside finite π₁^ét and a proposed Enriques-type construction. It does not ask for a nontrivial π₁-action on π₃, a nonabelian semidirect product involving π₁, or a noncommutative operation in a higher categorical model. Those would be different assertions. Higher homotopy groups may have nontrivial monodromy actions while remaining internally abelian.

I independently opened the primary reference [Mohammed Moutand, *On schemes with trivial higher étale homotopy groups*, arXiv:2312.08505v2](https://arxiv.org/html/2312.08505v2#S2.SS1), section 2.1. It gives the Artin–Mazur–Friedlander étale homotopy type in the pro-homotopy category of simplicial sets and defines the pointed étale homotopy pro-groups by applying homotopy groups. Smooth varieties fall within the locally noetherian setting in this construction.

For the mathematical application, take pointed simplicial representatives of its levels and their geometric realizations. The usual simplicial/topological homotopy-group comparison identifies each third group with the actual π₃ of an actual pointed space. The induced maps on homotopy groups are genuine group homomorphisms with exact functorial identity/composition laws, even though the underlying representatives originated in a homotopy category. Hence they satisfy the more general diagram interface used by the Lean theorem. Every such level is abelian, giving the pro-abelian representative.

The geometric realization comparison, induced-map construction, and scheme-to-pro-space construction are mathematical bridges, not supplied Lean theorems. The author explicitly acknowledges all three. I found no substitution of an arbitrary assumed CommGroup for an étale definition. Nevertheless the final write-up must preserve this distinction: the universal topological and diagram obstruction is formalized; the application to the standard étale construction is explained mathematically. The code does not claim a theorem quantifying over a formal `Scheme` type or a formal `Et` functor.

No special assumption on π₁ is used in the obstruction. This is appropriate: internal commutativity of π₃ is universal, so adding finite π₁, smoothness, or a particular surface construction cannot supply the requested witness. No numerical calculation of an Enriques surface's homotopy groups is required.

## 4. Quotients, inverse limits, and completion range

**PASS in the stated range.** `every_quotient_image_comm` assumes only a Group on its target, plus an actual surjective homomorphism from an actual π₃. Its proof pulls both target elements back and transports the actual source commutativity. Target commutativity is not assumed. The normal-subgroup quotient theorem uses an actual Mathlib quotient map and its actual surjectivity. Finite quotients are special cases.

`compatibleSubgroup` is the genuine subgroup of the dependent product cut out by every transition compatibility equation. Closure under identity, multiplication, and inverse is proved using the actual transition homomorphisms. This is the standard concrete underlying-group inverse limit. Proving its universal property is unnecessary for the asserted commutativity, although the file does not formalize that universal-property identification.

Both inverse-limit commutativity proofs work pointwise on actual compatible tuples. The quotient-limit theorem requires each target layer to be an actual surjective image of an actual π₃. It correctly does not need the chosen surjections themselves to form a natural transformation: each target layer being abelian already suffices for any group-valued transition diagram between them.

Consequently the supplied results cover finite quotient diagrams and the underlying groups of their profinite limits. They do not formalize topologies on the inverse-limit group, the universal property of profinite completion, arbitrary quotients in a formal pro-category, or a comparison formula between completion of a space and completion of its individual homotopy groups. Such formulas should not be asserted as Lean results. In particular the argument does not need, and must not infer, a generally false unrestricted identity π₃(holim Yᵢ)=lim π₃(Yᵢ). The main pro-abelian conclusion is already established at the diagram level.

## Recommendation

Proceed to the parent's independent fresh verification and paper/PDF stage. Keep the proof centered on actual higher-loop Eckmann–Hilton commutativity and the full diagram factorization. Treat quotient and inverse-limit conclusions as supplementary preservation results. Retain the explicit external étale/geometric-realization/pro-category interpretation boundary. No frozen source change is requested by this review.
