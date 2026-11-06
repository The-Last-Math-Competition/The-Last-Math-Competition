# Author-agent adversarial self-review: 00000002440

Verdict: PASS

# 2440: third etale homotopy groups cannot be nonabelian

Status: the formal core is complete and frozen for parent review. Recorded strict check exit 0 (14.047 seconds), full Lake build exit 0 (15.547 seconds). No TeX, PDF or PR is created by this agent.

## Exact source and mathematical result

`round5/source/00000002440.md`, SHA256 `03d57359934ae095fec66337cd08932ae4bebe74291fabb2232fa60d0641f923`, asserts the existence of a smooth variety X with finite pi_1^et(X) but nonabelian pi_3^et(X), with an Enriques-type construction. Both languages explicitly require noncommutativity of the third homotopy group itself.

For every pointed topological space (Y,y), the actual third homotopy group pi_3(Y,y) is abelian. Therefore the standard etale third homotopy pro-group is represented levelwise by abelian groups; it is a pro-abelian group. Neither smoothness, finiteness of pi_1, nor the proposed construction can change this obstruction. A nontrivial action of pi_1 on a higher homotopy group does not make the higher group's internal multiplication noncommutative.

## Genuine higher homotopy structure in Lean

`BasedSpace` contains only an actual carrier, a topology and a base point. It has no group data or commutativity hypothesis. `Pi3 X` is exactly Mathlib's `HomotopyGroup.Pi 3 X.carrier X.point`.

Mathlib defines this as the quotient of genuine continuous maps I^3 -> X that send the whole cube boundary to the base point, under homotopy relative to that boundary. The proof imports the original checked `Mathlib/Topology/Homotopy/HomotopyGroup.lean`, whose CommGroup instance is derived from actual coordinatewise concatenation of these cube-loops by the Eckmann-Hilton argument.

The submitted file explicitly exposes the genuine interchange law between coordinates 0 and 1 even before quotienting, and their common unit on homotopy classes. The theorem `actual_pi3_comm` then uses the resulting checked group structure. `actual_loops_commute_up_to_based_homotopy` strengthens the presentation back to the underlying representatives: concatenating two actual cube-loops in either order gives maps homotopic relative to the complete boundary. Thus an arbitrary supplied CommGroup is never substituted for the actual homotopy group.

For the mathematical explanation, let m_0,m_1 be the operations on classes from the first two coordinate directions and e their common constant-loop unit. The interchange law first gives

m_0(a,b)=m_0(m_1(a,e),m_1(e,b))=m_1(m_0(a,e),m_0(e,b))=m_1(a,b).

It then gives

m_0(a,b)=m_0(m_1(e,a),m_1(b,e))=m_1(m_0(e,b),m_0(a,e))=m_1(b,a)=m_0(b,a).

Associativity and inverses are the usual actual homotopy-group structure. The checked library implements this argument, not an assumed abelianity axiom.

## The pro-system itself is handled levelwise

`ThirdHomotopyDiagram I` is indexed by an arbitrary category I. Each object is an actual pointed space's Pi3; its arrows are group homomorphisms between those actual groups, with identity and composition laws. There is no commutativity field. This is more general than the diagrams arising from pointed transition maps, and includes every cofiltered such diagram.

The code independently constructs its group-valued diagram `groupDiagram : I -> Grp` and its commutative-group-valued diagram `abelianDiagram : I -> CommGrp`, and supplies an explicit natural isomorphism

forget(abelianDiagram) ~= groupDiagram.

The components are identity homomorphisms on the actual Pi3 groups. `every_actual_layer_comm` and `no_nonabelian_layer` also state the objectwise conclusion explicitly. Hence the standard pro-Pi3 diagram is already represented by abelian groups, before any inverse limit is taken.

This distinction is essential. An inverse limit alone can forget nonabelian information in a pro-system, so an abelian inverse limit would not be sufficient. The primary proof is the actual levelwise CommGrp factorization. We do not claim that every arbitrary pro-isomorphic presentation must have abelian groups at every stage; the canonical homotopy-group presentation does, which supplies the required pro-abelian representative.

## Quotient and profinite interpretations

`every_quotient_image_comm` proves that the image of any surjective homomorphism from an actual Pi3 group into an otherwise arbitrary group is abelian. No commutativity on that target group is assumed. `normal_quotient_comm` applies this to actual quotient groups by normal subgroups. Consequently every finite quotient used for profinite completion is also abelian.

The actual compatible-tuple inverse limit is defined as a subgroup of the product of the group diagram, with the transition compatibility equations. Its closure under identity, multiplication and inverse is proved. `actual_pi3_inverse_limit_comm` handles original Pi3 diagrams; `quotient_inverse_limit_comm` handles diagrams of arbitrary quotient images of actual Pi3 groups, in particular finite quotients and their profinite limit. These are additional checks; the pro-system conclusion does not rely only on them.

## Personally checked primary reference and exact formal boundary

Mohammed Moutand, *On schemes with trivial higher etale homotopy groups*, arXiv:2312.08505v2, 26 February 2026, https://arxiv.org/pdf/2312.08505v2 , section 2.1, PDF page 2. Actually opened and read. It states the standard Artin-Mazur-Friedlander construction Et : Sch -> Pro-Ho(Ssets) for locally noetherian schemes and defines pi_n^et(X,x) as pi_n(Et(X),x_et). A smooth variety is within this setting.

Using the standard geometric-realization interpretation of the homotopy groups of the pointed simplicial levels, their third homotopy groups are actual pi_3(|K_i|,k_i). The universal Lean theorem applies to every one of those actual pointed topological spaces. The induced transition homomorphisms give exactly a diagram of the kind treated above. Thus the standard etale third homotopy pro-group has an abelian-valued representative. Profinite completion, if included in the chosen convention, preserves this conclusion by the quotient and limit arguments above.

Lean does not construct schemes, rigid etale hypercovers, the Et functor, geometric realization, or the functor inducing Pi3 homomorphisms from pointed continuous maps. Those standard definitional/construction bridges are stated mathematically, with the primary reference. Lean instead quantifies over every actual space and every homomorphism diagram of their actual Pi3 groups, proving the complete universal obstruction needed for this application. No custom etale object is named and then assigned abelianity; no additional axiom or hypothesis about etale groups is used inside Lean.

## Adversarial author audit

1. Actual geometry: Pi3 is the existing relative-cube-homotopy quotient, not a newly defined convenient group.
2. No circular input: BasedSpace supplies no Group or CommGroup. Diagram data supply no commutativity assumption.
3. Actual Eckmann-Hilton: both distinct coordinate concatenations, common units and their actual interchange law are available in the proof and checked library.
4. Representative check: reversed cube-loop products are homotopic relative to the full boundary, not merely equal under a fabricated quotient relation.
5. Correct degree: all primary groups are exactly dimension three, indexed by Fin 3. No result about pi_1 or stable homotopy is substituted.
6. Pro versus limit: the entire diagram factors through CommGrp before taking limits; the inverse-limit result is supplementary.
7. Reindexing caution: the conclusion is that the pro-object has an abelian-valued representative, not the false assertion that every possible pro-isomorphic presentation has abelian stages.
8. Quotients: surjectivity is explicit; a target Group is permitted without assuming it commutative. The code proves that conclusion from the actual Pi3 source.
9. Limits: the limit is the genuine subgroup of all transition-compatible tuples, not an arbitrary group named a limit.
10. Source coverage: internal nonabelianity is impossible universally, so the finite-pi_1 premise and smoothness restrictions cannot produce a witness. No claim about the value of any Enriques surface homotopy group is necessary.
11. Formal boundary: schemes and the standard etale/realization construction are outside Lean and are identified explicitly. No claim that all etale geometry was formalized is made.
12. Trust: eight central printed dependencies are only propext, Classical.choice and Quot.sound; no sorry, admit, custom axiom or native_decide occurs. There is no numerical computation requiring an auxiliary verifier.

## Files and reproducibility

Main: `round5/drafts/00000002440/lean/Main.lean`, frozen SHA256 `40a0bf4691e533896eb1e47a13ac87e014738c87b3ba8f4b38372da105397736`.

Pinned Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b. The default Lake target is Main and warningAsError is enabled. `round14/quantum/check2440.py` records exact commands, cwd, exit codes, timings, hashes and raw output in `2440-status.json`, `2440-strict.log` and `2440-lake-build.log`. The wrapper is the existing `round7/run_safe.py`.

No previously frozen proof, TeX, PDF, PR, other problem or editor state was changed. Only the new 2440 project and its review/check records were written. Missing official pinned Mathlib dependency artifacts were fetched through the existing cache.


Reviewed artifact hashes:

- Main.lean: `40a0bf4691e533896eb1e47a13ac87e014738c87b3ba8f4b38372da105397736`
- main.tex: `2d02c0d5e4c11bce141c599eba4f56ab6fe1d995f21820d79bdfcf1b4f572763`
- main.pdf: `4d5bd09c0925db92af722315c00fbbd80ec96f5d1ab2319126265d90b812f0da`
- SOURCE.md: `03d57359934ae095fec66337cd08932ae4bebe74291fabb2232fa60d0641f923`
