# Independent review: TLMC 00000008207

Date: 17 October 2026.

## Verdict

PASS. The six-element minimum semilattice gives a complete counterexample to the asserted power-of-two restriction-fiber cardinality. The mathematical proof and Lean formalization count actual representation-isomorphism classes in a restriction fiber, rather than only enumerating scalar characters. Both ordinary unital and zero-preserving conventions are covered.

## Source and mathematical verification

Independently fetched and read both language versions of the official conjecture through the GitHub connector. Source blob: 6600f8caff54e2f0096802e7b1230f9dcb466634. The supplied source.md has exactly that Git blob identity.

For M={0,1,2,3,4,5}, a*b=min(a,b) is associative with identity 5. Every element is its unique inverse in the inverse-monoid sense. The only unit is 5.

For an irreducible nonzero unital representation rho, each rho(a) is a commuting idempotent. Its kernel is invariant. If the kernel is all of V, rho(a)=0; if it is zero, rho(a)(rho(a)v-v)=0 forces rho(a)=I. Thus all lines are invariant and V has dimension one. Its scalar character is a unique upper-threshold function chi_t(a)=1 exactly when a>=t. The six possible thresholds are all irreducible and pairwise inequivalent. All restrict to the trivial one-dimensional representation of the unit group. The fiber consequently has exactly six elements, and six is not a natural power of two.

Under the zero-preserving convention, exactly the constant-one threshold is removed; the fiber has five elements, likewise not a power of two. This conclusion is independent of the conjecture's imprecisely described parameter k. The separate image-description and smallest-example assertions need not be resolved.

The written proof also correctly covers arbitrary algebraic representation carriers: a nonzero vector's finite monoid orbit spans a finite-dimensional nonzero invariant subspace, which is the whole irreducible representation. Choosing a basis then gives the coordinate model used formally. In fact the written central-idempotent/line argument already works without a finite-dimensional hypothesis.

The cited primary reference was independently checked: Ganyushkin, Mazorchuk and Steinberg, [On the irreducible representations of a finite semigroup, arXiv:0712.2076v2](https://arxiv.org/pdf/0712.2076). Corollary 9 on printed page 7 gives the broader degree-one classification for finite idempotent semigroups; printed page 3 states the unital-module convention and finite-dimensionality of simple modules over a finite-dimensional field algebra. The submitted proof is self-contained and does not rely on the citation as an unproved formal axiom.

## Formal semantic review

Read Monoid.lean, Representation.lean and Main.lean in full.

- Rep K n contains genuine operators on K^n with addition and scalar linearity, identity action and multiplication compatibility. Its axioms do not impose the desired threshold classification.
- Subspace includes zero, additive closure and scalar closure, hence the standard linear-subspace properties. Irreducible requires n>0 and allows only zero/all invariant subspaces.
- Kernel invariance, the zero-or-identity lemma and the dimension-one theorem are proved from these definitions.
- The scalar-character classification, irreducibility of each scalar representation and classification of every irreducible are proved, not assumed.
- LinearIso includes linear forward and backward maps with both inverse laws. RepIso adds the actual intertwining equation. Distinct standard thresholds are proved inequivalent under this relation.
- RestrictsToTrivial requires a linear isomorphism to the one-dimensional trivial target and intertwining for every actual unit. This is the actual restriction condition, not an arbitrary label for a character.
- RestrictionFiber is a quotient of these actual irreducible fiber objects by representation isomorphism. The map from Fin 6 is proved injective and surjective.
- HasCard means existence of a bijection from Fin n. Cardinality uniqueness is proved generically, so the final no-power-of-two statement cannot be evaded by a second enumeration of another size.
- The zero-preserving subfamily is defined by the actual zero operator at the monoid zero. Its quotient is independently enumerated bijectively by Fin 5.

The coordinate-space boundary and the nonformal finite-orbit/basis reduction are explicitly disclosed in the paper. They are conventional mathematical identifications, not conclusion-specific axioms.

## Independent reproduction and trust audit

Copied the source and reproducibility files into a separate clean directory. Used Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, with only the supplied Std development.

- Clean Lake build: PASS.
- Warning-as-error elaboration of Monoid, Representation and Main: PASS.
- Independent leanchecker kernel replay of all three modules: PASS.
- Warning-as-error elaboration and axiom reports for all 47 authored theorems: PASS.
- Full environment audit of all 293 TLMC8207 namespace declarations, including definitions, structures, generated declarations and instances: PASS. All transitive axiom closures contain only propext, Classical.choice and Quot.sound, as applicable.
- No unsafe declarations, custom axioms or opaque declarations in the namespace.
- Source scan after removing comments: no axiom, unsafe, opaque, sorry, admit, native_decide, run_tac, run_elab, implemented_by or extern tokens.
- Supplied Python check: PASS for the monoid/inverse/unit computations; exhaustive scalar characters over F2, F3 and F5; and all 96 two-dimensional F2 representations, each having a proper invariant line.
- Separate reviewer-written enumeration: PASS for the min-monoid laws, unique inverses, unit group, all Boolean characters, threshold classification, common restriction value and zero-preserving subfamily.

The finite computations supplement the general representation proof. They are not used as proof oracles and are not a substitute for exhaustive representation classification.

## Paper and presentation

Read the complete final paper, independently rendered all three PDF pages, and visually inspected each page. The proof, formal boundary, reference and reproduction instructions are correct and legible. No clipped formulas, missing glyphs, overlaps or unreadable passages were found. The final first two pages are pixel-identical to the already inspected rendering; the final third page was rendered and inspected again after the last typography-only adjustment.

Read the final README, checked that the frozen source matches the clean-audited copy byte for byte, and verified every entry of the package SHA256SUMS. The clean package contains the proof, report, reproducibility scripts and verification logs, without scratch probes or compiled caches.

The PDF was also independently rebuilt from the final LaTeX source with the supplied build script. Layout-preserving extracted text and all three rendered page images exactly match the delivered PDF.

## Reviewed file identities (SHA-256)

- Monoid.lean: ba94c07a1fc6d1f35a9fc9b562c9168356f5c61a24322bc657030a22714faa9e
- Representation.lean: ba80b6869065923c21ae660dd006755e8131b504bf3f84780b46efa000159492
- Main.lean: 52a86d3ee0f5a82786f720f2f4dacc8e01071569b83a027ca70493ffad46e3f0
- Audit.lean: 0d16ddfc37db79e8158459930cba888ea89c16dd7ba8fd382607a246ed5acbfb
- paper.tex: b759c2a80233d2839a8910f19a4268a6d06ef22535068a479c73bd2e91f08313
- paper.pdf: a49094989cbe44aea9f022a641ec38cd487e171b17da6d5cb55fff01c444ce11
- source.md: dd7e801968f3f8ee559c12fb6bc69798ddd67bd79d1720556a6923d8adbc7350
- README.md: 57b5fe06240ebc5e9dabb4c3dec20a72fed0fe4c3b500c2dc8af0674d9dd6240

Publication and live eligibility checks are separate from this mathematical and reproducibility review.
