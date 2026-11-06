# Statement Alignment: 00000005838

## Frozen Source and Necessary Clause

Source commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400; Git blob
bcf128f6c8b7e7c438e4e096e9e99e38c3135082; raw UTF-8 SHA-256
c29985410d56eec486321081fc35957dbf31d5b14ffce47a32214383d48135d7.
Both complete languages are retained verbatim in source.md.

Both assert that the number of real-valued blocks of an involution
centralizer is half the total. This is a separate necessary conjunct.
The source does not restrict to odd primes, nonabelian/simple groups or
exclude the principal block. We choose G=C2,p=2, a finite nontrivial instance
with an ACTUAL nonidentity order-two element, not an empty/trivial loophole.
No meaning is invented for the undefined surrounding dichotomy/kernel terms.
The conjugate-pair clause is not separately refuted.

## Standard Modular Block Convention

The source's p-blocks use the standard splitting modular group-algebra
definition: nonzero primitive central idempotents of K[H], for algebraically
closed characteristic-p K. Primitive means indecomposable into two nonzero
orthogonal central idempotents. BlockTheory defines all these equations on
actual algebra elements, not Boolean labels or an assumed cardinality.
Webb's author-hosted textbook Chapter12 defines this convention and its
ordinary-character partition correspondence. The general dictionary to a
character-partition API is cited/reviewed, not claimed as a general Lean
representation-theory theorem. Characteristic-zero semisimple idempotents
are not substituted for modular p-blocks.

## Exact Mapping

| Source object or clause | Actual formal object and theorem | Paper |
|---|---|---|
| Finite group and nonidentity involution | Multiplicative(ZMod 2), card2, involution_ne_one and involution_square | Section2 |
| Involution centralizer | Actual Subgroup.centralizer of the singleton, proved top; centralizerEquiv | Section2 |
| Modular splitting field, p=2 | Actual AlgebraicClosure(ZMod 2), constructed Field/CharP2/IsAlgClosed instances | Section2 |
| Centralizer modular group algebra | Actual MonoidAlgebra with centralizer subtype; genuine domCongr AlgEquiv and idempotent transport | Sections2-3 |
| All algebra elements and multiplication | Actual coefficient decomposition/square_formula, universal over every characteristic-two field | Section3 |
| Primitive central block object | CentralIdempotent/PrimitiveCentral and Block subtype with nonzero/central/idempotent/orthogonal indecomposability | Sections1,3 |
| Actual total block count | centralizer_block_count=1 and centralizer_blocks_finite, not an assumed stored count | Section3 |
| Actual selected-block count | Predicate subtype for arbitrary P and selected_blocks_finite | Section4 |
| Half count in natural cross-multiplied form | any_selection_not_half_count: twice ANY selected count differs from total | Section4 |
| Ordinary rational/real half count | any_selection_not_half_rational and any_selection_not_half_real | Section4 |
| Necessary involution-centralizer half clause | HalfBlockClause and half_clause_false_for_every_selection over arbitrary dependent selection families | Section4 |

## Why No Realness Classifier Is Needed

For EVERY predicate on the actual singleton block type the selected subtype
has a natural cardinality r, with 2*r!=1. The actual real-block predicate is
one such predicate under any ordinary convention selecting blocks. The final
theorem quantifies universally over a dependent selection FAMILY, assumes
the half clause for all actual nonidentity square-one elements, and
instantiates it at the proved involution. It is not existence of an unrelated
false predicate, a definition of realness as True/False, or an assumed
classification of ordinary characters.

The count one, the actual finite block type and every selected subtype's
finiteness are proved. Nat.card's default for infinite types is never used
to manufacture the answer. Half is rational/real equality, not Nat floor
division. The concrete main conclusion carries no unproved idempotent,
block-cardinality or negative-conclusion premise.

All 34 public theorem types and recursive axiom footprints are audited;
only three standard foundational axioms are allowed. The installed compiler
and pinned dependency caches remain explicit trust inputs, not a full clean
dependency rebuild, empty-machine bootstrap or cross-platform validation.
No original conjecture or organizer metadata is changed. Independent AI
frozen-package review is not human endorsement or upstream acceptance.
