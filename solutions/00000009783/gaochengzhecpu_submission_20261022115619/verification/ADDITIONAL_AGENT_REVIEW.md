# Delegated peer semantic review: conjecture 00000009783

Verdict: PASS for the stated ordinary-path-depth reading; no substantive mathematical or semantic defect found.

This is a separate delegated-agent reading within the same AI workflow, not
external independent review. I read the complete exact bilingual SOURCE.md,
the complete Main.lean, main.tex, README.md, and author SELF_REVIEW.md. I did
not compile Lean, inspect a PDF, run publication tooling, or modify the draft.
Those checks remain the coordinator's responsibility.

Reviewed file fingerprints:

- `lean/Main.lean` SHA-256:
  `f68ef43b8dced7044f0b1a16e5b0282ef86ef0acb28863ee9c1ce989ef05a8db`
- `main.tex` SHA-256:
  `32e7350b99cf4aede4f852b98d6dfeecb2169fe2cfff1ba7f25a651ab348af6f`

1. **Exact source target.** The explicit last clause in both languages equates
   maximal ideal-chain length with supremal Bratteli path depth. The proof
   attacks that clause directly. The hereditary-subset and dimension-vector
   assertions need not be proved or disproved once this conjunction fails.
   No unrelated easier invariant is substituted.

2. **Actual AF algebra.** The object is Mathlib's actual complex field with
   its C-star algebra instance. `complexStages` is an actual sequence of
   StarSubalgebra objects, and `complex_approximatelyFinite` verifies finite
   dimension, closedness, monotonicity and dense union. Constant stages are
   legitimate. The predicate uses unital subalgebras, a sufficient subclass
   for this unital counterexample; no claim about arbitrary nonunital
   internal presentations is needed.

3. **Independent standard-definition check.** I inspected Blackadar's
   author-hosted Classification of C*-Algebras (June 4, 2025),
   https://bruceblackadar.com/Mathematics/Class.pdf . Sections I.3.2.1-2
   explicitly include finite-dimensional C-star algebras among AF algebras.
   Sections I.3.2.6-8 define partial embedding multiplicities and the
   level-by-level diagram. These support the paper's constant one-block
   presentation and its single-edge ray; no strict-growth hypothesis is
   part of the cited definition.

4. **Inductive-limit and matrix-block bridge.** `stageScalarEquiv` and
   `stageMatrixEquiv` identify the actual stage carriers with C and M1(C).
   `internal_external_stage_compatibility` connects the internal inclusions
   with the external identity maps. `matrixConnecting_identity` verifies
   that the transported matrix-block map is actually the identity.
   The unital and nonunital universal-property theorems establish the
   constant system's actual limit; continuity is handled from finite
   dimension. The universal properties are elementary here, and their
   code matches the paper's factorization argument.

5. **Multiplicity is appropriate in this exact case.** The code computes
   `edgeMultiplicity` as the complex dimension of the identity map's range.
   Such a formula would be wrong as a general definition of multiplicity
   for arbitrary matrix embeddings. In this one-dimensional identity case
   it equals the unique block multiplicity one. The file and paper
   expressly restrict this interpretation, and the concrete matrix identity
   and one-dimensional source/target make the connection valid. I do not
   regard the ray as an arbitrarily attached fake diagram.

6. **Actual paths and depth.** The Quiver arrow type has precisely the
   computed multiplicity between consecutive levels and is empty elsewhere.
   `rayPath n` constructs an actual Quiver.Path from level zero to level n.
   Its length n is proved by induction. The ENat supremum is over actual
   paths and is top because these witnesses exist for every n. Restricting
   to paths beginning at the root would still give the same unboundedness.
   Counting vertices rather than edges also leaves it unbounded.

7. **Genuine closed two-sided ideals.** `ClosedIdeal C` uses actual Mathlib
   Ideal objects with topologically closed carriers. Because C is
   commutative, two-sidedness is automatic. Every algebraic ideal is zero
   or all of C, and both are closed; these two also are star invariant,
   so there is no mismatch with C-star ideal conventions in this example.
   `every_ideal`, distinctness, and the cardinal-two proof classify all
   relevant ideals, not merely two selected ideals.

8. **Maximal chains, not a numerical assignment.** The whole closed-ideal
   order is a chain and `maximal_chain_is_all` proves every IsMaxChain is
   exactly this whole two-element set. StrictMono finite chains are bounded
   by the actual finite cardinality. The explicit zero-to-whole chain
   attains one strict inclusion and two elements. Therefore both claimed
   chain-length conventions are actually realized and finite, in contrast
   to the depth supremum. The supremum-of-finite-chains definition is
   justified here by the separately proved unique maximal chain.

9. **Quantified restriction.** `OneBlockDepthClause` restricts the source's
   universal claim to AF commutative C-star algebras star-isomorphic to C,
   with the constant one-block presentation. Its right-hand side is the
   explicitly constructed ray depth. Every such algebra can be presented
   by the same constant M1(C) system through the supplied isomorphism.
   More decisively, the actual instantiated counterexample is C itself,
   where all stage, limit and diagram bridges have been proved. Thus the
   negated restricted proposition is necessary for the ordinary universal
   source claim; it does not derive its contradiction from an unrealized
   pair of unrelated abstract numerical structures. The fixed-object
   `DepthEqualityClause` supplies a second explicit formulation.

10. **Scope and possible alternative readings.** A notion of depth that
    contracts repeated identity levels or counts only genuine ideal
    branching could behave differently, but that is not ordinary directed
    path depth and is not defined by the source. The paper openly states
    the ordinary meaning used. A restriction to infinite-dimensional AF
    algebras or strictly growing stages would be an additional hypothesis
    absent from both languages. These are scope qualifications, not defects
    in the stated counterexample. I found no correction necessary before
    the coordinator's build and presentation checks.

The paper accurately limits its formal claim: it does not assert a general
AF classification or a general hereditary-subset correspondence. My review
supports proceeding with the coordinator's final checks under the explicit
ordinary-path-depth reading.
