# Adversarial self-review: conjecture 00000001683
Verdict: PASS (author mathematical and Lean review; final build and PDF review delegated to coordinator).

1. **Correct reading.** Both source languages assert reconstruction for
   all n >= 8 from the ordinary vertex-deleted deck. The formal claim
   quantifies over all n >= 8 and all pairs of simple 3-uniform
   hypergraphs on Fin n. A pair on nine vertices is in the required
   range. The separate Steiner-only assertion is also formalised and
   negated; no claim is made against the usual necessary mod-6 condition.

2. **Real mathematical objects.** Hypergraph3 has a Boolean triple
   relation, the two adjacent-swap symmetries, and noRepeat. Adjacent
   swaps generate every ordering of a triple; noRepeat and symmetry
   exclude every repeated-vertex triple. Thus this is precisely a
   simple 3-uniform hypergraph relation, not a degree table substituted
   for one. More concretely, edgesX/edgesY are finite sets of unordered
   triples; uniformity and cardinality 28 are proved, and the two bridge
   theorems check every ordered triple against those sets.

3. **Bit-encoding risk.** The index 81*a + 9*b + c uniquely indexes the
   729 ordered triples on Fin 9. The bridge equivalences are Lean
   theorems quantified over every a,b,c, not a comment asserting that
   the decimal constants have the intended meaning. The printed edge
   sets agree with the mathematical lists in main.tex, including all
   eight edges through vertex zero in each object.

4. **Deck multiplicity and card domain.** Hypomorphic uses a full outer
   equivalence matching deleted vertices. For each v, its inner
   equivalence takes v to the matched deleted vertex and preserves
   every triple avoiding v. Bijectivity makes its restriction a
   bijection of the complements; conversely any card bijection extends
   by mapping the omitted vertices. The nine explicit certificates
   match v to v, so every card occurs with its original multiplicity.

5. **All isomorphisms are excluded.** not_isomorphic assumes an
   arbitrary equivalence e and IsIso X Y e. Its branches exhaust all
   nine choices at each selected vertex. They use proved degree or
   codegree preservation, injectivity, or a concrete failed edge
   equivalence. It does not merely reject the nine deck permutations.
   On paper, the unique degree-eight vertex fixes zero, degree nine
   forces e(1),e(2) into {1,2,7,8}, and codegree three leaves exactly
   four ordered pairs. The displayed D-by-L codegree table forces a
   third image in each case and produces four explicit edge conflicts.

6. **Counting conventions.** codegree counts third vertices completing
   an edge and therefore is the ordinary codegree on distinct pairs.
   doubleDegree counts ordered completions, hence gives twice the
   ordinary degree. Both preservation theorems are proved from
   equivalences of actual subtype counting types. The paper uses
   ordinary degrees (8,9,9,10,10,10,10,9,9), exactly half the Lean table.

7. **Steiner clause.** A Steiner triple system requires each distinct
   pair to lie in exactly one edge. Pair {0,1} lies in 012,016 in X and
   014,018 in Y, with no further such edges. Each codegree is two;
   X_not_steiner and Y_not_steiner formalise this contradiction.
   Nine does satisfy the standard congruence 3 mod 6; that arithmetic
   necessity is not purportedly refuted. The word "twin" cannot rescue
   the assertion because neither object is Steiner under any pairing.

8. **Novelty and source.** This is explicitly credited as the n = 3
   instance of Kocay's classical counterexample family, reproduced by
   Cooper and Okur. The proof is self-contained for this finite pair;
   it does not rely on an unformalised infinite-family theorem or a
   theorem about characteristic polynomials. SOURCE.md is copied
   byte-for-byte from the pinned source snapshot and its hash is
   recorded in SOURCE_PROVENANCE.md. The coordinator checked the
   historical PR/metadata snapshot and found no earlier submission.

9. **Kernel and axiom check.** The author ran lake env lean
   -DwarningAsError=true Main.lean successfully after all Lean additions.
   All eight printed theorem-axiom audits contain only propext,
   Classical.choice, Quot.sound. All finite evaluations use decide.
   No custom axiom, sorry, admit or native_decide occurs in the proof.

10. **Review boundaries.** Developed by a delegated AI agent with a
    self-review; the coordinating agent reviews it separately. There
    is no external independent review. This verdict covers the author
    proof and strict Lean check. The coordinator is responsible for
    the fresh build, final PDF compilation and visual inspection,
    final artifact hashes, and the immediate prepublication source,
    metadata and historical-PR conflict gates. Those checks are not
    represented as author-completed work.


Reviewed artifact hashes:

- Main.lean: `0d0236cd3cd074a3c79afa45b11efa835c5bf9f1b59917df0c95576fae1b2466`
- main.tex: `eb6b67408de2ba9d9c70410e6f55f82d374134d36a321cb7aab1dae02c41e472`
- main.pdf: `ca60fffc959731a4272b95e1c01d3a51f9a94ef1234671e1e0dc176ef5db9238`
- SOURCE.md: `6239d7092c6aa24d47141607a9201501e921a1d6cc266c24246734415ec5f294`
