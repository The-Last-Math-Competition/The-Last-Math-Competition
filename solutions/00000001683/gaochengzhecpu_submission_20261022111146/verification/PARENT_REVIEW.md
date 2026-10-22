# Parent adversarial review: conjecture 00000001683

Verdict: PASS

I read the exact bilingual source, the complete Lean proof, all of the human proof and the author's self-review. Both language versions assert reconstruction of 3-uniform hypergraphs for every order at least eight, with a separate assertion restricting any counterexample to Steiner triple systems. A pair on nine vertices is within that range. The paper correctly explains that Steiner triple systems have the usual pair-codegree-one condition; the source's design terminology is not used to substitute a different object.

The formal Hypergraph3 is a Boolean relation on triples, with the two adjacent-transposition symmetries and no repeated vertex. These generate full symmetry and exclude all repetitions, so the model is exactly a simple 3-uniform hypergraph. The displayed unordered edge sets each have 28 edges and all their edges have cardinality three. The universally quantified edgeX_iff_mem and edgeY_iff_mem theorems connect the entire bit encoding to these actual finite edge sets. I checked that all edges printed in the paper match the formal objects. There is no substitution of a degree table for a hypergraph.

IsIso quantifies over every vertex equivalence and every triple, with an iff rather than a one-way edge implication. Hypomorphic has an outer bijection on deleted vertices, so deck multiplicities are preserved, and an inner vertex equivalence taking the deleted vertex to its matched vertex. Bijectivity restricts it to a true bijection between the complements. The edge iff on all triples avoiding the removed vertex is exactly induced-card isomorphism. The nine explicit certificates match each vertex to itself and cover every deletion.

Degree and codegree invariance follow from equivalences of the actual counting subtypes. doubleDegree is twice the ordinary degree, and the paper uses the correctly halved degree sequence. I followed the full nonisomorphism proof: the unique degree-eight vertex fixes zero; the degree-nine class restricts images of 1 and 2; the codegree-three requirement leaves four ordered possibilities; a further codegree forces the image of vertex 3 or 4, and in every case one explicit triple has conflicting edge status. The Lean branch tree exhausts all nine image choices at each selected vertex and proves contradictions from invariants, injectivity or edges. It does not silently assume that only the named deck permutations could be isomorphisms.

I independently ran the root's finite audit on the final frozen Main.lean. It checked all 362880 vertex permutations without finding an isomorphism, verified the nine card equalities with multiplicity, and compared every one of the 729 ordered triples in each bit encoding to the edge lists. A separate GPT-6.1 Sol / High reviewer independently decoded the Lean source, checked all tables and cards, exhausted the 576 degree-preserving maps, and found the same four codegree-preserving candidates, each with an edge conflict. That reviewer also independently ran the final strict Lean command successfully. Its report, log and a portable supplementary checker are included. These numerical checks supplement the kernel proof and are not proof oracles.

The pair 0,1 has codegree two in both examples, proving that neither is Steiner. X_not_steiner, Y_not_steiner and steiner_clause_false formally establish the additional refutation. Nine does satisfy the standard congruence condition modulo six; the submission explicitly does not claim to disprove that necessary condition for actual Steiner systems. Kocay's classical family and Cooper-Okur's public description receive clear attribution, and no new infinite-family construction is claimed.

The final unchanged Lean source passed a fresh-directory lake build and a separate strict Lean invocation with warnings as errors, taking about 45 seconds each. The actual logs show successful exits and the eight printed theorem audits use only propext, Classical.choice and Quot.sound. Dependencies are pinned and their tracked source cleanliness was checked. After layout-only TeX repairs, only PDF checks were refreshed, with all Lean hashes rechecked against that completed fresh build. Native compilation of the final saved TeX succeeded.

I visually inspected all four final rendered PDF pages. Edge lists, both card tables, the degree/codegree displays, all four edge-conflict cases, theorem statements, attribution, formal scope, reproduction commands and references are readable and unclipped. The final PDF has no compiler warnings, missing characters or overlapping content. The submission records author development, a distinct parent adversarial review and an additional AI reviewer; it does not claim human or external independent approval.


Reviewed artifact hashes:

- Main.lean: `0d0236cd3cd074a3c79afa45b11efa835c5bf9f1b59917df0c95576fae1b2466`
- main.tex: `eb6b67408de2ba9d9c70410e6f55f82d374134d36a321cb7aab1dae02c41e472`
- main.pdf: `ca60fffc959731a4272b95e1c01d3a51f9a94ef1234671e1e0dc176ef5db9238`
- SOURCE.md: `6239d7092c6aa24d47141607a9201501e921a1d6cc266c24246734415ec5f294`
