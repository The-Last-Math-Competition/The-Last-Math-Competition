# Author-agent adversarial self-review: 00000000470

Verdict: PASS

# Conjecture 470: author proof and adversarial review

Status: author complete after the accompanying recorded checks; parent review is required before publication.

## Exact claim and counterexample

The precise bilingual source is `round5/source/00000000470.md`. It defines the random weighted spanning-tree polynomial as the sum of `p^(sum of edge weights)` over all spanning trees, with independent random edge weights. It claims uniform angular root distribution, at Kolmogorov distance O(v^(-1/2)), for vertex-transitive graph families.

Take the actual simple cycle C_m for every m >= 3. Assign each of its m original edges weight 1 or 2, independently with probability 1/2 each. This law is nondegenerate, has positive integer weights, and is identically distributed as well as independent. Write a for the number of edges of weight 1, b for weight 2, and W for their total weight.

Every spanning tree is obtained by deleting exactly one original edge. Therefore the actual polynomial, including repeated tree weights, is

    tau(p) = a p^(W-1) + b p^(W-2) = p^(W-2) (a p + b).

On the mixed event a > 0 and b > 0, its roots, WITH multiplicities, are W-2 copies of zero and one simple root -b/a. The latter is strictly negative real and thus has argument pi. The mixed event has probability 1 - 2/2^m, which tends to 1.

If arguments are taken only for nonzero roots, the actual empirical distribution is the nonempty point mass at pi. Its CDF at pi is 1, while the uniform CDF is 1/2, so the full Kolmogorov distance is at least 1/2. If all roots are retained using the explicit convention arg(0)=0, the empirical distribution is also nonempty. Its CDF at zero is (W-2)/(W-1), at least 1/2 since W >= m >= 3. The uniform CDF at zero is zero, again giving distance at least 1/2.

For EACH of these conventions the formally defined probability of the event "actual root multiset is nonempty AND its full CDF Kolmogorov distance is at least 1/2" tends to one, and does not tend to zero. Thus angular uniformity fails even in probability. This is stronger than needed to exclude the asserted vanishing O(m^(-1/2)) rate. For any fixed C, C/sqrt(m) eventually falls below 1/2, so the same mixed events violate that rate with probability tending to one. The Lean project formally proves the fixed-gap high-probability obstruction; the elementary comparison with the rate is stated here as its consequence, not represented as an additional Lean theorem.

## Exact formal semantics

The self-contained Lean 4.19 project is `round5/drafts/00000000470/lean`. It uses official pinned Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- `inputGraph n` is Mathlib's genuine `SimpleGraph.cycleGraph (n+3)` on ZMod (n+3). Connectivity, vertex/edge counts, and genuine graph automorphisms carrying every vertex to every other vertex are proved.
- Edges have original labels `i -> {i,i+1}`. Their labeling is proved injective and exhaustive. The graph obtained by deleting one edge is proved connected via a cycle cut argument and hence is a tree from its actual edge count.
- `SpanningTree n` contains ALL simple subgraphs of the input graph that satisfy Mathlib `IsTree`. The equivalence `treeEquiv` proves every such graph is precisely one deletion, and different deleted original edges give different trees. It is not an assumed enumeration.
- `treeWeight` sums actual original-edge weights over the actual tree edge finset. `treePolynomial` sums powers of X over ALL elements of `SpanningTree`. Its factorization is derived by reindexing through the proved equivalence.
- `actual_roots` is equality with Mathlib's actual polynomial `.roots` multiset, proved by polynomial root multiplication and the linear-root theorem. Multiplicities are not discarded. `actual_nonzero_roots` is its literal nonzero filter.
- `empiricalCDF` uses the actual multiset filter and actual multiset cardinality, and `KS` is the supremum over ALL real thresholds of absolute CDF error. The full range is proved bounded above. The limiting events explicitly require positive cardinality, preventing real division-by-zero defaults from entering the interpretation.
- `eventProbability` is normalized counting measure on ALL assignments `ZMod m -> Bool`. Total probability, probability bounds, and monotonicity are proved. The probability of each complete assignment equals the product over its m coordinates of 1/2, certifying the fair independent joint law.
- Exact mixed-event count and probability are proved for every n. Both genuine nonempty fixed-gap failure probabilities tend to one by squeezing between the mixed-event probability and one. Uniqueness of limits proves they cannot tend to zero.

The elementary cycle cut lemmas were physically copied and adapted from our earlier 7841 proof. No file imports another submission or an external local project. The present project compiles its own source module in full.

## Adversarial review

1. **Is the graph family actually vertex-transitive?** Yes: the proof provides actual cyclic translation graph isomorphisms, not an assertion or a graph property assigned by definition. All m >= 3 are covered, including the triangle.
2. **Is the weighting degenerate or dependent?** No: weights 1 and 2 each have probability 1/2. Every complete assignment has mass (1/2)^m, the genuine finite product law. There is no conditioning in the random model. The mixed event is used only for the lower bound, and its probability tends to one.
3. **Could a rare exceptional assignment be masquerading as an asymptotic counterexample?** No: failure occurs on 1 - 2/2^m of all assignments and both actual failure probabilities are formally proved to tend to one.
4. **Were spanning trees or edge multiplicities lost?** No: actual graph subtrees are exhaustively bijected with deleted-edge labels, and the polynomial sums all trees individually. Repeated exponents accumulate as coefficients a and b.
5. **Is the polynomial replaced by a chosen proxy?** No: the displayed factorization is proved equal to the sum over all genuine spanning trees, with actual edge weight sums.
6. **Does zero make the statement meaningless?** The disproof does not rely on that issue: discarding zeros leaves one genuine simple negative root, whose empirical measure is nonempty. Including zeros with arg(0)=0 also fails. Both versions have explicit positive-cardinality clauses in the final probability event.
7. **Are negative angles or branch choices relevant?** All nonzero roots in the mixed event are strictly negative reals, and their angle is pi in both the usual [0,2pi) convention and Mathlib's principal branch. Thus the argument is unaffected by the branch discrepancy away from the support.
8. **Is a single CDF threshold mistaken for the full distance?** No: the distance is the actual full supremum; a proved supremum bound permits the threshold lower bound. No exact KS formula is required.
9. **Does it rule out the stated probabilistic claim?** Yes: probability of a fixed positive gap tends to one, so convergence in probability to the uniform measure already fails. Any usual stronger interpretation of uniform convergence or a vanishing deterministic/probabilistic rate fails as well. No claim about unspecified alternative weight laws is needed: the conjecture gives none that excludes this iid law.
10. **Can one change what `p` means?** In the supplied definition p is the polynomial variable and exponents are sums of random edge weights. We follow that literal definition. A different generating function would be a different conjecture.
11. **Verification scope:** the independent Python script enumerates actual connected (m-1)-edge subgraphs and all 2^m weight assignments for 3 <= m <= 10 using exact integer/rational arithmetic. This is a consistency check only; the Lean proof supplies the unbounded-size result.

## Recorded checks

Run `round14/graph/check470.py` with the bundled Python. It records the actual command, working directory, elapsed time, exit status, Main.lean SHA256, strict Lean log, full lake build log, and exact Python verification log in the same directory. A successful result requires all three checks to pass and forbids proof holes and custom axioms in the source. The printed main theorem axioms must be only propext, Classical.choice, and Quot.sound.


Reviewed artifact hashes:

- Main.lean: `7cc0f740749db62145816c6a70ca098e92d79911e3c08a5f21d445996d996172`
- main.tex: `8dff108b11cc737d53c73403c38907fa650295d4fe755416af10ed884578122e`
- main.pdf: `2b31b09e1d2f1829438577ab0a362f735b31187c0d93a6e87817dec568037366`
- SOURCE.md: `dc9ebd8b04aa481c4f56c9bbcc8616a89ba2a18ef1f1dbe1255cadde65ff5daf`
