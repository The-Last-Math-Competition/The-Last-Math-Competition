# Author-agent adversarial self-review: 00000007841

Verdict: PASS

# Conjecture 7841: author proof, scope and adversarial review

Status: author proof complete, awaiting parent semantic review, clean-room validation, LaTeX/PDF and publication. No independent reviewer is claimed.

## Exactly which claim is disproved

The bilingual source defines p(G) as the probability of outputting **any** minimum cut. It then claims that the stated lower bound 2(1-epsilon(n))/n^2, epsilon(n)=O(1/n), is tight on cycles; the Chinese says precisely that equality is attained on cycles. That conjunct is false: for every n>=3, the actual Karger contraction algorithm on the simple connected cycle C_n has p(C_n)=1. The proposed expression tends to zero, even under the weaker hypothesis epsilon(n)->0. Thus it is neither equal nor asymptotically equivalent on this family. A conjunction containing this assertion is disproved.

The distinction is essential: the familiar Karger estimate 2/[n(n-1)] is the survival probability of one *prescribed* minimum cut on a cycle, not the probability of returning *some* minimum cut. This submission does not formally establish the rho(n) lower bound or discuss its actual extremizers. Do not present the rho part as the Lean conclusion.

## Ordinary mathematical argument

Represent C_m by vertices and edge labels Z/mZ, with edge i joining i to i+1. For m>=3 this is the usual simple connected cycle. When m=2 the same edge-labelled representation has two parallel edges; they must be retained.

For any selected edge e of C_m with m>=3, rotate e to zero. The map q:Z/mZ -> Z/(m-1)Z given by q(x)=max(val(x)-1,0) merges 0 and 1. It has no other collisions. The selected edge becomes a loop and is deleted. Every other source edge maps bijectively onto a target cycle edge, and its target endpoints are q(i),q(i)+1. Undoing the rotation gives the actual contraction of arbitrary e. The quotient is the cycle multigraph C_(m-1), including its parallel edges when m-1=2.

The number of crossing edges of a Boolean cut A is cut_m(A)=sum_i 1[A(i)!=A(i+1)]. It is even: write each crossing indicator as twice a 0-to-1 indicator plus A(i)-A(i+1); the latter telescopes around the cycle. Every nonconstant cut has a crossing, since an assignment equal on all consecutive vertices is constant. Hence every nontrivial cut has at least two edges.

At m=2 the algorithm returns the unique bipartition, of size two. Every contraction is a surjective vertex quotient, and pulling a cut back preserves properness and its edge count. Consequently every full contraction history returns an actual minimum cut of the original C_n.

At current order m, Karger samples each current edge with probability 1/m. The contraction certificate proves that all m edge labels are exactly the actual non-loop edges, so the complete history weights are 1/n * 1/(n-1) * ... * 1/3. Their sum is one. The success event is the assertion that the returned proper cut has no larger size than any other proper cut. Every history satisfies this event; summing their actual path weights gives p(C_n)=1.

For any correction with |epsilon(n)| <= C/n eventually, arbitrary large n have 2(1-epsilon(n))/n^2 < 1. Lean additionally proves the expression tends to zero whenever epsilon tends to zero. Exact equality and asymptotic sharpness on cycles are both excluded.

## Lean semantic map

- `inputGraph n`: Mathlib `SimpleGraph.cycleGraph (n+3)`, an actual simple graph on `ZMod (n+3)`.
- `input_connected`, `input_vertex_count`, `input_edge_count`: connected simple inputs of every order >=3 with n vertices and n edges.
- `input_edges`, `edgeLabel_injective`, `cut_is_actual_edge_count`: edge labels are in bijection with the actual undirected input edges, and the cut formula is their actual crossing-edge count.
- `collapse`, `contract`: explicit arbitrary-edge contraction vertex maps.
- `contraction_vertex_fibers`: the quotient identifies exactly the selected edge's two endpoints.
- `exactly_one_edge_deleted`: only the selected edge turns into a loop.
- `other_edge_preserved`, `contraction_edge_bijection`: all other original edge identities and their endpoints give the next cycle multigraph, with parallel edges retained.
- `cut_contract`, `contract_surjective`, `proper_pullback`: ordinary lifting of quotient cuts and exact cut-size preservation.
- `minimum_cut_lower_bound`: every proper cycle cut has at least two edges; this is proved from parity and connectivity, not assigned as a definition.
- `History k`: the actual finite product of edge choices at current orders k+2,k+1,...,3.
- `output k h`: an actual vertex bipartition of the original graph, obtained by recursively pulling the final two-vertex partition back through the selected contractions.
- `every_history_cut`, `every_history_success`, `actual_graph_success`: every branch returns a proper minimum cut of the actual original simple cycle.
- `pathWeight`, `pathWeight_uniform`, `history_card_succ`: actual sequential uniform-edge probabilities and normalization; no event is defined to have probability one.
- `actualSuccessProbability`: sum of actual path weights restricted to the genuine event of outputting any minimum cut.
- `actual_cycle_success_probability`, `cycle_counterexample`: p(C_n)=1 for the full family.
- `actual_no_cycle_sharpness`: any O(1/n) correction fails equality at arbitrarily large orders.
- `proposed_bound_tends_zero`: even epsilon->0 makes the proposed bound vanish.

Indexing: `History k` starts from order k+2. Thus the simple input `inputGraph n` of order n+3 uses `History (n+1)`. `cycle_counterexample` bundles these indices explicitly. The internally used order-two graph is a multigraph, not a false simple-cycle input.

## Author adversarial review

1. **Prescribed cut versus any cut:** Success compares the returned partition to every proper partition. No designated cut is selected, so it matches the source p(G), rather than a single-cut survival event.
2. **Sampling rule:** Every current edge is a distinct label; `contraction_edge_bijection` and `exactly_one_edge_deleted` certify the true sample space. `pathWeight` uses exactly 1/m at a stage with m edges. There are no artificial independent keep-coin probabilities.
3. **Actual contraction:** Vertex fibers are proved to merge exactly the chosen endpoints; the chosen loop alone is removed, remaining edges keep their identities, endpoint incidences and multiplicities. The cut is lifted by that quotient map itself.
4. **Parallel-edge trap:** The terminal 2-cycle has two parallel edges. It is never replaced by Mathlib's simple `cycleGraph 2`, which would have one edge. `terminal_cut=2` is checked by ordinary kernel `decide` on the correct edge-labelled object.
5. **Simple connected input:** Only orders >=3 are offered as input examples. Mathlib's actual cycle graph, connectedness and every underlying undirected edge are linked to the algorithm's cut count.
6. **All branches and unbounded orders:** `actual_graph_success` and the probability theorem quantify over arbitrary n and arbitrary histories. The exact auxiliary computations are not substitutes for this theorem.
7. **Asymptotic qualification:** No finite small-n exception is used. There is a quantitative arbitrary-large-order contradiction for every eventual O(1/n) correction, plus a full limiting theorem under epsilon->0.
8. **Scope honesty:** The disproof targets the explicit tight-on-cycles conjunct. It does not claim a Lean theorem about the infimum rho(n), general graphs, near-complete graph extremizers, or the classical single-cut lower bound.
9. **Auxiliary computation:** `verify.py` independently enumerates actual original-edge contractions, preserving multiplicities and deleting only loops. It checks C3..C9 success=1 and complete graphs with nontrivial probabilities, including K4=4/5, so the verifier does not hardcode success=1. This verifier was supplied by the parent as an independent implementation and copied unchanged; it is supplementary, not trusted by Lean.
10. **Proof trust:** Mathlib is pinned to Lean4.19 / c44e0c8ee63ca166450922a373c7409c5d26b00b. Strict checking uses warningAsError; all main theorems print only standard propext, Classical.choice and Quot.sound. There is no sorry, admit, native_decide or custom axiom.

Parent must still review the whole final Main.lean, independently rebuild the final submitted project, and ensure the paper states precisely this scope.

## Explicit normalization and asymptotic gap (parent review follow-up)

`pathWeight_nonneg` and `sum_pathWeight` make the finite probability distribution explicit: all weights are nonnegative and their total is exactly one. `actual_gap_tends_one` proves p(C_n) minus the proposed expression tends to one whenever epsilon tends to zero. `actual_gap_not_tends_zero` proves it cannot tend to zero. Thus the source's cycle claim fails even under an additive asymptotic-sharpness reading. These lemmas are part of the final frozen source and final strict/build logs.

## Final frozen source and executed validation

Main.lean SHA-256: `7b0f7b1e456cd6dbf312b06da97d91e3345a51ebec210ee33091b384bce92727`.

Final author checks, all exit code zero:

- `lake env lean -DwarningAsError=true Main.lean`: 16.985 seconds.
- Full `lake build`: 17.359 seconds, `Build completed successfully.`
- Actual exact-arithmetic `verify.py`: 0.062 seconds; C3..C9 all probability one and K4/K5/K6/K7 nontrivial complete-graph checks passed.

Exact commands, working directories and timings are recorded in `round13/graph/7841-result.json`; raw outputs in `7841-strict.log`, `7841-lake-build.log` and `7841-python.log`. Every printed theorem has only standard axioms. These checks concern the exact frozen Main hash above. No TeX/PDF was created by the author agent and no PR was opened by it.


Reviewed artifact hashes:

- Main.lean: `7b0f7b1e456cd6dbf312b06da97d91e3345a51ebec210ee33091b384bce92727`
- main.tex: `0f4ebbebb100f1a735a87229426f33d9a87a6395b4fc55d22d038b1f8fd6ed64`
- main.pdf: `28c1efeb7ae3e83cf9cd56c5f6b53d1d06c377bef2a9b5d90cd6e093f0335a65`
- SOURCE.md: `4e150cf1a14aea675fe8bf7f6688a94aba0f2273708a82abfdef38ed8dae54c2`
