# 9305 independent cross-review

**Verdict: PASS for the stated vertex-transitive-support counterexample. No blocking mathematical, semantic, or Lean issue found.** One optional title clarification is noted below. This reviewer did not write the proof and has not modified any frozen source, author log, verifier, or paper.

## Reviewed versions

Read in full: the exact bilingual source, `round5/drafts/00000009305/lean/Main.lean`, `solution.tex`, `verify.py`, and `round14/graph/9305-proof-and-review.md`. Also inspected the author's checker and result record. Reviewed hashes:

- Main.lean: `b1d3a6f9a0a573dc1dbfd07bea2f624b1d65edb6d8e94599e9deaf32ca79d717`
- solution.tex: `a5f94491ba6e4e242d0cdaf86787db6f172c6e5277985b655ec633b5893fe743`
- Author proof/review: `7d0cb7aee32c7375bebbc7e5c9cdcc97592a319042483f3dbab7e03f2aace98`
- verify.py: `b03d84facee7aad4d3a412b836d0f70747122623e693d48051d210af0acfd6ac`

## Rooted quotient and graph semantics

`RootedGraph` contains actual connected, countable, locally finite Mathlib simple graphs and a root. `RootIso` is a whole-graph isomorphism with a proved root equality; its equivalence relation and actual quotient are used. In particular the endpoint roots of P3 are pushed into the same rooted isomorphism class rather than treated as two distinct labeled states.

`Near` uses actual walks and lengths. `ballGraph` is the induced graph on exactly that set, and `BallIso` requires an actual root-preserving isomorphism. The existential representative definition of `cylinder` does not create a label loophole: whole rooted isomorphisms induce ball isomorphisms, and `obstruction_excludes_transitive` explicitly uses `Quotient.exact` to move a hypothetical transitive representative to the representative witnessing the cylinder.

`VertexTransitive` genuinely asks for graph automorphisms carrying each u to each v. It is not ordinary graph connectedness or the transitivity of an equivalence relation. This is the standard convention in the subject: [Aldous–Lyons, *Processes on Unimodular Random Networks*](https://arxiv.org/pdf/math/0603062), §1, PDF page 3, describes transitivity by this vertex-automorphism property.

## The P4 boundary trap

The critical radius-two argument is sound. It never claims that a P3 ball forces the entire connected graph to be P3.

`ball_root_degree` identifies the root's full neighbor set with its neighbor set in the radius-two induced ball. `ball_neighbor_degree` makes the corresponding identification only for an immediate neighbor of the root: every neighbor of such a vertex is reached from the root in at most two steps. The proof does not read a full degree at a distance-two boundary vertex.

`path_unequal_neighbor` always chooses an immediate neighbor. Thus the transported contradiction is between the full degree of the root and the full degree of one of its neighbors, respectively 1 versus 2 or 2 versus 1. Constant degrees are a genuine consequence of actual vertex transitivity.

For the endpoint of P4 the radius-two ball really is endpoint-rooted P3, but its first two full degrees are still 1 and 2. It therefore satisfies the obstruction and is correctly excluded from the transitive class. The independently rerun finite verifier explicitly includes this case.

## Genuine uniform-root finite sequence and limit

`copies m` is the actual disjoint-union graph on `Fin (m+1) × Fin 3`. `walk_same_copy` and `reachable_copy` establish its actual connected components. `componentRooted` uses the induced subgraph on reachable vertices, with `componentIso` giving its actual rooted P3 identification.

`uniformRootPMF` starts from the genuine uniform PMF on every vertex of the finite graph. The second-coordinate marginal is proved uniform, and the quotient class identity is used before proving `uniformRootPMF_eq`. Hence every actual uniformly rooted law equals the same P3 law. The underlying graph cardinalities genuinely diverge. This is not a constant bounded finite graph masquerading as a graph sequence.

Disconnected approximants and finite limiting root components are allowed by the exact source. They also agree with the standard definition: [Aldous–Lyons](https://arxiv.org/pdf/math/0603062), §2, PDF page 10, explicitly defines the uniform-root law for a possibly disconnected finite network by taking the selected vertex's actual connected component.

`LocallyWeakConverges` uses convergence of every rooted ball-cylinder probability. Although the file does not construct a separate local topology or invoke a generic weak-convergence API, exact equality of all the probability measures for every m makes the claimed local convergence immediate; no hidden tightness or cylinder-determination argument is needed here.

## Measure and integral audit

The event A is an actual measurable union of radius-two cylinders. `pathLaw_obstruction` obtains mass one using the support of the genuine mapped PMF and Mathlib's `PMF.toMeasure_apply_eq_one_iff`. This is actual measure evaluation, not an assigned probability table.

`ConcentratedOnTransitive` is an almost-everywhere concentration statement. From the set-theoretic exclusion of A, `transitiveLaw_obstruction_zero` derives the actual equation ν(A)=0. No measurability assumption on the entire transitive class is smuggled into the proof or needed for this implication.

The final theorem quantifies over arbitrary mixing measure spaces and actual measure-valued families. Its hypothesis is the barycentric identity on every measurable event, with Mathlib's genuine ENNReal-valued Lebesgue integral. Almost-everywhere concentration gives `components i A = 0` almost everywhere in the mixing parameter. `lintegral_congr_ae` and `lintegral_zero` therefore turn the identity at A into 1=0. The theorem does not need the component family to be measurable in order to exclude all families satisfying its identity; every ordinary measurable probability kernel is a special case.

Allowing arbitrary component measures and arbitrary mixing measures strengthens the exclusion. It does not reduce a probability-mixture claim to a finite convex combination. Since no such transitive-supported mixture exists at all, no extremality hypothesis on components or on the counterexample is required to refute the source's narrower assertion.

The formal statement uses a.e. concentration, not an explicitly formalized topological support. The paper states that convention. The usual support interpretation is also excluded mathematically because A is an open local-cylinder union disjoint from all transitive classes in the standard rooted graph space. The Lean file should not be described as having formalized that topology/support bridge; it currently does not make that claim.

## Optional editorial point

At `solution.tex:8` the title says “Ergodic Local Limits Need Not Be Supported on Transitive Graphs”, while the body and Lean intentionally do not establish extremality/ergodicity of μ. The mathematical statement is true for this fixed-underlying-P3 law, but the title is a little stronger than the explicitly supplied proof scope. Prefer “Local Weak Limits Need Not Be Mixtures of Transitive-Supported Laws”, or add the short ordinary observation that every re-rooting-invariant event is constant on the fixed underlying P3 and hence has μ-probability zero or one. This is a nonblocking presentation suggestion, not a flaw in the counterexample or mixture theorem.

## Independent reruns

On 2026-10-22, independently ran the strict command from the frozen Lean directory using the pinned runtime and `round7/run_safe.py`:

    lake env lean -DwarningAsError=true Main.lean

Exit code was 0. All six exported theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Independently ran the frozen `verify.py` with the pinned Python runtime. Exit code was 0, with PASS over 202013 rooted finite checks, 8769 radius-two obstruction instances, 199 regular graphs, the explicit P4 endpoint case, and forty exact uniform-root laws. Endpoint and middle masses were 2/3 and 1/3. These computations supplement the arbitrary-graph and arbitrary-mixture Lean proof.

No new theorem, project, subagent, PDF, or PR was created. Parent fresh-build validation and PDF page review remain separate steps.
