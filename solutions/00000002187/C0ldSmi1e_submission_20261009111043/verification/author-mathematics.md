# Disproof of conjecture 00000002187 as written

The exact bilingual source is preserved in `ORIGINAL.md`. Its SHA-256 is
`56e81da0707150507ae92a849a5d3807d221fd4608b685726460d9b89f3433b9`.

The definition printed in both languages is the minimum number of edges
of a graph containing the path. It imposes no edge coloring, quantifier over
colorings, or monochromatic-copy condition. The proof follows that explicit
definition. It makes no claim about the differently defined conventional
size-Ramsey number.

## Mathematical argument

For any finite-edge undirected simple graph H, let A(H) be the set of natural
numbers m for which there is an undirected simple graph G with exactly m
edges and a copy of H in G. A copy means an injective map of vertices
preserving adjacency; it need not preserve nonadjacency. Thus it is ordinary
subgraph containment, not necessarily induced containment.

The set A(H) is nonempty: take G = H and the identity map. Consequently its
least natural element exists and is attained by a genuine host graph.
Every copy of H in G maps each unordered edge {u,v} to {f(u),f(v)}.
Injectivity on vertices implies injectivity on unordered edges, so
|E(H)| <= |E(G)|. Taking H itself as host gives the opposite inequality.
Therefore the containment minimum equals |E(H)| exactly.

Take P_n to be the path on n vertices, indexed by 0,...,n-1, with edges
between consecutive indices. For n = k+1, its unordered edges are exactly
{i,i+1}, for i = 0,...,k-1. These edges are distinct, so there are k of them.
The empty path has no edges. Hence the minimum is n-1 for every natural n,
with natural subtraction at n = 0.

For n >= 1 its normalized value is (n-1)/n = 1 - 1/n, which tends to 1.
Uniqueness of a limit in the real numbers implies that it cannot tend to 3.
If there were any real sequence epsilon_n tending to zero and satisfying
the claimed identity minimum(P_n) = (3 + epsilon_n)n for all sufficiently
large n, division by n would force the normalized minimum to tend to 3.
This contradiction negates the full displayed asymptotic assertion.

If P_n is instead indexed by its number of edges, it is the graph denoted
P_(n+1) above. The formal theorem `pathMinimum_succ` proves that its minimum
is exactly n. Its normalized value is therefore exactly 1 for n > 0; the
same coefficient 3 is false under that convention as well.

The source's further sentence attributing the constant 3 to a limit of
named universal networks is not needed. Whatever additional intended
explanation it has, the quantitative equality it is intended to justify
is already false under the source's explicit definition.

## Formal correspondence

All mathematical declarations are in `Conjecture2187.lean`, within the
namespace `Conjecture2187`.

| Source notion | Formal object or theorem |
| --- | --- |
| A graph | Mathlib `SimpleGraph`, undirected and loopless |
| An edge | A member of `SimpleGraph.edgeSet`, an unordered pair (`Sym2`) |
| Containing H | `Contains H G`: an injective Mathlib graph homomorphism |
| A possible edge count | `Attainable H m`: existentially quantified host vertex type and graph, with a finite edge set, a copy, and edge count m |
| Existence of candidates | `attainable_self`, `attainable_nonempty` |
| The minimum number of edges | `minimumEdges H`, defined by `Nat.find` on the proved nonempty predicate |
| The minimum is attained | `minimumEdges_attained` |
| Leastness among all candidates | `minimumEdges_le` |
| Exact general containment minimum | `minimumEdges_eq` |
| The path P_n | Mathlib `SimpleGraph.pathGraph n`, on `Fin n` |
| The path's exact edge count | `pathGraph_card_succ`, `pathGraph_card` |
| R-hat(P_n) under the printed definition | `pathMinimum n` |
| Exact value n-1 | `pathMinimum_eq` |
| Alternate edge-count indexing | `pathMinimum_succ` |
| (3+o(1))n | `ClaimedAsymptotic`: there exists epsilon : N -> R tending to zero, with the equality eventually in n |
| Actual normalized limit | `pathMinimum_ratio_tendsto_one` |
| Failure of the proposed normalized limit | `pathMinimum_ratio_not_tendsto_three` |
| Full negation of the asymptotic assertion | `conjecture_false : Not ClaimedAsymptotic` |

No desired conclusion is used as a definition. In particular, neither n-1
nor an explicit path-edge formula defines the extremum. It is derived
from the independently defined set of all admissible finite edge counts.
`Nat.find` supplies both an attained witness and the minimum property.

Host graphs may have infinite vertex sets; only their edge sets are
required to be finite when recording a natural edge count. Infinite-edge
hosts cannot improve a finite attained minimum. This does not exclude any
candidate capable of lowering the result. The universal edge-injection
lemma also permits arbitrary universe levels. The extremum's existential
vertex type is in Lean's `Type`, as is usual for a set-sized mathematical
model; it imposes no cardinality bound on the vertex set.

The formal assertion is intentionally eventual: changing finitely many
terms does not affect little-o. It therefore also refutes the stronger
reading that the equality must hold for every n. The value at n = 0 and
Lean's convention for division by zero play no role: every ratio
calculation used in the limiting argument is eventually restricted to
n >= 1.

## Verification and reproducibility

Toolchain: Lean 4.19.0. Mathlib revision:
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
`lake-manifest.json` is byte-identical to the supplied neutral dependency
manifest, with SHA-256
`23184bd96e9aba720427b594e1312235abf64aea733dce75b0cf63c33e424db1`.
Its root-package metadata is inherited from that neutral input; the
actual project name and build targets are defined in `lakefile.toml`.

The development environment initially linked the supplied standard
packages for source replay. Before running the full project build, those
links were replaced with private copy-on-write clones inside the author's
project. No shared dependency was modified. Frozen sources exclude all
dependency copies, compiled objects, and other build artifacts.

From the project directory, with the specified toolchain and dependencies:

```text
lake build
lake env lean -DwarningAsError=true Conjecture2187.lean
lake env lean -DwarningAsError=true AuthorAudit.lean
```

The full project build and both warnings-as-errors replays passed.
`AuthorAudit.lean` checks every declaration whose originating module is
`Conjecture2187`, including private and generated declarations. It rejects
owned axioms, unsafe or partial definitions, and transitive use of any
axiom except `propext`, `Classical.choice`, and `Quot.sound`. It also prints
the principal definitions, theorem types, and theorem axiom sets. The
audit is a verification command, not an additional mathematical premise.

The final outputs and command exit codes are preserved under `logs/`.
One earlier project build failed because an audit-local variable lacked
an explicit Boolean type. That checking-code error was repaired before
the successful build and replay; `logs/lake-build-initial.log` preserves
the failed draft output. Initial mathematical development also involved
ordinary elaboration fixes, all resolved in the verified source.

No numerical experiment, external mathematical computation, randomized
test, or non-Lean mathematical source code is required. Arithmetic and
finite-set reasoning are proved by kernel-checked Lean terms. The
successor-path counting lemma was developed in a clean same-problem
auxiliary context and then incorporated and independently rechecked in
this complete project. No earlier solution or other conjecture was used.

This author package establishes a disproof of the written quantitative
claim. It does not contain publication artifacts, a submission decision,
or an assertion about eligibility; those are outside the author stage.
