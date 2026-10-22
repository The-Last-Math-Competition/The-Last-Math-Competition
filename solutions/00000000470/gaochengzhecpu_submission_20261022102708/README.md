# Disproof of Conjecture 00000000470

For actual cycles with independent fair edge weights 1 or 2, the genuine spanning-tree polynomial has exactly one nonzero negative root on an event of probability tending to one. Its nonempty empirical angular measure stays at Kolmogorov distance at least 1/2 from uniformity.

## Scope

Refutes angular convergence even in probability, hence any vanishing O(v^(-1/2)) rate, for the supplied polynomial and a nondegenerate iid positive-integer weight law. Both discarding zero roots and including them with arg(0)=0 fail. No alternative polynomial or unspecified restricted weight model is claimed.

## Formalization

Lean uses actual Mathlib cycle graphs, proves vertex transitivity by rotation isomorphisms, and exhaustively bijects all genuine spanning trees with deleted original edges. The actual edge-weight sum and full tree polynomial factor as X^(W-2)(aX+b), yielding their actual root multiset with multiplicities. A full real-threshold CDF supremum gives the genuine Kolmogorov bound. The fair independent assignment law is normalized counting with every assignment probability equal to the product of coordinate masses. Exact mixed-event counts imply that the probability of a nonempty actual empirical measure with gap at least 1/2 tends to one for each zero convention and does not tend to zero. An exact supplementary Python enumeration checks all weights and actual trees for cycles of sizes 3 through 10.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
