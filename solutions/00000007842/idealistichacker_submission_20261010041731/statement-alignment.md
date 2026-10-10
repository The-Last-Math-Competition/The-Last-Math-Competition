# Exact statement-alignment review map

## Frozen source

Both languages are in source.md, raw SHA-256
09751ed8def1feb0f573fb27567c1aba7f7f43682ca4419240f03d70c1fb0c70;
Git blob075b190a8cb157c3cbb46db832e7ddc4e64ada51.

## Source-to-proof map

| Required source fragment | Mathematical meaning | LaTeX | Lean definition/proof |
|---|---|---|---|
| displayed theta=E[T_blanket]/E[T_cov], shared by both languages | real-valued ratio where defined | Section1 | expected_time_ratio_obstruction; source_negation_half_log; source_negation_log_quotient |
| theta(G) in[4/3,4] for every graph | in particular theta(G)>=4/3 for every eligible sampled graph | equation(1) | LowerBound; graph_indexed_obstruction substitutes theta(sample n omega) |
| theta concentrates to log3/2 on tree-like graphs | every positive tolerance neighborhood has probability tending1 | equation(2) | ConcentratesTo uses actual measures and Filter.Tendsto, not Boolean data |
| unparenthesized log3/2 | natural log: cover BOTH (log3)/2 and log(3/2) | lemma1 | half_log_three_le_one; log_three_halves_le_one |
| conjunction of interval, endpoints, concentration and branching statements | full source implies interval-lower-bound AND concentration; not equivalence | Sections1-2 | NumericClaims; source_negation_half_log and source_negation_log_quotient prove closed negations of these necessary conjunctions |
| universal lower bound with target<=1 | theta-a>=1/3, so1/6 neighborhood is empty | theorem1 | empty_neighborhood |
| probability of empty event cannot tend1 | zero probabilities for every n; uniqueness of real limits contradicts0=1 | theorem1 | zero_neighborhood_probability; no_concentration_below_one |

## Why the original quantity is not replaced by a toy model

The negation is proved for EVERY possible real function theta, and the exact ratio
of two expected-time functions is explicitly substituted. This is stronger than a
proof for the particular random walk definition. No computed blanket value,
expectation existence or probabilistic runtime model is used as an unproved premise:
the ORIGINAL conjecture itself supplies its universal real lower-bound assertion.
For a finite connected graph family where both expectations define real ratios,
that assertion specializes directly to every graph in the family.

A random graph family can be represented by sample n omega in a graph-indexed domain
and a probability measure law n. The original all-graphs bound yields pointwise
LowerBound on this substitution. The same proof applies to every sampling law;
therefore any narrower tree-like condition is irrelevant to the contradiction.
The theorem is proved for arbitrary measures and maps, a SUPERCLASS of the legitimate
probability model; there is no nonemptiness inference from this superclass. It
shows that the two supplied assertions are incompatible for EACH such model.
For actual probability measures the event definition is exactly the usual one.

## Boundaries and ambiguities handled

- Natural logarithms are the standard convention; both conventional parentheses
  readings are covered by separate theorems. No decimal approximation is a premise.
- The English and Chinese surrounding prose differ in the introductory description
  of times, but both DISPLAY the same ratio and both contain the same incompatible
  numerical clauses. The proof uses only those common clauses.
- Excluding disconnected graphs or graphs where the ratio is undefined does not
  rescue the numerical conjunction on any valid sampled graph family.
- We do NOT assert the true interval, endpoint attainability, branching threshold,
  or which individual clause must be amended. Refuting a necessary conjunction is
  enough; strengthening it with other clauses cannot make it true.
- There is no artificial graph, hard-coded Boolean assertion, assumed nonempty
  efficient-system class, fake probability table or unproved decision bridge.

## Probability-definition and witness extraction bridge

`ConcentratesTo` is only the BROADER necessary neighborhood-mass condition for
arbitrary measures. `ConcentratesInProbability` is the standard neighborhood
formulation with explicit IsProbabilityMeasure for each law and Measurable for
each real random variable. The projection is mechanically proved, and the two
source_probability_negation theorems negate the lower-bound conjunction with this
normalized measurable probability formulation. Thus source-facing terminology does
not infer normalization merely from an imported module.

For varying n use a common space of all eligible finite labelled graphs (with the
discrete sigma-algebra), laws supported on the appropriate size, and the identity
sampling map. Each size has finitely many such graphs; arbitrary statistics are
measurable on the common discrete space. Equivalently a common measurable disjoint
union accommodates size-specific sample spaces. No law is calculated or fabricated.

The source is read as asserting an actual concentration phenomenon. Its interval
clause and concentration clause supply the witnesses/properties used in the kernel
negation. Tree-like restrictions can then be dropped because all sampling maps are
excluded under that interval bound. A changed reading involving only universal
quantification over an unspecified EMPTY class is not what is being refuted.
