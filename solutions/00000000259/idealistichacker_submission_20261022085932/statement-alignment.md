# Statement Alignment: Conjecture 00000000259

Both complete languages are preserved in `source.md`. The printed statistical
population is primes p=1 (mod 4), not composite fundamental discriminants. The
final theorem refutes the required density clause under the explicitly disclosed
standard density **relative to that prime class**.

| Source object or clause | Actual mathematical / Lean object |
| --- | --- |
| Prime p=1 mod 4 | `PellDensity259.Eligible p := p.Prime and p%4=1` |
| Negative Pell solvability | `PellDensity259.Solvable p`, actual existential integer witnesses |
| All eligible primes solve the equation | `PrimePell259.negative_pell_of_prime_one_mod_four`, positive Pell minimality and integer descent |
| Reference population below N | `eligiblePrimesBelow N`, actual filter of `Finset.range N` |
| Successful primes below N | `successfulPrimesBelow N`, same eligibility plus actual solvability |
| Relative density | `relativeDensity N`, real quotient of actual cardinalities |
| Positive denominator | Eligible prime 5 belongs for N>=6; no use of zero-division to obtain the limit |
| Infinite product over k>=2 | `factor n = 1-(1/2)^(n+2)`, genuine real `tprod` |
| Product convergence | `product_multipliable`, derived from summable geometric deviations |
| Claimed constant C | `claimedConstant := 1-tprod factor`, proved in [1/4,7/16] |
| Asymptotic negation | `not_claimed_relative_density`, closed `Not (Tendsto ... atTop (nhds claimedConstant))` |

The universal prime-radicand solvability theorem implies equality of the counted
sets for every N. Since the ratio is one for N>=6, its limit is one. Uniqueness
of real limits and C!=1 refute the density clause. The final theorem assumes no
external solution-existence, product-bound, or density premise.

This is a necessary-clause refutation of the printed conjunction, not an
equivalence with every introductory assertion. The wide-class-number sentence
is not assumed, and no class-number condition is silently inserted into the
prime population. The proof does not claim its denominator is the only possible
density convention. It advertises neither density among all primes nor natural
density among all integers, which would be different formal claims. It must not
be represented as refuting a different literature version of Stevenhagen's
conjecture for composite squarefree radicands.

The exact scalar certificate 8890182^2-109*851525^2=-1 corrects an earlier
bounded-search inference. It is not the universal or density proof. The old
research theorem was correct and was not modified to make a bounded search pass.

Original conjectures and organizer metadata remain untouched. Separate core and
paper preflights are not automatically final package approval: the frozen hash,
exact package reproduction, PDF, and all theorem types/axioms must be reviewed
together in final `review.json`.
