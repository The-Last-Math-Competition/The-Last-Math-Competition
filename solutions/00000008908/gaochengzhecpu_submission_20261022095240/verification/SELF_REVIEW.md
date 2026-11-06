# Author-agent adversarial self-review: 00000008908

Verdict: PASS

# 8908: author proof and adversarial review

Status: mathematical proof complete; final executed validation and hash below. Parent must still perform its own semantic review, fresh rebuild, LaTeX/PDF and publication. No independent reviewer is claimed.

## Exact scope

The English original specifies a monotone chain for Lovasz theta with endpoints the independence number alpha(G) and the clique number omega(complement G). These endpoints in fact coincide for every graph. On the actual simple five-cycle C5 both equal 2, but the full standard theta semidefinite program has value at least 5041/2257 > 2. Thus theta cannot belong to such a monotone chain in either direction. The Chinese text abbreviates the endpoint ambiguously; this disproof follows the English explicit clique-number endpoint and says so. Replacing it by the chromatic number of the complement produces the familiar valid sandwich theorem, which is a different statement and is not disproved here.

Only a strict lower certificate for theta is needed. We do not claim that the rational witness is optimal or that theta equals its objective. We do not need to formalize the familiar exact sqrt(5) value.

## Standard definition checked against a primary source

L. Lovasz, *On the Shannon Capacity of a Graph*, IEEE Transactions on Information Theory 25(1), 1979, pp. 1-7, Theorem 4 on printed/PDF page 3. Actual primary paper opened and read at:

https://people.orie.cornell.edu/miketodd/orie6327/lovshannon.pdf

Theorem 4 defines theta by maximizing the sum of matrix entries over ALL real symmetric positive semidefinite matrices with trace one and entries zero on edges. This is exactly the Lean `Feasible`/`feasibleValues`/`theta` program. The author-paper identity is used to select the canonical standard definition; no external unproved numerical bound is used.

The parent separately opened the matching SDP in Goemans' ICM1998 survey, https://math.mit.edu/~goemans/PAPERS/icm98.pdf , PDF page 3 / printed page 659. Either primary source can support the definition in the report.

## Self-contained rational proof

Let V=Z/5Z, and let G=C5, with neighbors differing by 1 modulo five. Form the integer circulant matrix B with entries B_ij=b_(j-i), where b=(-9,32,8,8,32). Its Gram matrix H=B^T B has diagonal 2257, entries zero on G's edges, and every other off-diagonal entry 1392. This follows by exact five-term products; no numerical eigensolver is involved.

Set X=H/11285, where 11285=5*2257. For every real vector z, z^T X z=||Bz||^2/11285 >=0, so X is positive semidefinite. It has trace one and the required edge-zero entries. Each row sums to 5041/11285, hence the SDP objective is 5041/2257. The difference from 2 is 527/2257>0.

The feasible set is genuinely nonempty because it contains X. It is bounded above in objective by 5 for ALL its matrices, not merely the witness. Indeed, positive semidefiniteness tested on e_i-e_j gives 2Y_ij <= Y_ii+Y_jj for every pair i,j. Summing these 25 inequalities gives 2 sum_ij Y_ij <= 10 trace(Y)=10. Thus its real supremum is well-defined and at least the witness value.

The actual complement of the five-cycle has maximum clique size 2. The pair {0,2} is a clique; checking all 32 vertex subsets shows no larger clique. Lean certifies both the existence and the universal upper bound using ordinary kernel `decide`, then uses Mathlib's genuine `cliqueNum` definition. Mathlib identifies the independence number with that complement clique number, so alpha(G)=2 as well. Both endpoints are 2 while theta(G)>2, proving the contradiction.

## Lean semantic map

- `graph`: Mathlib's actual `SimpleGraph.cycleGraph 5` on `Fin 5`, with its genuine complement.
- `Feasible G X`: full real Matrix.PosSemidef, trace=1, and every graph-edge entry zero. No circulant, rank or rationality restriction is imposed on the SDP domain.
- `feasibleValues`, `theta`: all feasible objective values and their real supremum.
- `B`, `witness`, `gram_entry`: explicit integer Gram factor and exact entries, normalized with 11285.
- `gram_psd`, `witness_psd`, `witness_feasible`: actual quadratic PSD proof, actual trace and all edge constraints.
- `entry_bound`, `objective_bounded`: all feasible matrices have objective at most 5, via actual PSD quadratic tests.
- `feasible_nonempty`, `feasible_bounded`: ensure the real supremum is a genuine nonempty bounded optimization value.
- `witness_row_sum`, `witness_objective`, `theta_lower_bound`: exact rational witness objective and its justified comparison to the full supremum.
- `complement_clique_upper`, `complement_maximum_pair`, `complement_clique_number`: actual Mathlib complement's maximum clique equals 2, not a proxy number.
- `independence_number`: Mathlib `indepNum` also equals 2.
- `counterexample`, `no_claimed_chain`: final strict violation of the alleged endpoint upper bound.

## Author adversarial review

1. **Theta has not been assigned the witness objective.** It is sSup of the objective over all PSD trace-one edge-zero real matrices. The witness is used solely to prove a lower bound.
2. **Supremum preconditions are proved.** The actual feasible set is nonempty and every feasible objective is <=5. No conditional-complete-order edge case is hidden.
3. **PSD is actual quadratic positivity.** B^T B is a Mathlib Gram matrix over the reals, scaled by a positive rational. Exact formulas, rather than approximate eigenvalues, certify it.
4. **Normalization and arithmetic:** Gram diagonal 2257, trace 11285, nonedges 1392, row sum 5041/11285, objective 5041/2257 and gap 527/2257 are all checked exactly. The independent Python implementation reconstructs the same factor from its circulant definition.
5. **Edge versus nonedge convention:** X vanishes on the actual cycle edges, matching Lovasz Theorem 4. In any event C5 is self-complementary, but this fact is not relied on to excuse a convention mismatch.
6. **Actual endpoint definitions:** The complement clique number and independence number are Mathlib's finite maxima, connected by its theorem, with a size-two clique and a universal subset upper certificate.
7. **Finite certificates use only the kernel.** `decide` enumerates a five-vertex graph / 32 vertex subsets. No native_decide, external solver or untrusted oracle is used.
8. **Language/scope:** The English source explicitly says clique number of the complement. The report must not say that the standard chromatic-number sandwich theorem is false. Since the two claimed endpoints coincide here, either monotone order of those endpoints fails.
9. **No optimality overclaim:** The exact standard theta value is unnecessary; the rational lower bound >2 is sufficient. No unsupported upper bound, eigenvalue formula or attainment claim is included.
10. **Trust and dependencies:** Lean4.19 / official Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b. Final strict checking, full build and auxiliary script must be actually run; final hashes and logs identify the checked artifact.

No TeX/PDF or PR has been created by this agent. Parent owns the final paper and submission.

## Final frozen source and actual validation

Main.lean SHA-256: `36281b8a4e00b73151244703a2b595d124b5389445a9f502d7bfed21d03c71b2`.

Final checks all returned exit code zero: strict `lake env lean -DwarningAsError=true Main.lean` 20.750 seconds; full `lake build` 21.907 seconds; exact independent `verify.py` 0.031 seconds. Every printed theorem uses only standard propext, Classical.choice and Quot.sound. Full commands, working directories and timings are in `8908-result.json`, and raw outputs in `8908-strict.log`, `8908-lake-build.log`, `8908-python.log` in this directory. This hash is frozen for parent review.


Reviewed artifact hashes:

- Main.lean: `36281b8a4e00b73151244703a2b595d124b5389445a9f502d7bfed21d03c71b2`
- main.tex: `7a574c0e87e1d2819ed7960e3639ac34625f3275a946aacf997e16286a3f6e01`
- main.pdf: `83fb9398e705234b96e419b5b568489982717d7fd0bec70c5187fa37162d90ba`
- SOURCE.md: `5940d1502259e2fea00b10d0484a0a5dbd71304db7f4ec45c0d2f40c76a5d4e5`
