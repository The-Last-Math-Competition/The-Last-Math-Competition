# TLMC 00000007730: a true third-moment obstruction to the universal free CLT rate

This submission refutes only the source's universal O(1/n) moment-convergence clause, which assumes centering, self-adjointness, freeness and bounded fourth moments but imposes no symmetry or vanishing third moment. The scalar case B=C and one-entry tuples suffice. It makes no claim about an even-moment restriction or the later cumulant/colored-Motzkin clauses. The complete bilingual source is in SOURCE.md.

The proof uses the native countable free product of C3 factors, its unique reduced words and actual embeddings. On the genuine Hilbert space lp(G,C,2), coordinate reindexing constructs bounded unitary left-regular operators and their group homomorphism. The native group-algebra lift is faithful because its action on the actual vacuum delta_e recovers every coefficient. Its true range is a native StarSubalgebra of bounded operators. The restricted vacuum functional is an actual positive, unital, bounded, tracial state. Traciality is proved on this regular star-algebra. Full scalar freeness is established for all lengths and all centered elements of the actual factor star-subalgebras using support extraction and the native unique-normal-form equivalence.

The actual variables Xi=lambda(gi)+lambda(gi)^* satisfy Xi^2=Xi+2, giving true moments 0,2,2,6 through order4. Yi=Xi/sqrt(2) are actual self-adjoint elements with identical full polynomial laws, mean0, variance1 and fourth moment3/2, including an explicit uniform bound. In the actual regular star-algebra the genuine standard normalized sum Sn=(sum_{i<n}Yi)/sqrt(n) has true third moment1/sqrt(2n), derived by evaluating the full mixed triple sum. No moment table or rate sequence is assigned as a definition.

The target is the genuine standard semicircle measure: Lebesgue measure restricted to[-2,2], with density sqrt(4-x^2)/(2*pi). Its total mass1 is proved by native integration and change of variables. Its cubic integrand is separately proved integrable and its third moment is proved0 by reflection. The actual complex discrepancy violates every eventual C/n bound, with all constants and starting indices quantified. This yields the native atTop Asymptotics.IsBigO negation. The general free CLT need not be assumed to prove these finite-sum and measure calculations.

The report identifies the concrete algebraic formulation of scalar noncommutative probability used here, following Novak's publisher-hosted notes. The Hilbert representation, genuine star-subalgebra, positivity/trace/freeness and actual semicircle measure are all proved in Lean; no additional identification axiom is supplied.

The project pins Lean4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. From lean/, run these four commands separately:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

lean/verify.sh runs the final three commands. Check.lean traverses the actual environment and uses ordinary #print axioms on every owned declaration, including generated names; only propext, Classical.choice and Quot.sound are allowed. Source-bound command logs, actual execution receipts, all sampled owned-thread masks, the reviewed LaTeX/PDF and a SHA256 manifest accompany the submission. Timings are production diagnostics, not controlled efficiency evidence. Organizer review remains pending.
