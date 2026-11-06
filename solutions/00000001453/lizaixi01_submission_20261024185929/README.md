# Problem 00000001453: the printed normalized-deficit CLT fails in dimension one

For the genuine compact convex body `[0,1]` in the one-dimensional real vector space, take independent uniform samples and their actual convex hull. The native volume deficit has mean `2/(n+1)`, second moment `6/((n+1)(n+2))`, and positive variance `2(n-1)/((n+1)^2(n+2))` for every `n>=2`. The true standardized laws have no mass below `-3`, whereas the standard Gaussian has positive left-tail mass. Both native weak convergence and the exact ordinary Gaussian CDF convergence criterion fail.

The source does not impose `d>=2`. This submission addresses only its printed normalized-deficit CLT conjunct under the usual positive-dimensional convex-body and actual mean/standard-deviation normalization conventions. It does not contradict a corrected `d>=2` theorem or assign values to the unspecified sphere constants. The variance-rate clause is not claimed false. `SOURCE.md` contains the complete original bilingual statement at the recorded upstream commit.

The formal model uses sample sizes `k+2` for all natural `k`. `uniform` is normalized Lebesgue restriction on the actual body, `sampleMeasure` its finite product, and the coordinate functions are proved independent and uniform. `polytope` is the native finite convex hull; its interval and volume identifications are proved. Marginal and joint tail probabilities come from actual coordinate rectangles. A proved Fubini identity computes every moment used, including the cross moment. `deficit_variance` is a theorem about native variance, not a prescribed value. `standardizedLaw` is the actual native pushforward probability measure. The convergence obstruction uses native Portmanteau and the genuine native standard Gaussian. No distribution or moment identification is assumed from the literature.

The report cites Vu for the customary sampling model and centered/variance normalization, and Chen for elementary order-statistic background. All mathematics needed for the counterexample is proved in Lean; these references are not extra axioms. There is no external geometry/GIT/model identification boundary in this submission.

## Reproduce

Lean `4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From `lean/`:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

After the version command, `./verify.sh` runs the remaining three commands. `Check.lean` uses ordinary `#print axioms` for the complete owned namespace, including generated/private declarations, and checks explicit target coverage. The only permitted foundation axioms are `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `native_decide`, or additional axiom.

Original source-bound command/axiom/fresh-kernel receipts and actual thread-mask observations are included in `evidence/`. The package manifest binds the report, PDF, complete pinned Lean project and receipts. Production timings are diagnostic observations and are not controlled causal research-efficiency evidence.
