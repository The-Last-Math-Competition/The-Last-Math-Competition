# TLMC 00000001911: the printed full Hilbert transform need not be L2 bounded

This submission disproves only the first printed **untruncated strong-L2** conjunct on the conventional Euclidean plane. The formula in the source has no outer cutoff. It does not refute the standard short-scale Stein problem, its weak-type formulation, or the undefined resonance-set clause. The entire original English and Chinese text is included in `SOURCE.md`.

The actual field is W(x,y)=(max(1,x),y), V=W/||W||. With the genuine Euclidean norm, W is 1-Lipschitz, its norm is at least one, and V is an everywhere unit, globally 2-Lipschitz field. A native smooth compact bump centered at zero, equal to one on the unit ball and supported in radius two, is converted to a genuine native Schwartz map and has native `MemLp` exponent two.

The proof defines actual integrals over epsilon <= |t| <= R. On the positive-width cone x >= 4, 0 <= y <= x, it proves genuine integrability and the joint limit as epsilon -> 0+ and R -> infinity. Eventual equality to an actual compact-interval integral proves that limit. The true value is at least 1/(2x). A genuine native `MemLp` function agreeing almost everywhere with those limits cannot exist: the actual volume-preserving complex/real-coordinate equivalence and Fubini would give an integrable row function dominating 1/(4x) on [4,infinity), contrary to native nonintegrability of the inverse function.

The final statement excludes every native continuous real-linear operator on native `Lp` exponent two that agrees almost everywhere on all real Schwartz tests with these actual full-PV limits. Such agreement is necessary for an L2-bounded extension of the printed full transform. The stronger intermediate obstruction already excludes any L2 representative for the single genuine bump, even without linearity or a norm estimate. No pointwise limit is assigned outside the cone, no divergent norm is totalized to zero, and no literature theorem is imported as an axiom.

Lacey and Li's arXiv:0704.0808v3 printed pages 1-2 explicitly use a finite outer scale and a weak-type Stein formulation; printed page 27 separately discusses the full transform. Those complete selected pages and their actual images were read. The report discloses this distinction prominently. The construction proves the counterexample directly, without a transference theorem or geometric identification assumption.

The complete pinned project is in `lean/`; the full mathematical report is `report.tex` / `report.pdf`. From `lean/`, run:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

Alternatively, run `lean --version`, then `bash verify.sh` for the remaining three commands. Lean is pinned to 4.33.0 and Mathlib to db584cd6d46c92f209a44c0f1c829460d327499d. The audit calls ordinary `#print axioms` for every actual owned declaration, including private/generated names, and checks exact environment coverage. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There is no `sorry`, `native_decide`, or extra axiom.

`evidence/` retains full command logs, source-bound verification/execution receipts and all actual CPU-mask samples, qualification, PDF and independent semantic review. `SHA256SUMS.json` binds every other personal-package file. Production timings are diagnostic, not evidence of controlled research-efficiency improvement. Organizer review is pending.
