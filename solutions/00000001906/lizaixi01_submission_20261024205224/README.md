# TLMC 00000001906: a fixed real-line interval excludes square-root growth

This submission disproves the printed finite-coefficient square-root asymptotic for the conventional unweighted **rough real-line** Rubio de Francia square function. The source does not specify a domain or Fourier normalization; this standard interpretation is stated explicitly in the report. It uses native Lebesgue measure and the transform exp(-2πixξ), inverse exp(2πixξ).

For every genuine family of admissible constants C(p), the Lean proof derives C(p) ≥ p/(8πe) for every real p ≥ 2. Thus native `Asymptotics.IsBigO atTop C Real.sqrt` fails, and C(p)/sqrt(p) cannot converge to any finite real coefficient. It does not assign an optimal constant, prove a sharp linear coefficient, dispute Rubio de Francia boundedness, or replace the operator by a smooth, martingale or periodic square function.

The frequency interval is fixed at [0,1]. The input is the actual indicator of [-R,R], with R=exp(p). Native Fourier and inverse Fourier definitions, integrability and genuine Fubini yield the kernel integral. The actual imaginary part is an integral of (1-cos(2πt))/t. A proved integration-by-parts bound gives a logarithmic lower bound on the real interval [R+1,R+2], whose native Lebesgue measure is one. Native `eLpNorm` monotonicity and the true indicator norm yield the linear bound. An assumed finite admissible bound explicitly gives native `MemLp` for the continuous output, so no totalized infinite-norm/default-zero argument is used.

`Main.lean` includes the real finite-family rough square function and its singleton reduction, all Fourier/integration/norm bridges, and the real-parameter big-O and finite-ratio-limit contradictions. The two primary references support the conventional operator definition; their asymptotic theorems are not imported as axioms. Garg et al. Theorem 1.1 is lacunary, and the later arbitrary-interval discussion concerns the circle. No transference or dilation theorem is invoked by this direct real-line construction.

The entire original bilingual source is in `SOURCE.md`. The mathematical report is `report.tex` / `report.pdf`, with the complete pinned Lean project in `lean/`. Reproduce from `lean/`:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

Alternatively, run `lean --version`, then `./verify.sh` for the remaining three commands. Lean is pinned to 4.33.0 and Mathlib to db584cd6d46c92f209a44c0f1c829460d327499d. The audit calls ordinary `#print axioms` for every actual owned declaration, including private/generated names, and checks exact environment coverage. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There is no `sorry`, `native_decide`, or extra axiom.

`evidence/` retains full command logs, source-bound verification and execution receipts, all actual CPU-mask samples, qualification, PDF and independent semantic review. `SHA256SUMS.json` binds every other personal-package file. Production timings are diagnostic, not evidence of controlled research-efficiency improvement. Organizer review is pending.
