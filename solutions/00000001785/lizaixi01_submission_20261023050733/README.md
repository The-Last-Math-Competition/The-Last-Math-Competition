# Disproof of 00000001785: incompatible step-function and formula clauses

The source explicitly requires a step function C(c) and the formula C(c)=max(1,2c)*pi. On the legitimate positive parameter window (1/2,1), this formula is injective and has uncountable image. Genuine finite disjoint-interval indicator sums have finite restricted image; genuine countable disjoint interval covers with constant values have countable restricted image. Both bridges are formally proved from actual representations, rather than renaming a range property Step.

The final statements quantify over every real function C. Restriction lemmas also explicitly exclude both representations on all positive parameters with the printed formula. Only positive c in (1/2,1) are needed. The proof does not compute an actual Ohsawa-Takegoshi optimum, assign it a formula, refute an independent extension theorem, or infer a jump from the word transition. If step function were replaced by piecewise-linear function, that would be a different statement.

The standard finite interval-indicator definition is fixed by L. Ryzhik, Stanford Math205A Fall2015 homework3solutions, problem1(i), p.1: https://math.stanford.edu/~ryzhik/STANFORD/STANF205-16/205A_hw3_sol.pdf . Countable interval-piece representations are separately treated as a more permissive alternative. The original bilingual source is included.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, all 15 theorem axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF, source-bound logs/receipts and SHA256 manifest accompany the proof. No sorry, native_decide or additional axiom. Worker and separate supervising AI agent reviewed source/report/PDF; organizer acceptance is pending.
