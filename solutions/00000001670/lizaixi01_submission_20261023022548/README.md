# Disproof of 00000001670: incompatible real characterizations

The source simultaneously specifies P3 = 0.918 and P3 = (2/pi) arctan(sqrt(2)). Mathlib's actual real sqrt, arctan and pi give the latter < 2/3. It differs by more than 1/4 even from every value that rounds to 0.918 to three decimals. Lean proves the complete analytic chain and rules out both interpretations for every real P and every sequence of real constants at index 3.

This refutes the explicit necessary numerical conjunction. It does not identify the genuine random-graph constant, assume a probabilistic limit theorem, or refute the independent asymptotic and concentration statements.

Closed [PR 189](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/189) by orionsheep already observed the same numerical inconsistency in prose. Its [review](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/189#issuecomment-5965633103) rejected the formal proof because Lean contained only natural-number trivia, with none of the real analytic chain. This submission repairs those missing steps and covers rounded decimals. The elementary observation is attributed, not claimed as new.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. New Main build, ten transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF, receipts, logs and exact hashes accompany the submission. No sorry, native_decide or added axiom. OpenAI Codex assisted; a separate supervising Codex agent reviewed source, report and PDF. This is AI review, not human certification. Organizer acceptance is pending.
