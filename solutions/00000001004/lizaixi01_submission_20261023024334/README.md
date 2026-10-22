# Disproof of 00000001004: a larger cap in the actual PG(6,q)

For every finite field K of odd characteristic, choose a nonsquare d. The actual projective points represented by (1,x,y,x^2-d*y^2,s,t,s^2-d*t^2) form a q^4-point cap: anisotropy and the quadratic mixing identity exclude three distinct collinear points. Lean proves the normalized projective embedding, injection, cardinality, and standard no-three-collinear condition using Mathlib Projectivization.IsCollinear.

The true maximum is defined by a largest-cardinality member of the finite family of all actual caps, whose existence and universal maximality are proved. Thus m2(6,q) >= q^4. On arbitrarily large odd prime fields, this contradicts the source's fixed n = 6 claim 2*q^3*(1+O(q^-1)). The final theorems negate an actual Mathlib IsBigO O(q^2) error and directly negate the relative expansion, with full eventual and error-function quantifiers. No finite example replaces the asymptotic claim.

This elementary quadratic/product construction is classical; see [Elsholtz and Lipnik, Introduction and Related Work](https://arxiv.org/abs/2211.09772). Their discussion includes stronger bounds. This package proves the weaker sufficient q^4 bound without assuming a published cap-size theorem.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. New Main build, seventeen transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF, source-bound receipts, logs and hashes accompany the submission. No sorry, native_decide or extra axiom. OpenAI Codex assisted; a separate supervising AI agent reviewed source/report/PDF. Organizer acceptance is pending.
