# Disproof of 00000004271: no finite-support approximation of rational doubling

The actual additive group Q is divisible and doubling x -> 2x is a nonidentity automorphism. Its only automorphism with finite moved-element support, finite defect image, or a finite-index subgroup fixed pointwise is the identity. All three facts and their subgroup/image bridge are formally proved.

For every true metric on Q, evaluating at x = 1 gives a fixed positive uniform approximation error dist(1,2). For every true metric on Aut(Q,+), the fixed positive distance from identity to doubling likewise prevents arbitrary approximation. More generally, for every T1 topology on the actual automorphism group, doubling is outside the closure of the singleton candidate set. This includes genuine extended metrics whose values may be infinite. The source leaves the subgroup-index metric undefined; the proof covers all genuine metrics and T1 topologies instead of choosing a new formula.

The group-theoretic finitary definition is [Dardano and Rinauro, arXiv:1403.4193v4, Introduction, pp.1-2](https://arxiv.org/abs/1403.4193v4), under that version's exact title *The group of inertial automorphisms of an abelian group*. Lean constructs the actual defect homomorphism and fixed AddSubgroup, checks the actual finite-index condition and proves the image/index equivalence on Q. No external equivalence theorem is inserted as an axiom.

The approximation necessary clause is refuted; no independent optimal exponent is computed. A nonseparating pseudometric or basis-relative finite-rank linear change is a different notion, not claimed to be refuted by this submission.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, twenty-two transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF and source-bound receipts accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review the source/report/PDF; organizer acceptance is pending.
