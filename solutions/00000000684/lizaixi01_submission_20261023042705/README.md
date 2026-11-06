# Disproof of 00000000684 in the standard Kauffman virtual-group model

The actual round circle in C x R (real three-space) has an injective planar projection, no classical or virtual crossings, and a standard Wirtinger group isomorphic to Z. The group is genuinely finitely generated and infinite, while the diagram is classical. This contradicts the necessary forward implication of the proposed iff.

Lean derives the crossing-preimage set from the actual circle map and proves it empty. Its complement is explicitly homeomorphic to Circle; its actual connected components give exactly one arc. The actual crossing index is empty, so every crossing-relator assignment has empty range. The resulting actual PresentedGroup is proved isomorphic to the free group on this arc type and then to Multiplicative Z. The actual spatial embedding and its plane projection and zero height are supplied. No dummy classical=True predicate or unrelated one-generator presentation is used.

The precise standard model is [Kauffman, Virtual Knot Theory (1999), Section 4, printed pp.671-672](https://homepages.math.uic.edu/~kauffman/VKT.pdf). The report distinguishes this crossing-free formalization from a general virtual-knot classification, full Reidemeister invariance, complement fundamental-group identification, or other extended virtual groups. ClassicalRealization is a sufficient actual plane realization for this subclass, not a definition of all nonclassicality.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, transitive axiom audits and full official leanchecker --fresh Main replay are required. Full LaTeX/PDF, source-bound receipts and hashes accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review source/report/PDF; organizer acceptance is pending.
