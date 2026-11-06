# Counterexample for 00000003161: unrestricted exact sparse recovery

For every ambient dimension N>=3, the actual 2-by-N real matrix with columns (1,j) recovers every vector with at most one nonzero coordinate, including zero, by a total decoder. Its actual minimum measurement count is at most 2. For every positive dimension-independent C, some N satisfies 2<C log N, so this minimum violates the claimed C k log(N/k) necessary count at k=1.

The source defines the filtered support, proves the complete one-coordinate representation, proves measurement injectivity on that entire class, constructs a total classical decoder, and defines the true least successful count using Nat.find. It does not substitute an abstract injection or assign the minimum a numerical value.

This concerns the literal exact real-arithmetic recovery statement y=Ax with no noise/stability/precision or decoder restriction. It does not refute lower bounds with additional assumptions. [Ardestanizadeh--Cheraghchi--Shokrollahi, Bit Precision Analysis for Compressed Sensing](https://arxiv.org/abs/0901.2147) explains the distinction between 2k exact Vandermonde measurements and additional precision costs. The undefined noise-sphere packing clause does not specify those missing mathematical assumptions.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new Main build, eleven transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete report/PDF and source-bound receipts accompany the project. No sorry, native_decide or added axiom. OpenAI Codex assisted, with a separate supervising Codex agent reviewing the source/report/PDF. This is AI review, not human certification. Organizer acceptance is pending.
