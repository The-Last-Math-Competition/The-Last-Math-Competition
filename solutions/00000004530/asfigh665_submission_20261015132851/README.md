# Proof of Conjecture 00000004530

**Result: proved.** A two-vertex message-passing system with periodic damping gives an explicit family with one averaging step every `p` updates. Every algorithm has exactly the consensus states as fixed points and reaches consensus after at most `p` steps. The periods `p = 1` and `p = 2` have different trajectories from the same initial messages `(1, -1)`.

## Files

- `proof.tex`: complete English mathematical proof and formalization correspondence.
- `proof.pdf`: compiled, visually checked report.
- `lean/Main.lean`: self-contained Lean proof.
- `lean/lakefile.toml`, `lean/lean-toolchain`: reproducible Lean 4.24.0 project.

## Verification

Run from the `lean` directory:

```text
lake build
```

No third-party Lean packages or network downloads are required after installing Lean 4.24.0. The build has been run successfully. The theorem `Conjecture4530.conjecture4530` proves coincidence of fixed points, finite-time convergence from every initial state, and different physical message trajectories. The separate theorem `message_passing_identity` verifies the exact denominator-cleared convex damping rule on the two-node graph. The frequency schedule and update recurrence are also proved.

There are no proof placeholders, `native_decide`, or custom axioms. The axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope and semantics

Both source-language statements are existential and specify no alphabet, graph, or continuous frequency interval. This construction uses integer messages of equal parity and the explicit discrete sweep of averaging frequencies `1/p`, for positive integers `p`. These are actual local two-node message updates, not unrelated numerical assumptions. The half-damped average is always integral; there is no rounding. The state is fixed precisely when every scheduled update preserves it; each individual update and the update over a complete period have the same fixed-point set. Both trajectories have the same limit, but their sequences of iterates differ, as required.

The latest `origin/main` metadata and solution tree were checked before construction: both solved flags for 00000004530 were false and no solution directory was present. An all-state GitHub pull-request search for the exact identifier also returned no results. This submission modifies only its own directory.
