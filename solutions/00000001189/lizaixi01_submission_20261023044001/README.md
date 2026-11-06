# Disproof of 00000001189 under its printed fixed-dimension definition

The source defines minimal support as a minimum of natural fixed-space dimensions, then requires support n^2 - 1. On actual SL2(F2), the genuine minimum is zero and cannot be three. This is an internal incompatibility in the printed definition and necessary numerical clause, not a theorem about a different codimension or adjoint support invariant. No n=1 boundary case is used.

Lean uses the actual SL2(F2) natural action, actual linear kernels and subgroup closures. It proves that common fixed space equals the fixed space of the generated image. The actual transvections U and L generate the full group by Mathlib's transvection generation theorem and F2 coefficient cases. Their common fixed space is zero, and each fixed dimension is at most one. The genuine set of generating-pair fixed dimensions is nonempty, contains zero, and has zero as an attained minimum before its infimum is evaluated. For every alternative nonempty family of actual natural-image subgroups, the fixed-dimension minimum is at most two as well.

This refutes the necessary support formula and hence the original conjunction. It does not deny generating-pair existence, Singer-cycle constructions, or an alternative support convention replacing the source's definition. The full bilingual source is preserved.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, every theorem's transitive axiom audit, and full official leanchecker --fresh Main replay are required. Full LaTeX/PDF and source-bound logs and receipts accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review source/report/PDF; organizer acceptance is pending.
