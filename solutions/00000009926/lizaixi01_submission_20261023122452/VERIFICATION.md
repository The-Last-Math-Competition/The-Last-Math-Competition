# Verification

The frozen source passed a new root build in a separate pinned Lean 4.33.0 project. Main was newly compiled, and dependency Git commits match the manifest.

- `lake build +Main`: exit 0, Main newly built.
- `lake env lean -DwarningAsError=true Check.lean`: exit 0; all 38 named targets (21 theorems plus 17 definitions/abbreviations). Standard allowed logical axioms only or no axioms.
- `lake env leanchecker --fresh Main`: exit 0, 245.5327 diagnostic WSL seconds. Full official kernel replay, not an independently implemented kernel.
- Both PDF pages rendered at 100 dpi and visually inspected by worker and separate supervising AI; no overfull boxes.
- Complete source scope, categorical classification proof, report and PDF reviewed by a separate supervising Codex agent.

Main SHA256: `d67acb4f8dec4a4ed22a9e9cbd4402f77cd65bcb1a05fb66dacc790249a40fbd`. Receipts bind source, commands, exits and log hashes. One bounded owned process group, CPU affinity 0,2, no owned residuals. This selective production case is not an additional experimental sample or an efficiency claim.

Actual persistence modules are vector-space-valued functors, with natural transformations and genuine natural isomorphisms. Skeleton gives the actual natural-Iso quotient and equality iff Nonempty Iso. The isoclass function is complete. A different constant invariant is proved distinct by the true nonisomorphism of constant zero and Q, using an actual component linear equivalence and injectivity. Their real finite set has cardinality2 and is complete, uniformly for all index categories and arbitrary subclasses. The true pointwise-finite-dimensional subtype and Nat2/Real2 preorder instances are explicitly handled. This refutes only the unrestricted any-two-invariant/at-least-three necessary clause. The constructed codomain is actual isoclasses and the construction is noncomputable. No numerical, discrete, computable, local, stable or rank-plus-undefined-degeneracy classification is asserted. Full bilingual source preserved, no prior same-ID PR found, no sorry/native_decide/extra axiom; organizer acceptance pending.
