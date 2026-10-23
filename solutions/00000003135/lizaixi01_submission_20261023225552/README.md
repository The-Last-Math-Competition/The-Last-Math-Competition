# Problem 00000003135

The literal claim for an unrestricted nilpotent Lie group fails for the actual discrete real Lie group C2. Its true tangent Lie algebra is zero and its coadjoint orbit quotient is nonempty and a subsingleton. Its full unitary dual has two provably distinct classes. Thus there is no bijection.

The source states no connectedness or simple-connectedness assumption. This submission does not refute the connected simply connected Kirillov theorem and does not interpret the undefined extra measure phrase. The group is an ordinary zero-dimensional real Lie group; no finite-field Lie-ring orbit method is substituted.

## Complete objects and proof

- Multiplicative (ZMod 2), with actual group law/cardinality and nilpotence.
- Genuine discrete charts, real smooth manifold and smooth group operations, compactness, Hausdorff and second countability.
- Mathlib GroupLieAlgebra and its standard Lie structure, finite dimension zero, actual derivative of conjugation and its dual coadjoint action.
- The actual quotient by the coadjoint orbit relation, proved nonempty and subsingleton.
- The full type of strongly continuous irreducible unitary representations on arbitrary nonzero complex Hilbert carriers in a fixed universe. Unitary equivalence uses actual surjective complex-linear isometries, including between different carriers.
- Actual trivial and sign representations on the complex Hilbert line. All complex subspaces are zero or whole, proving irreducibility. Every purported unitary intertwiner contradicts injectivity at 1 and -1.
- Distinct classes in the full representation quotient exclude a bijective orbit correspondence. No classification or assigned count for the rest of the unitary dual is assumed.

report.tex and report.pdf give the argument. The complete lean/Main.lean has 51 explicit declarations and the audit covers all 89 namespace declarations, including generated structure/auxiliary declarations. The imported namespace is enumerated again by Check.lean. No sorry, native_decide or extra axioms.

## Reproduction

Pinned Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all dependency revisions are included. Run from lean/:

    ./verify.sh

The four gates are version, new root build, warning-as-error all-declaration axiom/coverage check, and official full fresh-kernel replay. See VERIFICATION.md and evidence/ for actual commands, logs, hashes, execution data and all observed thread masks.

The full original bilingual source is in SOURCE.md. Initial and final all-state eligibility checks accompany the package. Organizer acceptance is pending. This is selective production research, not a controlled efficiency experiment.

Primary scope reference: Fuchs–Kirillov, https://armj.math.stonybrook.edu/Articles/250708-Fuchs/index.html, Introduction.
