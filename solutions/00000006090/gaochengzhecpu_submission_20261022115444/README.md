# Proof of conjecture 00000006090

On the same objective f(x)=x²/2 and initial value x₀=1, baseline gradient
descent uses step 1/2 throughout. For any prescribed m, a second method
uses 1/4 at step m, 2/3 at step m+1, and 1/2 elsewhere. Its iterate differs
only at index m+1. At that index the exact absolute-error gap is 2^(-(m+2));
from m+2 onward the two trajectories agree identically. Both tend to the
unique minimizer zero and have limiting successive-error ratio 1/2.

## Source reading and scope

The source itself describes the finite-scale distinction as finite-scale
behavior and pre-asymptotics. The proof realizes this with the actual
finite error curves of iterative algorithms. The source supplies no separate
operator or numerical definition for "finite-scale spectrum"; none is
invented here. Eventual equality of the entire trajectories is stronger than
simply assigning both algorithms the same asymptotic convergence-rate label.

The formal objective is a real function with an actual HasDerivAt proof.
The algorithm is a genuine recursive gradient-descent update using Mathlib
`deriv`. The proof verifies every step lies in (0,1), proves exact trajectory
formulas for all m and n, prefix and tail equality, exact finite error gap,
actual filter convergence to zero, and the actual limiting ratio of successive
absolute errors. No finite numerical table substitutes for an asymptotic claim.

The main theorem is:

```lean
theorem conjecture_6090_true : SeparationClaim
```

`SeparationClaim` quantifies over one objective, every chosen finite index m,
and actual step schedules and iterative trajectories. It includes the
gradient update, common initial value, valid positive steps, common limit,
common asymptotic error ratio, common prefix, finite discrepancy, and exact
common tail. The exact error-gap formula is additionally proved by
`error_gap`. All mathematical ingredients used in the paper are formalized.

## Reproduction and review

Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with public-Git pinned metadata.
In `lean/`:

```text
lake env lean -DwarningAsError=true Main.lean
lake build
```

Compile `main.tex` with Tectonic or a compatible LaTeX engine.
The author strict check passes. Main/bridge axiom audits use only propext,
Classical.choice, and Quot.sound.

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. Review mode: agent development with parent adversarial
review; no external independent review. The coordinating agent performs
the fresh project build and PDF inspection before deciding whether to publish.

The exact bilingual `SOURCE.md` comes from upstream commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`; current history/source records show
no prior PR or existing solution for this conjecture.
