# Proof of conjecture 00000003527

For every normal ordinal function f, the actual fixed-point set is closed
in the ordinal order topology and unbounded. Mathlib's ordinal derivative d
is its normal increasing enumeration, with range exactly the fixed-point set.
The formalization verifies its initial, successor and limit recursions and
the equality d(ω)=sup_n d(n).

Separately, for every starting ordinal a, the least fixed point at least a
is nfp f a=sup_n f^[n](a). Its lower bound, fixed-point identity and minimality
are all proved. These two limit constructions are deliberately separated:
for the identity function, d(ω)=ω while nfp id 0=0. The source's ω-th term
of the fixed-point sequence is read as the ω-th term of the standard
increasing enumeration, rather than conflated with iteration of f from zero.

## Formalization and scope

```lean
theorem Conjecture3527.conjecture_3527_true : FixedPointClaim.{u}
```

`FixedPointClaim` universally quantifies every normal function on actual
Mathlib ordinals. It combines genuine `IsClosed`, `¬ BddAbove`, exact range
equality for the actual derivative, normality and all recursion clauses,
the ω enumeration limit, and the iteration formula and least-fixed-point
properties for every starting ordinal. A separate theorem gives a fixed
point strictly above every ordinal; `identity_limits` verifies the example
distinguishing the two constructions. All mathematical conclusions in the
paper are formalized.

This is a classical theorem verified using substantial existing Mathlib
results, not a claim to an original theorem or to a new library-independent
proof. FixedPoint supplies unboundedness, the exact derivative range and
normality, its recursion, and next-fixed-point iteration/minimality. Family
supplies the normal-function formula at ω. Topology supplies the normality /
strict-monotonicity-and-continuity equivalence; the new closure proof applies
the genuine continuous equalizer theorem to f and the identity.

## Reproduction and review

Lean 4.19.0; Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with public-Git pinned metadata.
In `lean/` run:

```text
lake env lean -DwarningAsError=true Main.lean
lake build
```

The author strict check passes with warnings as errors. The main theorem
and closure/range/ω/minimality axiom audits use only propext, Classical.choice
and Quot.sound. Compile `main.tex` with Tectonic or compatible LaTeX.
The coordinating agent performs the fresh project build and PDF inspection.
The author does not claim those later checks were already performed here.

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. Review mode: agent development with parent adversarial
review; no external independent review.

Both languages in the exact `SOURCE.md` were read. The parent fetched it from
upstream commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, checked that no
earlier PR or solution exists, and recorded its SHA-256 in the batch source
record. The source's statement is classical; no additional conjectural
assumption or numerical surrogate is used.
