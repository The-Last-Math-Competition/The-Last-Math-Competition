# Reproducing the Lean verification

This project uses **Lean 4.24.0**, the core standard library, and no external
packages or Mathlib. With that version of Lean and Lake on `PATH`, run:

```console
lake build
lake exe verify
lake env lean Conjecture564.lean
```

The last command also prints the axiom dependencies of the principal results.
There are no `sorry`, `native_decide`, or custom axioms. Closed finite arithmetic
is proved by `decide`, which is checked by the Lean kernel. Rational arithmetic
uses `decide +kernel` because core Rat marks some operations irreducible for
ordinary elaborator reduction; `+kernel` asks the kernel itself to reduce the
same proof term and does not invoke native execution.

`Conjecture564.lean` defines integer exchange matrices, their principal-coefficient
extensions, initial F-polynomials, and the first mutation by positive/negative
exponent products. It verifies the standard A2 Cartan companion and the full
4-by-2 principal extended matrix, proves the first-mutated polynomial equals
`1 + y_1` for all natural-number assignments, and evaluates it at all ones.
The file also constructs both simple reflections from the Cartan matrix. Their
product has order exactly 3 and characteristic polynomial t^2+t+1; a coefficient
calculation verifies (t-1)(t^2+t+1)=t^3-1. These calculations confirm the standard
A2 Coxeter data h=3 and exponents 1,2. The generalized Catalan number uses exact
`Rat` division, so the intermediate factor 5/2 is not truncated.

The formal proposition `A2DivisibilityClaim` is the universal A2 restriction that
any literal global conjecture must satisfy. `not_A2DivisibilityClaim` refutes it,
and `refutesEveryClaimCoveringA2` records the logical reduction explicitly. The
Lean file does not claim to implement all cluster algebra types or the entire
mutation graph; one first-mutated variable in a legitimate finite A2 seed is
enough to contradict the universal assertion.
