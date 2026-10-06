# Disproof of conjecture `00000003940`

**Verdict: false by invariance.** The file defines a finite-type invariant as
a numerical invariant obtained from a truncation of the DGA, but then asks for
two chain-isomorphic DGAs for which all such invariants differ.  These demands
are incompatible.

A chain-level DGA isomorphism preserves the differential, product, grading,
and filtration.  It therefore restricts to an isomorphism of every finite
truncation.  Any numerical quantity that is genuinely an invariant of that
truncation has the same value on isomorphic truncations.  Hence for every
finite-type invariant `I_n`,

```text
DGA(L_1) isomorphic to DGA(L_2)  ==>  I_n(L_1) = I_n(L_2).
```

The crossing-number bound does not help: no pair exists at any crossing
number, so in particular none exists with at most `12` crossings.

## Formal verification

The Lean project states the argument at its correct abstraction level.  Given
an isomorphism relation and a family of numerical invariants that respects
that relation, it proves there cannot exist an isomorphic pair on which every
invariant differs.  It also checks an explicit list-truncation instance.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```

The project uses core Lean/Std only and contains no proof placeholders.
