# Conjecture 00000000088: an integer cannot be a pseudo-Anosov stretch factor

## Disproof

The conjecture quantifies over every prime (p\ge 2), so (p=2) is an admissible test case. Thurston's algebraic-unit theorem says that every pseudo-Anosov stretch factor is an algebraic unit. If the stretch factor were the rational integer 2, its inverse (1/2) would also have to be an algebraic integer. A rational algebraic integer is an integer, but (1/2\notin\mathbb Z). Thus no pseudo-Anosov element can have stretch factor 2, disproving the universal claim.

The cited result is William P. Thurston, “On the geometry and dynamics of diffeomorphisms of surfaces,” *Bulletin of the American Mathematical Society* 19 (1988), no. 2, 417–431, DOI: [10.1090/S0273-0979-1988-15685-6](https://doi.org/10.1090/S0273-0979-1988-15685-6). A later published account explicitly states the algebraic-unit conclusion and attributes it to Thurston: Joshua Pankau, “Salem number stretch factors and totally real fields arising from Thurston's construction,” *Geometry & Topology* 24 (2020), 1695–1716, [published article](https://msp.org/gt/2020/24-4/gt-v24-n4-p.pdf).

## Lean scope

`lean/Main.lean` verifies the arithmetic core: an integer with an integer multiplicative inverse must be (1) or (-1), so (2) cannot have an integer-unit certificate. The final theorem takes an explicit `unitBridge` parameter stating that any hypothetical witness with stretch factor (2) supplies an integer reciprocal for (2). This parameter represents the consequence of Thurston's theorem together with the fact that rational algebraic integers are integers.

The Lean project does **not** formalize mapping class groups, pseudo-Anosov maps, the algebraic-unit theorem, or the rational-algebraic-integer theorem. It does not prove the original conjecture end to end in Lean. The written proof invokes the cited published mathematics for that bridge; the Lean theorem checks only the resulting arithmetic implication. There are no custom axioms, `sorry`, or `native_decide` uses.

## Files and reproduction

- `report.tex` and `report.pdf`: mathematical disproof and scope statement.
- `lean/`: self-contained Lean 4 project using core Lean only.

From this directory, run:

```text
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

The direct Lean check prints the axiom dependencies of the main arithmetic theorems. The report was compiled from `report.tex` and visually checked after rendering.
