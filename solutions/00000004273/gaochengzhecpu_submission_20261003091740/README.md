# Disproof of conjecture 00000004273

**Result:** Disproof under the reading stated below.

The finite reduced abelian 2-group C_2 direct-sum C_4 has first two Ulm quotients both isomorphic to F_2. Hence u_0 = u_1 = 1, contradicting strict decrease; both invariants are nonzero.

## The conjecture

> Definition: The Ulm sequence is the cardinal sequence of the Ulm subgroup quotients of a countable p-group. Conjecture: The realizable sequences are exactly the full sequences that are termwise at most countable and strictly decreasing in the ordinal order, and the sequence lattice is closed under taking subsequences within length omega_1. (lattice characterization of Ulm sequence realizability)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000004273.md); both languages are in `SOURCE.md`.

## Reading and scope

Countable includes finite groups. Both quotient dimensions (1,1) and cardinalities (2,2) fail strict decrease.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `groupG`, `quotient0`, `quotient1`, `conjecture04273_false`, `full_conjecture_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

## Reproduce

From this submission directory:

```text
cd lean
lake build
```

From this submission directory, rebuild the PDF with:

```text
tectonic main.tex
```

## Submission status

AI-assisted with Codex; submitted by **gaochengzhecpu**. The statement-to-proof correspondence was checked locally by a separate agent, and the PDF was rendered and inspected. This remains a draft for independent mathematical review; local verification is not organizer acceptance. `verification.json` gives hashes of the reviewed files.
