# Disproof of conjecture 00000008435

**Result:** Disproof under the reading stated below.

The complement-of-singleton symmetric design on seven points admits four successive derived designs, with parameters (7,6,5), (6,5,4), (5,4,3), (4,3,2), and (3,2,1). This refutes the proposed limit under the stated BIBD convention, which allows complete designs.

## The conjecture

> Definition: Residual and derived designs: the designs obtained from a given design by residual and derivation operations. Conjecture: The parameters of the residual and derived designs are (v-k, k-t, lambda) and (k,t,1); the symmetric designs recovering the original parameters after two levels of derivation are exactly the symmetric BIBDs; and the length of the derivation chain is at most 3. (upper bound on derivation chain length)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008435.md); both languages are in `SOURCE.md`.

## Reading and scope

Uses complete complement-of-singleton designs; the source does not explicitly exclude this family. Under the BIBD convention 2 <= k < v the four derivations are valid. A convention additionally excluding complete/trivial designs is outside this counterexample's claim.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `d2_correct`, `d3_correct`, `d4_correct`, `also_point_derivations`, `conjecture8435_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
