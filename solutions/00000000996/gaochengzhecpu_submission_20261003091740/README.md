# Disproof of conjecture 00000000996

**Result:** Disproof under the reading stated below.

The two displayed quantities are 4/3 and 7/4. Their ratio is exactly 16/21, not 7/9; reversing the ratio gives 21/16, also not 7/9.

## The conjecture

> Definition: The critical spectral dimension of percolation. Conjecture: The universal ratio between the spectral dimension 4/3 of percolation on random graphs and 7/4 of the jungle gym is 7/9 (a universal ratio).

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000000996.md); both languages are in `SOURCE.md`.

## Reading and scope

Refutes the literal rational ratio, without asserting additional percolation results.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `exact_ratio`, `reverse_ratio`, `conjecture996_false`, `reversed_claim_also_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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

Independent arithmetic check: `python verify.py`.

## Submission status

AI-assisted with Codex; submitted by **gaochengzhecpu**. The statement-to-proof correspondence was checked locally by a separate agent, and the PDF was rendered and inspected. This remains a draft for independent mathematical review; local verification is not organizer acceptance. `verification.json` gives hashes of the reviewed files.
