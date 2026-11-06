# Disproof of the literal degree clause in conjecture 00000004374

The source states that the next nonzero **odd** homotopy degree is a multiple of `p^2-1` for every odd prime. For `p=3`, every such multiple is even. This refutes the printed statement without computing any K-group. It does not refute a repaired statement about differences or shifted occurrence degrees.

## Formal coverage

`OddDegree.lean` contains eight proved theorems, including the explicit primality of 3, the obstruction for arbitrary nonzero-homotopy predicates and arbitrary low-degree cutoffs, and the distinction from shifted periods. The necessary clause permits different occurrence degrees for different primes; no stronger uniformity is assumed. All definitions and proofs use core Lean/Std only.

`Audit.lean` prints dependencies of all eight theorems. Only Lean's standard `propext` and `Quot.sound` appear; two elementary theorems have no axioms. No custom axiom, sorry, native decision shortcut or hidden homotopy assumption is used.

## Reproduce

With official Lean 4.31.0 / Lake / leanchecker and a working pdflatex installation on PATH:

    bash verify.sh

The script copies only the sources into a new temporary directory, builds, elaborates strictly at trust level zero, audits dependencies, replays the module with leanchecker, and rebuilds the PDF. The PDF build is checked for actual nonempty PDF output. `solution.tex` and `solution.pdf` provide the full written argument.

In the assistant cloud, existing TeX needed explicit preexisting format/font paths and writable caches, not installation or permission changes. The first TeX attempt failed on a read-only default cache; a later attempt emitted DVI under the restored format. The final command explicitly forces PDF output. These exploratory failures are not mathematical verification successes. Final verification records are included.

## Scope and disclosure

Prepared and reviewed with AI assistance for Galaxy-0. Independent AI review is not human review or competition acceptance. The mathematical result is a literal inconsistency of the posted degree conditions, not a new K-theory computation or a classification of integer K-groups. If the intended conjecture concerns a shifted degree or a period of differences, it must first be restated and is not settled here.

Original source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/b355e42906e6eaf52bc7e9d005e0ef02d8aa7400/conjectures/00000004374.md

Baseline and source verified 2026-10-26. This submission is supplied under the upstream GPL-3.0 license.
