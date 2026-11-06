# Solution Review — Conjecture 00000001683 (PR 1095)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111146`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001683; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Ulam reconstruction for 3-uniform hypergraphs means reassembling them from their vertex-deleted hypergraphs. Conjecture: 3-uniform hypergraphs are reconstructible for n ≥ 8 (no counterexamples); any counterexample must be a twin pair of Steiner triple systems whose construction requires the 3-design parameters (v,3,1) to satisfy v ≡ 1,3 mod 6. 定义：3-均匀超图的 Ulam 重构指由其点删超图重组。猜想：3-均匀超图在 n≥8 时可重构(无反例);任何反例必为 Steiner 三元系的孪生对,其构造要求 3-设计的参数 (v,3,1) 满足 v≡1,3 mod 6。

**Decisive results.** Two explicit simple 3-uniform hypergraphs X and Y on {0,...,8}, each with 28 edges, have identical vertex-deleted decks with multiplicity but admit no vertex isomorphism. Neither is a Steiner triple system: the pair {0,1} has codegree two in each. This refutes both reconstruction for every n >= 8 and the asserted restriction of counterexamples to Steiner systems. The example is Kocay's classical n = 3 construction, with its extra vertex 0, not a newly claimed construction. The decisive Lean declaration is `conjecture1683_false`, whose statement is: ¬ ReconstructionClaim. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1095. The submission gives a complete, formalised disproof of conjecture 00000001683.
