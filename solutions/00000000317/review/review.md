# Solution Review — Conjecture 00000000317 (PR 1216)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027162007`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000317; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed statement has two clauses: c_F ∈ L but c_F ∉ M, and among the first 20 partial quotients of Freiman's constant the digit 1 appears exactly 8 times. The submission refutes the second clause. It reads 'first 20 partial quotients' both as a_0,...,a_19 (count 5) and as a_1,...,a_20 (count 6), and abstracts the first clause as an arbitrary proposition InLNotM.

**Decisive results.** The theorem is the negation of the conjunction: for every proposition InLNotM, not (InLNotM and count=8). Since the count is 5 (or 6 in the shifted indexing), the second conjunct is false, and therefore the filed conjunction is false whatever the first clause says. The counterexample is not a special case outside the regime: the computation is exactly the first 20 regular continued-fraction partial quotients of Freiman's constant. The Lean definitions `cfState` and `pq` implement the Gauss map and floor; the file proves the required complete quotients x_n=(p_n+r_n√462)/s_n through n=20 and the floor identities a_n, then counts the 1s.

**Report correspondence.** The report's Tables 1-2 and the main theorems match the Lean declarations exactly: a_0,...,a_20 = 4,1,1,8,2,14,2,2,1,12,117,1,1,7,16,35,6,2,7,2,1; count 5 for a_0...a_19 and 6 for a_1...a_20. The report explicitly says the first clause is not formalized and that the main theorem treats it as an arbitrary proposition. The report compiles.

## Disposition

APPROVED — merged as PR 1216. The submission gives a complete, formalised disproof of conjecture 00000000317.
