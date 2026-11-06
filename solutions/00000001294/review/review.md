# Solution Review — Conjecture 00000001294 (PR 1145)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023054721`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001294; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the number of leaves at level n of the 3x+1 reversal tree is O(c^n) with c=(4/3)^{1/2}. The submission reads the standard finite-depth unfolded inverse tree: level N is the actual fiber {x>0 : T^N(x)=1}, and 'leaves at level N' means frontier nodes at that depth (the infinite tree has no terminal leaves, since every node has child 2n). Both the full odd-step map T_0 and the shortcut map T_1 are covered, pruned and unpruned.

**Decisive results.** Lean defines the full and shortcut Collatz maps, the actual level fiber as a finite set (using x≤2^N T^N(x)), and the 3-pruned subset. For every Good n (positive, not divisible by 3) it constructs three distinct children that map to n in exactly seven steps; the table's arithmetic is checked case-by-case. It recursively maps words in {0,1,2}^m to genuine depth-7m nodes and proves the node map injective, giving 3^m≤|prunedLevel b (7m)|≤|level b (7m)| for b=false and b=true. Since claimedBase^7=(4/3)^{7/2}<3, 3^m grows faster than claimedBase^{7m}; Lean proves for every C and cutoff N that C·c^{7m}<3^m eventually, hence the cardinality sequence is not O(c^n). This directly negates the filed asymptotic bound for the standard tree.

**Report correspondence.** The report matches Lean: the three-children-every-seven-levels construction, the injection from words, the lower bounds, claimedBase^7<3, violates_every_bound, and the Big-O negations for both normalizations. The report explicitly discloses the frontier-node convention and says it does not claim a first-hit cycle-deleted variant or the Collatz conjecture. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1145. The submission gives a complete, formalised disproof of conjecture 00000001294.
