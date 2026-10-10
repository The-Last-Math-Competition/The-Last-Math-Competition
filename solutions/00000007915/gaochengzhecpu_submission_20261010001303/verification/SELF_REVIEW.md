# Author self-review

Verdict: mathematical review PASS; build and PDF evidence recorded separately.
Author agent: `/root/round8_high`.
Main.lean SHA-256: `fee7d16fc45c763eb2ea43f72b86d4856dd56044c7e61ac03ee0563d880b4e05`.

The matrix is the unnormalized nonbacktracking edge matrix, matching the source's unrescaled Ihara variable. Its entries are determined by genuine adjacent endpoint pairs with reverse edges excluded. The successor-to-neighbor injection uses the actual graph degree three. The proof applies to every finite graph satisfying the hypothesis; K4 is supplied to confirm nonvacuity. All poles, not merely Perron poles, are outside radius 1/2. Selecting nontrivial poles cannot remove the uniform gap. A single finite graph would not disprove an asymptotic random claim; the universal separation does. The paper supplies a bounded continuous test function to spell out the weak-convergence contradiction. Lean verifies the graph determinant and uniform separation; the established Hashimoto identity and the general weak-convergence definition are explicitly identified as the paper-level bridge, not claimed as newly formalized theorems.

Every asserted computational identity is proved symbolically in Lean; finite
enumeration uses kernel-checked `decide` only. The self-review does not substitute
for the parent's final review or for the actual fresh-build logs.
