# Source and scope record

- Official problem: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000001043.md
- Official file blob SHA when read: `9eb40bbefbd89804f9caaad74105dbc3c64319cb`
- The source describes Carlitz rank with the undefined shorthand “AB-expression layers.” It asserts an upper bound of four for prime-field permutations and a further norm-basis decomposition claim. It supplies no definition of A/B and no bibliographic citation.
- This submission uses standard Carlitz rank: the minimum number of zero-fixed inversions x^(q−2) in a composition with arbitrary affine bijections. It does not assert an unsupported alternative definition of AB.
- Primary definition actually inspected: Zhiguo Ding, *Connecting two types of representations of a permutation of F_q*, Section 4 immediately after Theorem 10: https://arxiv.org/html/2103.09064v1 . That passage explicitly defines the alternating affine/inversion expression and its minimum inversion count. The paper also cites the introducing Aksoy et al. paper, DOI https://doi.org/10.1016/j.ffa.2009.02.006 . Access to the latter full publisher page was unavailable, so it is not represented as a full-text source inspection.
- The complete structural proof is included in `solution.tex` and `solution.pdf`. Lean proves the same counterexample by a separate complete algebraic normalization, not by assuming a cited characterization theorem.
- Refuting the universal rank-at-most-four clause refutes its conjunction with the additional decomposition clause. No assertion about the separate decomposition terminology is needed.

## Eligibility snapshot

At 2026-10-09 19:29 UTC, official metadata listed problem 00000001043 as neither proven nor disproven. Metadata blob SHA: `9189d96240d7117f4ef1d96c2c84502aa7a3ca50`.

All-state pull-request searches for `1043` and `00000001043` returned no matches. A search for `Carlitz` returned only unrelated submissions 108 and 244. This snapshot must be refreshed before publication.
