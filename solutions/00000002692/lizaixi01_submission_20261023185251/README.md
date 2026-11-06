# 00000002692: empty boundary for a genuine p-adic contraction

The actual polynomial f(x)=5*x on Q_5 and its unit-ball restriction to Z_5 are strict contractions with nonzero derivative. Their convergence basin at 0 is the whole phase space, all periodic points are exactly {0}, and the true topological basin boundary is empty. The Z_5 basin image in Q_5 is the clopen closed unit ball, so the ambient boundary is empty too. This refutes the boundary clause of the printed conjunction.

The basin means the full set of points whose iterates converge to the fixed point, including that point. No multiplier order is assigned to the nonunit residue 0 mod 5, and no separate corrected measure-only statement or degree-at-least-two variant is claimed. The actual basin has the full phase-space mass for any measure. The proof uses true Padic and PadicInt values, actual iterates and convergence, Function.periodicPts, frontier and closure, rather than finite modular computations.

Closed PR276 was rejected for arithmetic-only Lean without any conjecture objects. Its shell 5Z_5 minus 25Z_5 is not the boundary of the clopen ball 5Z_5; mapping to zero mod 25 also differs from equality to zero in Z_5. The complete error attribution and corrected mathematical proof are in report.tex/report.pdf. SOURCE.md preserves both original languages. lean/ contains the pinned project and all-named axiom audit; evidence/ contains qualification, exact commands, logs, fresh-kernel receipts and separate supervising AI review.

Standard unit-ball convention: Fan and Liao, arXiv:1408.4574, p.2. No later degree-at-least-two result from that paper is used. AI-led production, not organizer acceptance or a controlled efficiency claim.
