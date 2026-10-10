# 00000001198: odd Zonal unit coefficient

The empty-partition normalized Zonal polynomial is the actual symmetric polynomial 1. Its unique LR coefficient in its product with itself is 1, so it cannot be any finite alternating sum of even integers. This refutes only the parity clause of the conjecture as stated, which does not exclude the empty partition.

Files: proof.tex, compiled proof.pdf, and the full pinned project in lean/. Reproduce with Lean 4.19.0: cd lean and run lake build. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The project prints standard axiom audits for its mathematical results. The proof cites the primary NIST DLMF Zonal normalization, including the zero partition.
