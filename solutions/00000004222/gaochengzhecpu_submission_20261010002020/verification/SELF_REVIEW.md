# Author self-review

Verdict: mathematical review PASS; actual build and PDF evidence recorded separately.
Author agent: `/root/round8_high`.
Main.lean SHA-256: `46f002e01c6a4ee7cf40bea263cdb2698544d4c46f1364db9667f172a40762ee`.

The source states ordinary equality with the derivative at 1 and does not specify a reduced polynomial or normalization. The chosen top-dimensional Laplacian is the actual 4 by 4 down/Hodge Laplacian, so the derivative order really equals the face count. The tree predicate retains the complete 1-skeleton, asserts no selected 2-cycle, and asserts that every actual 1-cycle has a selected filling; it does not define tree count to be 4. Injectivity and surjectivity are both proved. The omitted-face correction has no divisions, hence preserves integer chains and shows all four torsion weights are 1; this paper bridge is distinguished from the Q-only formalization. No general homology library or abstract simplicial-complex theorem is falsely claimed. Both the matrix and its actual characteristic polynomial are used. The highest derivative is 24 for every monic degree-four polynomial, irrespective of the Laplacian entries. Parent adversarial feedback identified the alternate 6 by 6 up-down convention in the standard simplicial tree theorem; a supplementary paper calculation now proves its characteristic polynomial is t^3(t-4)^3 and the fourth derivative at 1 is 72. This supplementary convention calculation is explicitly not claimed as a Lean theorem. The author self-review is internal and does not replace the parent adversarial review.

All finite enumeration and boundary matrix entries use kernel-checked `decide`
(including its kernel-reduction mode); the algebraic calculations use exact proof.
No external independent review is claimed.
