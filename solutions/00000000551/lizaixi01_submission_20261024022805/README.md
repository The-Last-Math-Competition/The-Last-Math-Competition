# Counterexample to 00000000551

For the actual complex path algebra of `3 → 2 → 1 → 0` modulo all length-two paths, an explicitly constructed finitely generated module has projective dimension exactly 3. Therefore its genuine little finitistic dimension is at least 3, contradicting the stated universal bound 2 for special biserial algebras.

The Lean proof constructs a standard square-zero extension and independently verifies its actual path-algebra quotient presentation. It proves the quiver path classification, full interval basis and concatenation multiplication, the exact relation ideal, and the standard special biserial conditions. Concrete module maps give projective retracts and short exact sequences. The dimension calculation uses Mathlib's Ext-based `CategoryTheory.projectiveDimension`; the final bound uses a supremum over all finitely generated finite-projective-dimension modules. No desired dimensions or counts are assigned as definitions.

The example concerns the source's universal statement; it is an acyclic string algebra. No claim about a classification, a universal optimal replacement bound, or only the cyclic subclass is made. Full original bilingual source is preserved in `SOURCE.md`.

See `report.pdf` and `report.tex` for the mathematical argument, `lean/` for the complete pinned project, and `VERIFICATION.md` and `evidence/` for actual verification and source-bound receipts.
