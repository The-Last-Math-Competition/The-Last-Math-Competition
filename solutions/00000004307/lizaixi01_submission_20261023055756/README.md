# Conjecture 00000004307: necessary rank formulas conflict

The English source says the same minimal rank is 2k-1 AND, when gcd(k,p-1)=1, exactly 1. The Chinese has the same clauses. With legal positive k=3 and odd prime p=5 (also k<=p-2), this would require the same rank to be both 5 and 1.

This submission refutes that literal necessary conjunction. It does not compute an actual Euler-system or higher-K-group rank. No artificial Euler-system object is defined, and no desired rank is assigned as a definition. Every candidate rank function is quantified over. A different corrected piecewise reading in which the conditional clause overrides the first is explicitly outside the claim.

The Lean proof covers every characteristic-zero semiring-valued candidate, with explicit natural, integer and cardinal specializations, restricted and unrestricted formulas, and fixed prime p=5. The optional restricted index range makes the necessary claims weaker and still impossible. All 9 theorems receive transitive axiom audits.

Files: complete original bilingual `SOURCE.md`; LaTeX source and rendered PDF; pinned Lean 4.33.0 / Mathlib project; source-bound build, axiom and full official fresh-kernel receipts and logs; final eligibility/review evidence; SHA256 manifest. OpenAI Codex assisted, with separate supervising AI review. Organizer acceptance is pending.
