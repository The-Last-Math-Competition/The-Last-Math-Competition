# TLMC 00000000039: infinitely many counterexamples

For every cutoff L, the genuine integer sequence in Main.lean supplies an odd N>L such that N is not p+2^a+2^b for any Nat.Prime p and any natural exponents a,b. The conventional prime-sum meaning of p is explicit; arbitrary integer p would make the statement trivial.

This formalizes an adapted Crocker construction using Fermat products, an explicit 28-class exponent covering, genuine ZMod inverse residues and a growing sequence. It includes distinct, equal and zero exponents, actual divisibility obstructions and the complete sufficiently-large quantifier. No finite counterexample alone is substituted for the claimed asymptotic assertion.

The integer moduli need not be prime: any divisor greater than one of the hypothetical prime must equal that prime. All finite certificates are proved in Lean with ordinary decide and norm_num; Python was exploratory only. Main.lean has no sorry, custom axioms or native_decide.

Lean4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Run lean/verify.sh. The package includes exact source, full LaTeX/PDF, all-namespace ordinary axiom enumeration and the source-bound build/fresh-kernel command evidence. Production timings are not controlled research-efficiency data. The mathematical argument is classical, not a novelty claim. Organizer review remains pending.
