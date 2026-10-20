# Parent adversarial review: 00000009527

Verdict: PASS

The complete bilingual statement, Main.lean, author report, auxiliary exact script,
fresh build logs and all three final PDF pages were inspected. This is internal
parent review of an agent-developed proof; no external independence is claimed.

The actual source order has the displayed direction. The proof supplies a strict
successor of D, which refutes maximality rather than merely greatestness. Mutual
equivalence cannot eliminate a strict comparison. Same qubit domain/codomain.
Density matrices use actual Mathlib PosSemidef and trace one, with arbitrary
finite ensemble cardinality and nonnegative real weights of sum one. Off-diagonal
input entries are never assumed zero. The entropy is actual Hermitian spectral
von Neumann entropy; the diagonal formula is proved from eigenvalues and trace.
Its fallback on non-Hermitian matrices is unused on the channel outputs involved.

Both normalized finite Kraus families act as claimed on every complex matrix:
two projections for Z; two copies of each E_ab/2 for D. This characterization
certifies CP at every ancilla size and trace preservation. Jensen for -x log x
on nonnegative reals gives chi(Z)>=0 for all ensembles; constant D gives zero.
The genuine equiprobable orthogonal density ensemble gives log(2)>0 for Z.
The secondary reset-map antisymmetry counterexample is separately certified.
No claim about the unrelated broadcast-capacity expression is needed or made.

Fresh lake build, strict Main.lean and exact rational Python checks all exit 0.
Only propext, Classical.choice and Quot.sound occur in the axiom audit.
Native desktop compilation succeeded for the exact TeX hash. Tectonic has no
warnings. All three final PNG pages are clean, complete and readable.


Reviewed artifact hashes:

- Main.lean: `130d28164d77a44c7451f2f212e974db44ba6c4167891f66110bb19c49254bd0`
- main.tex: `ba1825557201bf1e6525d113a0ac276f0f41d69261090234705dfe9e36380178`
- main.pdf: `6105c0c25e50e36b3db4abf9cc318094016925fec39e68a4bdb9c601a2bd668c`
