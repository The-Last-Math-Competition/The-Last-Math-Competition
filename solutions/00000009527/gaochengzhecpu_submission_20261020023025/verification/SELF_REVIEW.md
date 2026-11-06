# Author-agent adversarial self-review: 00000009527

Verdict: PASS

Main.lean SHA-256: `130d28164d77a44c7451f2f212e974db44ba6c4167891f66110bb19c49254bd0`

# 9527: strict successor of the completely depolarizing channel

Source direction: Phi <= Psi iff chi(E;Phi) <= chi(E;Psi) for every finite input ensemble E. The source explicitly claims this is a closed partial order on channel space and that its unique maximal element is the completely depolarizing channel. We refute maximality itself, not merely greatest-element language or a quotient convention.

Take a qubit, D(A)=tr(A) I/2, and Z(A)=diag(A00,A11), the completely dephasing channel. They have the same input and output spaces. Z has Kraus E00,E11. D has eight Kraus operators Eab/2, each of the four matrix units occurring twice; the duplication keeps all coefficients rational. Every Kraus family satisfies sum K* K=I, and the displayed maps equal sum K A K* on every complex matrix.

For any finite ensemble (p_i,rho_i), D sends every state to I/2, hence chi(E;D)=0. Write a_i=Re(rho_i00), b_i=Re(rho_i11). Positive semidefiniteness gives a_i,b_i>=0; the actual dephasing output is diag(a_i,b_i). Its von Neumann entropy is f(a_i)+f(b_i), with f(x)=-x log x and f(0)=0. Concavity of f and finite Jensen yield chi(E;Z)>=0 for every ensemble, including those of noncommuting input states. Thus D<=Z.

For the equiprobable ensemble E00,E11, Z leaves the two pure states unchanged. Their entropies vanish and the average entropy is log 2. Thus chi(E;Z)=log 2>0=chi(E;D), proving Z is not <=D. Therefore D has a strict successor and is not a maximal element, even after quotienting channels by mutual less-noisy equivalence. This alone disproves the conjecture conjunction; it does not make any claim about the separate broadcast-capacity formula.

Additional literal-space obstruction: R0(A)=tr(A)E00 and R1(A)=tr(A)E11 are distinct CPTP reset channels with chi(E;R0)=chi(E;R1)=0 for every ensemble, so the relation is not antisymmetric on raw channels. Quotienting repairs this secondary defect but does not repair the strict D<Z counterexample.

# Semantic audit

- Actual objects: complex 2 by 2 matrices; density states are Mathlib PosSemidef plus trace one.
- Entropy is defined from Mathlib Hermitian eigenvalues, not an arbitrary Shannon proxy.
- The theorem entropy_diagonal is proved by spectral membership and trace preservation under unitary conjugation. It handles arbitrary real diagonal entries; the entropy application uses nonnegative entries.
- Arbitrary ensembles: n is universally quantified; real weights are nonnegative and sum one. No restriction to diagonal input states is used in Jensen.
- KrausCPTP is exactly the finite Kraus characterization of CPTP maps in finite dimensions. It certifies all four displayed maps on arbitrary complex inputs, not just basis states or a finite test list.
- Strict maximality: both D<=Z and not Z<=D are formal conclusions.
- Zero eigenvalues use the continuous convention -0 log0=0 supplied by Real.negMulLog.
- Log base is natural; multiplying all information by a positive constant leaves the comparison unchanged.
- Auxiliary verify.py uses exact rational arithmetic only and is not imported by Lean.
- No claim of novelty: these are elementary consequences of standard dephasing and reset channels.
- Author self-review was followed by parent adversarial review; no external independent review is claimed.

# Scope of disproof

The separate capacity attainability clause is not assessed. The maximal-element assertion is false for concrete same-space qubit channels, which suffices to refute the source conjecture. The failure survives any quotient identifying mutually less-noisy-equivalent channels.

# Reference checked

John Watrous, *The Theory of Quantum Information* (2018), author-hosted draft:
https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf
Sections 2.2 (finite Kraus channel characterization, completely dephasing and depolarizing examples), 5.2 (spectral von Neumann entropy), and 8.1 (Holevo information). The elementary strict comparison here is proved in full; no capacity theorem or external numerical routine is assumed. Retrieved 2026-10-19. PDF opened and relevant sections inspected through web.

# Formal theorem map

- `eigenvalue_diagonal`, `eigenvalue_sum`, `entropy_diagonal`: actual spectral entropy reduces to binary Shannon entropy on diagonal matrices.
- `dephase_kraus`, `depolarize_kraus`, `reset_kraus`: normalized Kraus witnesses and arbitrary complex input action identities.
- `density_diag_real`, `density_diag_nonneg`, `dephase_density`: genuine density states supply nonnegative real diagonal entries.
- `holevo_dephase_nonneg`: Jensen argument for every input ensemble.
- `depolarize_lessNoisy_dephase`: first required order direction, universally over all finite ensembles.
- `orthogonalEnsemble`, `orthogonal_holevo_dephase`: actual equiprobable orthogonal density states have Holevo value log2 under dephasing.
- `dephase_not_lessNoisy_depolarize`: strict reverse comparison failure.
- `depolarize_not_maximal`: the principal disproof, bundling both actual CPTP certificates and the strict order comparison.
- `not_antisymmetric`: additional distinct reset-channel example.

No TeX or PDF has been authored by this agent; parent is responsible for complete final LaTeX/PDF pipeline and submission.


Reviewed artifact hashes:

- Main.lean: `130d28164d77a44c7451f2f212e974db44ba6c4167891f66110bb19c49254bd0`
- main.tex: `ba1825557201bf1e6525d113a0ac276f0f41d69261090234705dfe9e36380178`
- main.pdf: `6105c0c25e50e36b3db4abf9cc318094016925fec39e68a4bdb9c601a2bd668c`
