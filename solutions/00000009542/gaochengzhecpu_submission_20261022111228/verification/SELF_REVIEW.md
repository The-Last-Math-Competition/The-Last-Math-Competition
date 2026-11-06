# Author-agent adversarial self-review: 00000009542

Verdict: PASS

# Conjecture 9542 — strict compound-channel minimax gap

Status: complete actual quantum-channel counterexample, pending parent review/publication. No TeX, PDF or PR created by this agent.

## Exact claim and result

Exact bilingual source: `round5/source/00000009542.md`. Its first assertion identifies the entanglement-assisted capacity of a finite unknown fixed-channel set with min_i max_rho I(rho,Phi_i).

For the three explicit qutrit-to-classical-bit channels below, the actual single-letter quantities are

sup_rho min_i I(rho,Phi_i) = h(1/3) < log 2 = min_i sup_rho I(rho,Phi_i).

All logarithms here and in Lean are natural, so the quantities are in nats. In bits divide every value by log 2. The established compound entanglement-assisted coding theorem identifies the left quantity with the operational capacity. Therefore the first conjunct is false. The subsequent continuity and exponent assertions need not be independently refuted.

## Actual channels and complements

Fix input H_A=C^3 with basis e_0,e_1,e_2 and output H_B=C^2. For i=0,1,2, set b_i(j)=0 if j=i, and 1 otherwise. Let

K_(i,j)=|b_i(j)><j|,
Phi_i(A)=sum_j K_(i,j) A K_(i,j)^* = diag(A_ii, tr A-A_ii).

These are actual complex-linear completely positive trace-preserving maps. The code proves positivity of every matrix amplification, not merely positivity on 3-by-3 inputs. The generic amplification identity is

(id_k tensor KrausMap_K)(X) = sum_j (I_k tensor K_j) X (I_k tensor K_j)^*.

An actual Stinespring isometry is

V_i |j> = |b_i(j)> tensor |j>.

Both partial traces of V_i A V_i^* are checked. Its output channel is Phi_i, and its complementary channel is

Phi_i^c(A) = P_i A P_i + Q_i A Q_i,
P_i=|i><i|, Q_i=I-P_i.

This complementary channel keeps the full 2-by-2 block on the unselected coordinates. It is **not** full dephasing. The code also checks that outputs and complementary outputs of every actual density matrix are normalized PSD matrices.

## Genuine von Neumann entropy and the universal upper bound

The formal entropy is the real trace of the genuine continuous functional calculus of eta(x)=-x log x, with eta(0)=0. The code proves, using Mathlib's actual Hermitian spectral theorem,

S(A)=Re tr(cfc eta A)=sum_j eta(lambda_j(A)).

It also proves the genuine diagonal formula S(diag p)=sum_j eta(p_j). Thus this is the ordinary von Neumann entropy, not a proxy Shannon function attached to diagonal entries.

For an arbitrary PSD matrix A, and arbitrary complementary self-adjoint projections P,Q, the code proves

S(A) <= S(PAP+QAQ).

Here is the checked argument. Let U and V be the actual unitary eigenvector matrices of A and B=PAP+QAQ, and put X=V^*PU, Y=V^*QU. Then XX^*+YY^*=I and X^*X+Y^*Y=I. Therefore

w_ab=|X_ab|^2+|Y_ab|^2

is doubly stochastic, and the eigenvalues mu_a of B satisfy mu_a=sum_b w_ab lambda_b. Scalar Jensen for eta on [0,infinity) gives sum eta(lambda_b)<=sum eta(mu_a). Every part of this argument is kernel-checked, with no entropy-increase axiom assumed.

Use the standard entropy-exchange formula for channel mutual information through the actual Stinespring complement:

I(rho,Phi_i)=S(rho)+S(Phi_i(rho))-S(Phi_i^c(rho)).

For p_i=rho_ii, pinching entropy increase yields

I(rho,Phi_i) <= S(Phi_i(rho)) = h(p_i).

The formal state domain contains **all** complex PSD trace-one matrices, including coherent inputs. The code does not define I to be h(p_i). It defines the actual three entropy expression above, and proves the inequality. On diagonal input states the complementary channel fixes rho, so equality holds.

## Exact optimizations and strict gap

For every input density matrix, p_i>=0 and p_0+p_1+p_2=1. Some p_i<=1/3. Monotonicity of h on [0,1/2] implies

min_i I(rho,Phi_i) <= h(1/3).

The uniform diagonal state rho=I_3/3 attains equality simultaneously for all three channels. Hence the true supremum over all density matrices of the finite infimum equals h(1/3).

For each fixed i, I(rho,Phi_i)<=h(p_i)<=log 2 for every density matrix. A diagonal state with p_i=1/2 and the other two coordinates 1/4 attains log 2. Each individual supremum therefore equals log 2.

The code uses actual real `sSup` over the full density-matrix state set and `Finset.inf'` over the three channels. It proves the suprema are the stated finite values by upper bounds and explicit attaining states. There is no unbounded/empty sSup junk-value issue.

Strictness follows from the exact binary-entropy theorem, without approximation. An independent algebraic form is

h(1/3)=log 3-(2/3)log 2,
log 2-h(1/3)=(1/3)log(32/27)>0.

## Formal boundary and operational bridge

Lean proves the entire explicit finite-dimensional quantum construction and the strict inequality of the actual mutual-information optimizations. It does **not** encode arbitrary asymptotic communication codes, purification-independence of channel mutual information, or prove the general compound coding theorem from scratch. No such general theorem is added as an axiom or a hypothesis that makes the numerical conclusion conditional.

The ordinary entropy-exchange expression above is used as the standard equivalent definition of channel quantum mutual information with a specified genuine Stinespring complement. The mathematical paper must state this convention and its equivalence to the purification formula. It then invokes the published coding theorem to identify the fully checked left quantity with operational entanglement-assisted classical capacity. The theorem is applicable to an unknown fixed memoryless channel selected from a finite set; the same encoder/decoder must work on all members, with no sender channel-state information or feedback. We exhibit such an instance. This is not the arbitrarily varying channel model, which involves a different optimization.

## Personally verified primary reference

H. Boche, G. Janßen, S. Kaltenstadler, *Entanglement-assisted classical capacities of compound and arbitrarily varying quantum channels*, arXiv:1606.09314v3 (25 January 2017), https://arxiv.org/pdf/1606.09314 .

Actually opened and read. Theorem 1, equation (7), PDF page 6, gives the operational compound capacity as sup_rho inf_s I(rho,N_s), for average and maximal error. Definition and equation (2), PDF page 4, give the standard purification quantum mutual information. Remark 3, equation (44), PDF page 13, already explicitly records strict separation from inf_s sup_rho for another concrete finite-channel example. Our construction is an independently checked smaller-input three-channel illustration; it is not presented as a previously unknown phenomenon.

## Adversarial author audit

1. Complete positivity: the code checks every finite matrix amplification by actual Kronecker-conjugation identity. Ordinary positivity alone is not substituted for CP.
2. Trace preservation: explicitly proved for every input matrix, plus genuine complex linearity. The output dimension is two and the input dimension is three.
3. Stinespring bridge: V^*V=I and both partial-trace formulas are checked on arbitrary matrices. The complement includes internal unselected-block coherence.
4. True entropy: trace(cfc eta) is identified with the actual eigenvalue entropy. No custom entropy with convenient behavior is introduced.
5. Arbitrary coherent inputs: the upper bound holds on all PSD trace-one complex matrices. Restricting only to diagonal states would be insufficient and is not done.
6. Correct information: I is the entropy-exchange formula using the actual complementary channel. Equality with h(p_i) is only asserted for diagonal inputs, after proving the complement fixes them.
7. Exact extrema: uniform rho attains the joint value; a separate valid diagonal state attains each individual value. The optimizing state cannot be chosen after learning i for the compound value.
8. Real suprema: nonemptiness and uniform finite upper bounds are checked in the `csSup` arguments. Actual finite infima are used.
9. Units: natural logarithms throughout Lean and this report; optional conversion to bits divides both sides by log 2.
10. Compound versus AV model: only one fixed unknown member is used for the whole block, matching the public theorem. No convex hull or infimum over time-varying distributions is substituted.
11. Formal coverage: operational coding and the general purification-equivalence theorem are explicitly external published bridges. The final claim does not say these universal theorems have been formalized.
12. Trust and computation: final printed dependencies must be only propext, Classical.choice, Quot.sound; no sorry, admit, native_decide or custom axioms. The independent rational Python script checks all matrix units and exact entropy-log coefficients, and is not a Lean oracle.

## Files and reproducibility

`round5/drafts/00000009542/lean/Main.lean`: actual formal proof.
`round5/drafts/00000009542/verify.py`: independent exact Fraction checks, no numerical eigensolvers or floating point.
`round14/quantum/9542-status.json`: complete commands, exit codes, timings and final hashes.
`9542-strict.log`, `9542-lake-build.log`, `9542-verify.log`: actual raw output.

Pinned Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The Lake default target is Main and warningAsError is enabled in lakefile.toml. No shared snapshot, publication allowlist, TeX or PDF was changed by this agent.

Frozen Main SHA256: `99cc222c4cdc897b17225c24ad10ba023828143e7caa9051a7df2152e6eb8752`. Strict check passed in 31.094 seconds; full Lake build passed in 32.203 seconds. Independent exact verification exit code 0, SHA256 `457e5d789eabe8cbed3eec02a9a26996ba87dcdb353c5ab66fced0f9d1327c04`. Forbidden-token scan: [].


Reviewed artifact hashes:

- Main.lean: `99cc222c4cdc897b17225c24ad10ba023828143e7caa9051a7df2152e6eb8752`
- main.tex: `fd8f085e9a61d8bf1f0c19f5c7a0300617ae3abe4c9c0da60f85217dc7044863`
- main.pdf: `397b7be547f05cec368aa3769e4282d46431afac1f6c1cc975fddc10da9d3019`
- SOURCE.md: `b6df7a51deb1d8f884e303fe7f544293c1e4a89470612dc56f226fd3385ecf35`
