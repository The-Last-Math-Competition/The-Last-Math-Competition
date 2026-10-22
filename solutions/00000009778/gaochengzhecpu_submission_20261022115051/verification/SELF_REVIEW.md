# Author-agent adversarial self-review: 00000009778

Verdict: PASS

# 9778: Volterra singular values have a nonzero even-power correction

Status: complete mathematical disproof with an explicitly delimited formal analytic core and an external substantive Hilbert-space spectral bridge; frozen for parent review. Recorded strict check exit 0 (15.468 seconds), full Lake build exit 0 (16.282 seconds), and independent exact verifier exit 0 (0.468 seconds). No TeX, PDF or PR is created by this agent.

## Exact source and conclusion

Exact bilingual source: `round5/source/00000009778.md`, SHA256 `863ab4780417b8861486863879baf2ebcfffe7b687a8d91d8fafd0b5a15a8b9c`. It claims that the standard Volterra singular values have leading term 1/(pi n) and corrections containing only odd inverse powers, with a further assertion about Bernoulli coefficients.

For V:L2(0,1)->L2(0,1), (Vf)(x)=integral_0^x f(t)dt, the actual singular values indexed from n=1 are

s_n(V)=1/[pi(n-1/2)].

Consequently n^2(s_n(V)-1/(pi n)) tends to 1/(2pi), which is strictly positive. A complete asymptotic expansion with only absolute odd powers n^-1,n^-3,n^-5,... would force this limit to be zero. The odd-only clause is therefore false, so the whole conjunction is false. A full expansion does exist; the disproof does not claim otherwise.

## Full mathematical identification of the actual L2 singular values

Work over either real or complex L2(0,1) with Lebesgue measure. The kernel K(x,t)=1_{0<=t<=x<=1} belongs to L2((0,1)^2), with integral of |K|^2 equal to 1/2. Its Hilbert-Schmidt integral operator is exactly V, so V is bounded and compact. Cauchy-Schwarz and Fubini give the genuine Hilbert adjoint

(V* g)(s)=integral_s^1 g(t)dt.

The Gram operator A=V*V is compact, positive and self-adjoint, with

(Af)(s)=integral_s^1 integral_0^t f(u)du dt
       =integral_0^1 [1-max(s,u)]f(u)du.

Here all integrals and Fubini manipulations are legitimate for f in L2, since L2(0,1) embeds into L1(0,1). Put F(x)=integral_0^x f(u)du and y=Af. Then F is absolutely continuous and continuous; y is C1 with y'=-F everywhere, its derivative is absolutely continuous, and y''=-f almost everywhere. Thus y belongs to H2(0,1), with boundary conditions y'(0)=0 and y(1)=0.

Suppose Af=lambda f for a nonzero L2 eigenvector and a nonzero eigenvalue. Positivity gives lambda>0. Replace f by its canonical representative f_tilde=y/lambda. This representative is C1 and H2 and agrees almost everywhere with the original f. Since F is also the integral of this continuous representative, y''=-f_tilde now holds everywhere and f_tilde is C2. It satisfies

lambda f_tilde''=-f_tilde,
f_tilde'(0)=0,
f_tilde(1)=0.

Writing omega=1/sqrt(lambda)>0, the first boundary condition eliminates the sine solution, so a nonzero solution is C cos(omega x), C!=0. The second boundary condition gives cos(omega)=0, hence omega=(n-1/2)pi for exactly one integer n>=1. Therefore every nonzero eigenvalue is

lambda_n=1/[pi^2(n-1/2)^2]=4/[(2n-1)^2 pi^2].

Conversely, each cos((n-1/2)pi x) is a nonzero eigenfunction with this eigenvalue, by direct integration. The submitted Lean file independently checks these genuine forward/backward integral identities for every half-integer mode. The ODE argument shows that each eigenspace is one-dimensional.

The compact self-adjoint spectral theorem ensures that there is no other nonzero spectrum. Moreover ker(A)=ker(V)=0: if Vf=0 in L2, its continuous absolutely continuous representative F is zero almost everywhere, hence everywhere, and f=F'=0 almost everywhere. Therefore the eigenmodes exhaust L2; in particular there is no omitted component affecting the singular-value list. The values lambda_n are strictly decreasing to zero. The actual singular values of V are the nonnegative square roots of the ordered Gram eigenvalues, so

s_n(V)=sqrt(lambda_n)=2/[pi(2n-1)]=1/[pi(n-1/2)], n=1,2,... .

Zero is the accumulation point of the spectrum, not an extra nonzero singular value inserted into the ordering. This completes the actual operator, adjoint, spectral exhaustion and ordering argument, rather than merely exhibiting some eigenfunctions.

## Primary reference and the square-root distinction

Mark R. Opmeer, *Decay of singular values for infinite-dimensional systems with Gevrey regularity*, Systems & Control Letters 137 (2020), 104644, DOI 10.1016/j.sysconle.2020.104644. Stable author/repository PDF:

https://purehost.bath.ac.uk/ws/portalfiles/portal/203458869/GevreySingularValues.pdf

Actually opened and read. Example 31 appears on PDF page 23 (zero-based pageno 22; printed page 22). It defines the actual Volterra integral operator on L2(0,1) and explicitly states sigma_n(V*V)=4/[(2n-1)^2 pi^2]. Since V*V is positive, these are its eigenvalues. They are not the singular values of V itself; the positive square root is necessary. The complete independent argument above supplies the operator-theoretic justification and exhaustion, while the reference confirms the exact formula for the same actual operator.

## Exact asymptotic contradiction

For n>=1, direct algebra gives

n^2(s_n-1/(pi n))=(1/(2pi))*n/(n-1/2) -> 1/(2pi) != 0.

A standard necessary consequence of a complete odd Poincare expansion is that for some real c,

s_n=1/(pi n)+c/n^3+o(n^-3).

Multiplying by n^2 gives n^2(s_n-1/(pi n))=c/n+o(1/n)->0, a contradiction. The formal predicate `OddExpansionThroughThree` expresses exactly this necessary finite-order statement as n^3 times the remainder tending to zero. It is not declared to be a definition equivalent to the whole infinite expansion. Refuting the necessary condition refutes the asserted full odd expansion.

The actual full expansion is geometric: for every M>=0,

s_n=sum_{j=0}^M 1/[pi*2^j*n^(j+1)]
    + {1/[pi*2^(M+1)*n^(M+2)]}/{1-1/(2n)}.

Thus all integer inverse powers occur, with nonzero coefficients. If 'odd corrections' were instead read as odd powers inside the relative bracket pi*n*s_n, its expansion 1+1/(2n)+1/(4n^2)+... also has a nonzero even relative coefficient. The standard absolute odd-power interpretation is the one explicitly refuted by the formal core.

## Index conventions

Zero-based singular-value indexing gives 1/[pi(n+1/2)], whose n^-2 coefficient is -1/(2pi), still nonzero. More generally any integer reindex n -> n+k leaves an offset a=k-1/2. The formal theorem proves for every real offset a that

n^2(1/[pi(n+a)]-1/(pi n)) -> -a/pi.

For every integer k, k-1/2!=0; this is proved exactly in Lean. Therefore no integer change between ordinary ordinal conventions rescues an odd-only expansion. The half-integer variable nu=n-1/2 would make the formula exactly 1/(pi nu), but nu is not the asserted integer singular-value index n.

## Precisely what Lean proves

1. Genuine interval integrals V f(x)=integral_0^x f and the backward integral on actual functions, and their exact actions on every nonzero cosine mode with half-integer frequency. These are genuine analytic integral identities.
2. The nonnegative root of the exact Gram spectral formula, with n>=1 explicitly required.
3. The second asymptotic coefficient for an arbitrary sequence eventually equal to the reference rational formula, for any real offset, including eventual avoidance of all denominator poles.
4. A standard third-order odd Poincare condition forces the second coefficient to vanish.
5. Under the explicitly stated actual Gram spectral identity and nonnegativity, the coefficient is exactly 1/(2pi), and the odd condition is impossible.
6. Every integer reindex retains the contradiction.

`referenceFormula` is named a reference formula, not singular values. The final Lean theorem quantifies over an arbitrary sequence satisfying the public Gram spectral formula and nonnegativity; that formula is a theorem hypothesis, not a custom global assumption or an assigned definition of actual singular values.

The actual L2 extension, Hilbert adjoint, compact self-adjoint spectral exhaustion and ordering are supplied by the complete mathematical proof above and the cited primary result. They are an external substantive spectral bridge, not a pure definition and not reconstructed in Lean. The pointwise integral-mode check alone is not claimed to establish that bridge. Thus this is a complete mathematical disproof with a kernel-checked formal analytic core; it is not described as a fully formalized L2 singular-value identification.

## Adversarial author audit

1. The actual operator and domain L2(0,1) are specified. The first coefficient and indexing agree with the canonical unit-interval Volterra operator.
2. The actual Hilbert-Schmidt kernel gives boundedness and compactness; the backward integral is justified as the Hilbert adjoint by Fubini in the mathematical proof.
3. The Gram kernel is 1-max(s,t), not min(s,t). Its boundary conditions are f'(0)=0 and f(1)=0.
4. L2 eigenvectors are upgraded via the canonical representative y/lambda before applying a classical C2 ODE argument. Differentiating a merely a.e. equivalence without this step is avoided.
5. Compact positive spectral theory and the ODE classification justify exhaustion and sorting. Mere existence of a countable list of eigenfunctions is not substituted for the full singular-value sequence.
6. Opmeer states the spectrum of V*V; the positive root for V is explicit, and Lean uses both nonnegativity and n>=1.
7. Complete expansion existence is not denied. Only the asserted odd-only correction pattern is refuted; the actual all-power geometric expansion is provided.
8. The necessary odd-expansion condition is third-order, not just a first-order o(n^-1) estimate.
9. The generic reference formula is never defined to be actual singular values. Its identification with the true operator is the clearly stated external theorem bridge.
10. Pole and n=0 totalization artifacts cannot enter the limit proof: the formal arguments use eventual equality, n>=1 for the Gram formula, and eventual nonzero denominators for arbitrary offsets.
11. All ordinary integer index shifts are treated; no half-integer renaming of n is silently allowed.
12. The independent exact verifier checks rational algebra only. It proves neither Hilbert-space spectral identification nor infinite limits and is not a Lean oracle.
13. Eight printed theorem dependency lists contain only propext, Classical.choice and Quot.sound. No sorry, admit, custom axiom or native_decide occurs in the proof.

## Verification and freeze

Main: `round5/drafts/00000009778/lean/Main.lean`, frozen SHA256 `b77533cd819fc46d67762256ad07000b22299cb8e99d551fbc3ceb2b91b66e86`.

Lean 4.19.0; Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The Lake default target is Main and warningAsError is enabled. `round14/quantum/check9778.py` records actual strict/build/independent-verifier commands, cwd, exit codes, elapsed times, hashes and complete raw outputs in `9778-status.json` and `9778-*.log`.

The independent `verify.py` is an exact copy of the parent's separately written `round14/parent_verify9778.py`. It checks 33,600 rational identities after scaling out pi, across integer shifts -10 through 10, n=20 through 219, and geometric truncation orders 1 through 8, with both second- and third-order residual identities. Its explicit scope excludes the actual spectral theorem and infinite limits.

All previous problems remain frozen. No TeX, PDF, PR, shared publication state, other problem or editor state was modified by this agent.


Reviewed artifact hashes:

- Main.lean: `b77533cd819fc46d67762256ad07000b22299cb8e99d551fbc3ceb2b91b66e86`
- main.tex: `6c975d08f2d4c178541ee76bebc89a1c99edaf299f96b350f49f073137693e78`
- main.pdf: `6a5a6a5870606a746f958bfef160cc3f9924feea191798fef619d56dd407cd94`
- SOURCE.md: `863ab4780417b8861486863879baf2ebcfffe7b687a8d91d8fafd0b5a15a8b9c`
