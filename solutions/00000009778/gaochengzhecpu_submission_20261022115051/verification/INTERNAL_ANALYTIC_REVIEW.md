# 9778 — independent analytic proof review of the actual Volterra spectrum

**Verdict: the real L² spectral bridge is mathematically valid with the proof below.** The parent has explicitly allowed a substantive external spectral-theorem bridge, provided the full mathematical proof and the formalization boundary are honest. This review therefore does not demand that Lean reconstruct all of Hilbert-space spectral theory. It does require that the paper distinguish the complete mathematical operator proof from the conditional Lean asymptotic theorem and the proved pointwise mode identities.

Only this review file was written. No quantum-author file, frozen source, shared progress record, new problem, or subagent was created or modified. Read the exact bilingual source, the current `lean/Main.lean`, the graph agent's initial review, and the parent's exact-algebra verifier.

## 1. Actual Hilbert-space operator, boundedness and compactness

Take H=L²((0,1);C), with Lebesgue measure; the same proof works over R. For f in H define its canonical primitive

    F(x) = integral_0^x f(t) dt,     0<=x<=1,
    Vf = the L² class of F.

Because L²(0,1) is contained in L¹(0,1), F is an absolutely continuous function on [0,1], F(0)=0, and F'=f almost everywhere. Its definition is independent of the representative of f. Moreover

    |F(x)| <= sqrt(x) ||f||_2,
    ||Vf||_2² <= (1/2)||f||_2².

Thus V is a genuine bounded linear operator on the actual L² space. Its kernel is the actual triangle indicator

    K(x,t)=1_{0<=t<=x<=1}.

The integral of |K|² over the unit square is 1/2. The Hilbert–Schmidt integral-operator theorem therefore gives ||V||_HS²=1/2 and compactness. Diagonal or endpoint conventions for the indicator change it only on null sets. This applies the standard theorem to a checked square-integrable kernel; it does not merely label a pointwise function map “compact”.

For an optional direct compactness proof, |F(x)-F(z)|<=sqrt(|x-z|)||f||_2 gives uniform boundedness and equicontinuity of primitives of an L²-bounded set. Arzelà–Ascoli gives a uniformly convergent subsequence, hence an L²-convergent one.

## 2. The adjoint and the correct Gram kernel

Use the inner product linear in the first argument. For f,g in H, the absolute double integral in the following interchange is finite, since it is at most ||f||_1||g||_1. Fubini gives

    <Vf,g>
      = integral_0^1 integral_0^x f(t) conjugate(g(x)) dt dx
      = integral_0^1 f(t) conjugate(integral_t^1 g(x) dx) dt.

The backward integral belongs to L², for example by its analogous Cauchy–Schwarz bound. Consequently the actual Hilbert-space adjoint is

    (V*g)(x) = integral_x^1 g(t) dt.

Set A=V*V. It is bounded, compact, self-adjoint and positive, with

    <Af,f>=||Vf||_2².

Another justified Fubini interchange gives its canonical integral formula

    (Af)(x) = integral_0^1 (1-max(x,t)) f(t) dt
            = integral_x^1 F(s) ds.

For fixed x, absolute integrability of the relevant triangular double integral is bounded by ||f||_1. The kernel is **1-max(x,t)**, not min(x,t). The latter is the kernel of VV*, which has the opposite mixed boundary conditions.

## 3. Precise regularity and boundary conditions for arbitrary L² input

Let y(x)=integral_x^1 F(s) ds be the canonical representative of Af. Since F is continuous,

    y in C¹([0,1]),
    y'(x)=-F(x) for every x,
    y' is absolutely continuous,
    y''=-f almost everywhere,
    y'(0)=0,      y(1)=0.

At endpoints, derivatives are understood as the appropriate one-sided traces. In particular y belongs to H²(0,1). Both weak derivatives are in L²; y and y' are also bounded on this finite interval.

**For general L² f, do not state that y''=-f holds classically at every point or that f is C².** The eigenvalue equation supplies the necessary regularity upgrade; it is not legitimate to differentiate an arbitrary L² representative twice.

## 4. Eigenfunction bootstrap before solving the classical ODE

Suppose f is a nonzero L² eigenvector and Af=lambda f as an equality of L² classes. Positivity implies lambda is real and nonnegative. In fact lambda>0: if Af=0, then ||Vf||_2=0; the continuous primitive F is zero almost everywhere and hence identically zero, so f=F'=0 almost everywhere. Thus ker A=ker V={0}.

Define a new, canonical representative

    f_tilde(x)=y(x)/lambda.

The eigenvalue equation says f_tilde=f almost everywhere, and the preceding section gives f_tilde in C¹ and H². Since changing representatives does not change integrals,

    F(x)=integral_0^x f_tilde(t) dt

for every x. Now f_tilde is continuous, so the ordinary fundamental theorem of calculus gives F'=f_tilde at every point. Since y'=-F everywhere, y is C² and

    y''=-f_tilde everywhere.

Dividing by lambda yields the genuine classical boundary-value problem

    f_tilde'' + lambda^(-1) f_tilde = 0,
    f_tilde'(0)=0,       f_tilde(1)=0.

This is the required L²-to-classical bootstrap. Further smoothness follows by repeatedly using the differential equation, but C² already suffices. One may alternatively formulate the intermediate step entirely in Sobolev language; the explicit primitive argument avoids relying on an unstated embedding theorem.

## 5. Classifying every possible eigenfunction

Put omega=lambda^(-1/2)>0. The general real or complex C² solution is

    f_tilde(x)=a cos(omega x)+b sin(omega x).

The derivative boundary condition gives b=0. Nonzeroness gives a!=0, and the endpoint boundary condition forces cos(omega)=0. Hence, uniquely for some n>=1,

    omega_n=(n-1/2)pi,
    lambda_n=omega_n^(-2),
    f_tilde(x)=a cos(omega_n x).

Thus every possible nonzero eigenvalue has the displayed form, and each corresponding eigenspace has dimension at most one. This classification applies to **all** L² eigenvectors because the regularity argument was proved first.

## 6. Converse, exhaustion, multiplicity and ordering

Every displayed mode is genuinely present. Direct integration, using cos(omega_n)=0, gives

    V(cos(omega_n x)) = sin(omega_n x)/omega_n,
    V*V(cos(omega_n x)) = cos(omega_n x)/omega_n².

These modes are nonzero. Therefore every lambda_n is an eigenvalue and its eigenspace is exactly one-dimensional.

The compact self-adjoint spectral theorem states that H is the orthogonal direct sum of ker A and the closed span of its eigenspaces for nonzero eigenvalues. The kernel has already been proved zero. The preceding classification and converse identify every such eigenspace. Consequently

    e_n(x)=sqrt(2) cos((n-1/2)pi x),   n>=1,

form a complete orthonormal eigenbasis. Normalization follows from the elementary cosine-square integral; orthogonality also follows from self-adjointness and distinct eigenvalues. **The argument does not jump from “we found some cosine eigenfunctions” to “these are the whole spectrum”.** Exhaustion uses the theorem together with the complete eigenfunction classification and the zero-kernel proof.

The eigenvalues lambda_n=1/[pi²(n-1/2)²] strictly decrease to zero. Each occurs once, by the one-dimensional eigenspace calculation. Zero is an accumulation point of the compact spectrum but is not an eigenvalue. There are no extra positive eigenvalues, negative eigenvalues, complex eigenvalues, or hidden zero-eigenspace contributions.

By the definition of singular values of a compact operator, the decreasing positive singular values of V, repeated with multiplicity, are the positive square roots of these eigenvalues of V*V. Thus the **actual sorted singular-value list**, with ordinary one-based indexing, is

    s_n(V)=1/[pi(n-1/2)]=2/[pi(2n-1)],  n=1,2,... .

Equivalently, the actual ordered Gram spectral values are

    s_n(V)²=lambda_n=4/[(2n-1)² pi²].

Do not confuse this Gram list with the singular values of V itself. The first is squared relative to the second.

If a complete SVD is desired, put h_n(x)=sqrt(2)sin(omega_n x). Then Ve_n=s_n h_n and V*h_n=s_n e_n. The h_n are orthonormal by the Gram identity. They are complete because ker V*={0}: a vanishing backward primitive is continuous and hence identically zero, and its almost-everywhere derivative is -g. Boundedness of V then gives the L²-convergent SVD expansion from the input orthonormal basis.

## 7. Consequence for the source and exact Lean boundary

For the actual one-based list,

    n² (s_n(V)-1/(pi n)) = n/[pi(2n-1)] -> 1/(2pi) != 0.

This rules out an odd-only absolute inverse-power Poincaré expansion. Already the necessary truncation s_n=1/(pi n)+c/n³+o(n^-3) would force the displayed scaled residual to tend to zero. The full unrestricted inverse-power expansion does exist; the source is refuted by its **odd-only parity clause**, not by nonexistence of an expansion. No Bernoulli-coefficient assertion needs to be settled after that clause fails.

The current Lean file proves actual interval-integral identities for all half-integer cosine modes, positive-square-root extraction from the ordered Gram identity, and the resulting asymptotic contradiction for every sequence satisfying that identity. Its pointwise `volterra` and `backwardIntegral` definitions on functions are genuine integrals, but they do **not** construct the Hilbert-space quotient operator, prove its Hilbert–Schmidt compactness or adjoint theorem, or identify its entire ordered singular-value sequence. Those are substantive external mathematical steps, established above and not supplied as Lean axioms.

Accordingly the final paper may correctly say: “The mathematical L² argument identifies the actual singular values; Lean verifies the mode-integral identities and the conditional asymptotic consequence of that identification.” It should not say that Lean itself proves the actual L² spectral exhaustion or that a prescribed numerical sequence is defined to be the singular values. The parent has authorized this precise external-theorem scope.

## 8. Primary references personally checked

1. [Joel H. Shapiro, *SVD For the Volterra Operator*, Portland State University Analysis Seminar, 17 February 2023](https://joelshapiro.org/Pubvit/Downloads/joel_volterra2.pdf). Opened the author's PDF. PDF pages 6–8 give the Gram spectral decomposition and SVD. Its regularity upgrade is left as an exercise; Section 4 above supplies the explicit canonical-representative argument needed in the paper.
2. [Mark R. Opmeer, *Decay of singular values for infinite-dimensional systems with Gevrey regularity*, Systems & Control Letters 137 (2020), 104644, institutional peer-reviewed manuscript](https://purehost.bath.ac.uk/ws/portalfiles/portal/203458869/GevreySingularValues.pdf), Example 31, PDF page 23 / printed page 22. Personally reopened it. The example gives the actual L² Volterra operator and its ordered Gram spectral values, consistent with the independently derived formula above.

The proof supplied here checks the analytic bridge rather than relying solely on a search-result formula. It does not require a new Lean development or changes to the author's files.

## 9. Subsequent check of the parent's new main.tex

Read the parent's full newly written paper, including the actual operator and spectral proof on pages 1–2. Reviewed `main.tex` SHA256: `c2ed2247e873261e2e3f465b65ae47c566710919cc9bb1df1aad483da84043c1`.

**PASS; no required correction found.** The paper checks the genuine Hilbert–Schmidt kernel, gives the correct adjoint and Gram kernel, states the a.e. derivative for general L² input, selects the eigenfunction representative y/lambda before the classical ODE, derives the correct mixed boundary conditions, classifies all nonzero eigenfunctions, verifies every mode conversely, proves the zero kernel, and invokes the compact self-adjoint theorem on A rather than V. Simplicity and strict ordering are sufficient to identify the actual sorted singular values. The asymptotic parity conclusion, integer shifts and explicit Lean-versus-L² boundary are consistent with the reviewed core. No paper, source, or other author file was modified.
