# Independent mathematical review: conjecture 00000007534

Reviewed 2026-10-23 against the original bilingual statement at https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000007534.md.

## Verdict on mathematical counterexample

Valid against the unrestricted literal claim, conditional on making the geometric-cohomology identification explicit. This is the standard modular obstruction to an averaging projection, not a new failure of Maschke's theorem.

Let X = Spec(C), regarded as an R-scheme. The geometric base change is Spec(C tensor_R C), isomorphic to two copies of Spec(C). The absolute Galois group Gal(C/R) = C2 permutes these two geometric components. Hence its action on H^0_et(X_C, F2) is the swap representation on V = F2^2. This identification concerns geometric cohomology, not H^0(Gal(C/R), V), which would already be the invariant subspace.

Write the group algebra as F2[C2] = {a + b s : a,b in F2, s^2=1}. In characteristic two, (a + b s)^2 = (a+b) 1. Equating this with a + b s forces b=0; the only idempotents are therefore 0 and 1. Their actions have respective images zero and V. The invariant subspace is the nonzero proper diagonal {(0,0),(1,1)}. Consequently no group-algebra idempotent has image equal to the invariant subspace. The first necessary assertion in the conjecture is false.

## Necessary distinctions and strongest intended reading

- A nonequivariant linear projection onto the diagonal exists. The counterexample must not claim that no linear projection exists.
- The element 1+s has image equal to the diagonal, but (1+s)^2=0. It is not an idempotent projection. Thus the issue is specifically the idempotency requirement, not the existence of a group-ring map with that image.
- If the conjecture were restricted to a finite group whose order is invertible in the coefficient field, its averaging assertion would hold. The source supplies no such restriction. The disproof must explicitly state this scope rather than attack the characteristic-zero averaging theorem.
- The phrase 'representation multiplicity' has no uniquely specified modular interpretation. The first conjunct already fails; no separate refutation of that ambiguous second conjunct is needed.

## Verified primary references for the mathematical bridge

- Stacks Project, Lemma 58.2.2, https://stacks.math.columbia.edu/tag/04JI : schemes etale over a field correspond to discrete absolute-Galois sets; a finite separable field extension maps to its set of embeddings in a separable closure.
- Stacks Project, Lemma 59.59.2 and Example 59.59.3, https://stacks.math.columbia.edu/tag/03QQ : cohomology of a field and constant finite coefficients. Applied to the algebraically closed components, H^0 is F2 on each component.

These sources were read directly. The explicit splitting C tensor_R C = C x C and its two embeddings give the swap action without requiring a deep comparison theorem.

## Formal coverage requirements

The Lean project should construct the actual convolution multiplication, swap action, invariant predicate, image predicate, idempotency, and universal nonexistence theorem. Any finite degree-zero cochain realization must compute its cohomology rather than merely assign a desired dimension. If schemes, complex/real fields, etale sites and the geometric H^0 identification are not mechanized, that boundary must be stated. A finite module certificate alone does not constitute a formalized general etale-cohomology comparison.

## Completed formal and document review

Read the entire final Lean source and entire LaTeX argument, and visually inspected both final rendered PDF pages. No mathematical or formal blocker was found. The written argument explicitly supplies the geometric realization and openly states that schemes, real/complex fields and the etale comparison are not mechanized. The source now includes the two-vertex function/coordinate correspondence and proves that swapping coordinates is the permutation pullback action. It computes the boundary quotient and transfers the actual invariant-image obstruction to it. In particular, the conclusion is not merely a stronger retraction property substituted for image equality.

Independent compilation of a copied source with Lean 4.31.0 and warningAsError=true succeeded. Independent leanchecker replay of the compiled module succeeded with exit code zero. The complete named-theorem audit covers 55 theorems: 54 have no axioms, and evaluate_from uses only the standard Quot.sound axiom through functional extensionality. The main counterexample has no axioms. There is no sorry, custom axiom, native_decide, or kernel bypass in the reviewed source. See final-compile.log, final-kernel.log, and final-all-theorems-audit.log in this review directory.

Reviewed Lean source SHA256: 4b35b7378e2629ab3616447cef450bff891f0fa7ea6692f9f9946667654478be.

Final reviewed LaTeX SHA256: 032b2ceb254fd4c79d8cac9209811060029fb841533b1909837d5f156221c8f2.

Final reviewed PDF SHA256: 751dc079000d7b3709bff3bb7fa323322a8e614298f938df08a2003a6cffbbd7.

The final two-page PDF was visually re-inspected after a layout-only improvement. Both pages are legible without clipping or overlap; references now fit on page two. The final scope paragraph explicitly excludes claims about characteristic-zero/Q_l or geometrically connected reformulations.

Scope for acceptance remains important: the source omits coefficient characteristic, cohomological degree, and geometric connectedness. This example uses degree zero, modular F2 coefficients, and a finite-etale scheme connected over R but geometrically disconnected. It refutes the literal unrestricted assertion, not a characteristic-zero/Q_l or semisimple reformulation. No contest acceptance or score credit is implied by this independent review.
