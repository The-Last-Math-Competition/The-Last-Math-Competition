# Author-agent adversarial self-review: 00000000998

Verdict: PASS

# Conjecture 998: transpose amplification counterexample

Status: AUTHOR REVIEW PASS; actual strict Lean check exit 0. Parent review and fresh publication build remain parent responsibilities. No independent external reviewer is claimed.

## Exact target and interpretation

The exact bilingual source is `round5/source/00000000998.md`. It asserts that the supremum of completely bounded norm divided by ordinary operator norm on the observable algebra of three qubits equals sqrt(2). Three qubits have Hilbert space C^8 and observable C*-algebra M_8(C). Under the standard convention this is the ratio for nonzero completely bounded complex-linear maps T:M_8(C)->M_8(C).

The source does not restrict to completely positive maps or quantum channels. This distinction matters: the counterexample is the transpose map, not a channel. It is complex-linear, unital, positive, star-preserving, and bounded, but not completely positive. The Lean proof only needs its complex linearity and complete boundedness.

## Self-contained mathematical proof

All matrix norms below are the operator norms induced by the Euclidean norm on the corresponding complex Hilbert spaces. The norm of T as a map between these normed matrix spaces is its usual bounded-linear-operator norm.

Let tau(A)=A^T for A in M_8(C). Transposition is a star-algebra isomorphism from M_8(C) to the opposite C*-algebra and therefore preserves the C*-norm. Since tau(I)=I, ||tau||=1. Lean uses Matrix.transposeAlgEquiv and a star-preserving extension, then the standard isometry theorem for star-algebra equivalences. No entrywise sup or Frobenius norm is substituted.

For every natural k, use the actual block amplification T_k=id_{M_k} tensor T. With row indices (a,i) and column indices (b,j),

    (T_k X)[(a,i),(b,j)] = T(X_ab)[i,j],
    (X_ab)[i,j] = X[(a,i),(b,j)].

Write B_ij=I_k tensor E_ij. Direct entry computations give

    tau_k(X) = sum_(i,j=0)^7 B_ij X B_ij.

Every B_ij is a partial isometry and has norm at most one: B_ij^* B_ij=B_jj, B_jj^*=B_jj, and B_jj^2=B_jj. The C*-identity gives ||B_jj||^2=||B_jj||, hence ||B_jj||<=1, followed by ||B_ij||^2=||B_jj||<=1. The triangle and product inequalities therefore show

    ||tau_k(X)|| <= 64 ||X||

uniformly over every k and X. In particular tau is genuinely completely bounded and its cb supremum is a finite real number, not an unbounded conditional sSup default.

At amplification size k=8 take the swap matrix F indexed by pairs:

    F[(a,i),(b,j)] = 1 if a=j and i=b, and 0 otherwise.

Equivalently F=sum E_ab tensor E_ba. The actual finite matrix identities F^*=F and F^2=I imply ||F||=1 by the C*-identity. Let Omega=sum_(i=0)^7 e_i tensor e_i, a nonzero vector in C^64. Direct multiplication shows

    tau_8(F) Omega = 8 Omega.

The Euclidean operator norm inequality gives ||tau_8(F)||>=8. Consequently

    8 <= ||tau||_cb <= 64,   ||tau||=1,
    ||tau||_cb / ||tau|| >= 8 > sqrt(2).

Thus sqrt(2) is not even an upper bound for the ratio set and cannot be its supremum. No exact value of the global ratio supremum or of ||tau||_cb is required or claimed as a formal theorem here. The familiar sharp value ||tau||_cb=8 is compatible with, but stronger than, what this submission needs.

## Definitions and theorem mapping

`open scoped Matrix.L2OpNorm` selects Mathlib's Euclidean operator norm for every matrix size. `Matrix.l2_opNorm_def` and `Matrix.cstar_norm_def` identify that norm with the norm of the corresponding continuous linear operator on EuclideanSpace.

- `Obs` is literally Matrix (Fin 8) (Fin 8) Complex.
- `transposeMap : Obs ->L[Complex] Obs` is the bounded complex-linear transpose map.
- `transpose_norm`, `transposeMap_norm`: exact matrix isometry and ordinary map norm one.
- `amplify`: actual blockwise application of the given linear map to each M_8 block, with product indices for the matrix on C^k tensor C^8.
- `blockUnit_star`, `blockUnit_mul`, `blockUnit_norm_le`: exact matrix-unit identities and uniform contraction bound.
- `amplify_transpose_sum`, `amplify_transpose_bound`: actual all-k amplification formula and uniform bound 64.
- `swapMatrix`, `swap_star`, `swap_square`, `swap_norm`: literal 64-by-64 complex swap matrix and norm one.
- `omega`, `omega_nonzero`, `amplified_swap_eigen`: literal nonzero Euclidean vector and exact eigenvalue equation.
- `amplification_norm_lower`: actual amplified matrix norm at least eight.
- `amplificationRatios T` contains ||T_k X||/||X|| for all k and all actual complex matrices X.
- `CompletelyBounded T` means this set is bounded above, equivalent to uniform boundedness of the amplification operator norms. `cbNorm T` is its real sSup.
- `transpose_completelyBounded`: explicit upper bound 64 for this set.
- `transpose_cbNorm_lower`, `transpose_cbNorm_upper`: genuine sSup inequalities 8<=cbNorm(tau)<=64.
- `cbRatios`: ratios cbNorm(T)/||T|| of nonzero completely bounded maps on M_8(C).
- `counterexample`: an actual member of this ratio set exceeds sqrt(2).
- `not_upperBound`: sqrt(2) is not an upper bound.
- `not_claimed_supremum`: not IsLUB cbRatios sqrt(2), directly refuting the claimed supremum value.

The ratio convention at X=0 uses Lean's division by zero value 0. This only inserts zero into the amplification ratio set; it does not change the standard supremum, whose nonnegative values arise from nonzero X. k=0 likewise contributes only zero and has no effect. The lower-bound argument uses k=8 and the explicitly nonzero norm-one F. The ordinary-map denominator is exactly one, so no zero-map division occurs in the counterexample.

## Author adversarial review

1. **Correct norm? PASS.** The scoped L2OpNorm is the C*-norm transported from continuous linear operators on EuclideanSpace. It is not Matrix's default entrywise norm. Every norm statement and the CLM domain/codomain are constructed under this scope.
2. **Actual map, not an abstract number? PASS.** Transpose is an explicit complex-linear continuous map on literal M_8(C). No assumption supplies its norm or cb norm.
3. **Correct three-qubit algebra? PASS.** C^2 tensor C^2 tensor C^2 has complex dimension 8; its full observable algebra is M_8(C). The problem specifies no smaller commutative algebra or channel restriction.
4. **Correct amplification? PASS.** Each (a,b) block is transformed by tau, so the outer k indices remain fixed and only the inner 8-by-8 block indices are transposed. The witness is not full transposition on M_64.
5. **Finite actual cb norm? PASS.** A single amplification would not suffice to show complete boundedness. The proof supplies an all-k norm bound via 64 genuine sandwich terms, proving BddAbove before using le_csSup. csSup_le also receives an actual nonempty set witness.
6. **Nonzero witness? PASS.** F^2=I, ||F||=1. Omega_(0,0)=1 is proved, so cancellation in the eigenvector norm inequality is justified.
7. **Correct supremacy negation? PASS.** A supremum in the order-theoretic sense must be an upper bound. The final theorem refutes IsLUB of the full actual cb ratio set at sqrt(2), via an explicit legitimate map. It does not rely on a conditional real sSup for the global ratio set, and does not pretend to prove that global supremum equals eight.
8. **No semantic overclaim? PASS.** The formal result is a counterexample to the claimed constant; the sharp transpose cb norm or universal sharp bound is not advertised as formalized. tau is not called a physical quantum channel.
9. **All auxiliary computation? PASS.** verify.py uses exact Python integers to independently check swap/partial-transpose/rank-one identities for dimensions 2 and 8. It is auxiliary only; every needed norm inequality is proved by Lean.
10. **Proof trust? PASS.** Strict Lean command actually ran with exit zero. Printed axioms of the ordinary norm, uniform amplification bound, cb lower bound and final negation contain only propext, Classical.choice, Quot.sound. No sorry, admit, native_decide, custom axioms, or numerical oracle is used.

## Actual verification evidence

Lean toolchain: leanprover/lean4:v4.19.0.
Mathlib pinned revision: c44e0c8ee63ca166450922a373c7409c5d26b00b.
Strict command from the project directory:

    PY -X utf8 ../../../../round7/run_safe.py ../../../../tools/lean-4.19.0-windows/bin/lake.exe env lean -DwarningAsError=true Main.lean

Actual final strict result: exit 0, 23.031 seconds.
Actual complete `lake build` result: exit 0, 36.641 seconds, target Main built successfully with all four printed axiom lists unchanged. Log: `round13/quantum/998-lake-build.log`.
`round13/quantum/998-strict.log` contains the four real #print axioms outputs.
`round13/quantum/998-status.json` records command, exit code, elapsed time and source hash.
`round13/quantum/998-verify.log` records actual successful auxiliary output.

Main.lean SHA256:
0aadb3431e4b81e8e3e873fffdb555d2e012e4a596f5e07419ef15a47cd705d3

verify.py SHA256:
84c5b80c64d0af8fe3bce1a6aac85b0465032f29de86fbe705f384ed617a4b80

## Primary reference for established background

Vern Paulsen, *Completely Bounded Maps and Operator Algebras*, Cambridge University Press, Chapter 1, printed pages 4-5 (matrix norms, amplification, cb definition and transpose example), Exercises 1.7-1.9 on printed page 8 (swap, rank-one partial transpose, transpose isometry). Publisher excerpt personally opened and searched:
https://assets.cambridge.org/97805218/16694/excerpt/9780521816694_excerpt.pdf

This is a standard counterexample applied to the competition's asserted constant, not a new result about transpose maps. The proof above is self-contained and Lean does not import any theorem asserting the transpose cb norm.

## Handoff limits

No TeX/PDF has been created by this agent. No PR, publication state, global snapshot, or parent publishing script has been modified. Parent owns final paper, PDF, source provenance, full fresh build, parent adversarial review and upload. This agent is finished with its one assigned problem and will not open another.


Reviewed artifact hashes:

- Main.lean: `0aadb3431e4b81e8e3e873fffdb555d2e012e4a596f5e07419ef15a47cd705d3`
- main.tex: `57205d3c05b7083d6bc8af21569bbb09d025d53b9e878eae4822d8da6996e742`
- main.pdf: `774da22e1b2d49a05fd96a21d3d9cf20c61ada9ed4ac2761a64d5c248723bb4d`
- SOURCE.md: `5ff0e7ca839c1e1828c83beb5eb1402f132afff44a1e6082194542e45451b3e3`
