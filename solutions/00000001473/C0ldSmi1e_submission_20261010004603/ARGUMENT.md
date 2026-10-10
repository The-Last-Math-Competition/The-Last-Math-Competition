# Disproof of the explicit upper bound in conjecture 00000001473

## Claim addressed and conventions

The supplied English statement defines proximity as the coordinate infinity distance between an optimal integer solution and an optimal real-relaxation solution. It asserts the universal upper bound

\[
\|x^*-\bar x\|_\infty\le n\Delta,
\]

where the text calls Delta the maximal absolute value of the data, and also asserts a sharpness clause. The supplied Chinese version states the same upper bound and sharpness clause. The upper bound is false for finite pure integer linear programs, even when both optima are attained and unique and the real optimum is a vertex. A counterexample to this upper bound refutes its conjunction with the sharpness clause. This argument does not assert that each possible separate interpretation of the sharpness clause is false.

Here a finite pure integer linear program has finitely many decision coordinates, finitely many linear equality and inequality constraints, integral coefficients and right-hand sides, an integral linear objective (with its specified constant), and specified variable domains. Its real relaxation changes each integer coordinate to a real coordinate and retains all constraints and domain bounds. The feasible sets below are unbounded rays; the number of variables and constraints is finite, and both minima are attained. No compactness assumption is used or needed by the source statement.

For every form below, n means the actual number of decision coordinates, including any slack coordinate. Delta is computed from every explicitly supplied finite numerical datum: all matrix entries, all right-hand-side entries, all objective coefficients, the objective constant, and every finite lower or upper variable bound. An absent bound contributes no numerical value. An explicit nonnegativity bound contributes 0. Infinity norms use the actual coordinates of the particular form. Delta is not a determinant parameter. The derived values 50 and 100 in the solutions are not input coefficients.

## Form A: mixed equalities and inequalities, unrestricted variables

The integer program is

\[
\begin{array}{ll}
\operatorname{minimize} & x\
\text{subject to} & -10x+y=0,\\
                  & -10y+z=0,\\
                  & -2x\le -1,\\
                  & (x,y,z)\in\mathbb Z^3.
\end{array}
\]

There are no additional domain bounds. The objective coefficient vector is (1,0,0), and the objective constant is 0. Thus n=3. Every input datum has absolute value at most 10, and the coefficient -10 occurs, so Delta=10.

The real feasible set is exactly

\[
F_A=\{(t,10t,100t):t\in\mathbb R,\ t\ge 1/2\}.
\]

Indeed the inequality is equivalent to t>=1/2, and the two equalities successively force y=10t and z=100t. Conversely all displayed points satisfy all three rows. The objective is t. It therefore has the attained unique real minimum at

\[
\bar x_A=(1/2,5,50).
\]

The integer feasible set is exactly

\[
I_A=\{(k,10k,100k):k\in\mathbb Z,\ k\ge 1\}.
\]

For necessity, the first coordinate is an integer at least 1/2, hence at least 1. The equalities determine the other coordinates. For sufficiency, integer k>=1 gives an integer feasible triple. The objective k has the attained unique minimum at

\[
x_A^*=(1,10,100).
\]

The real optimum is a vertex. To check the defining extreme-point condition, suppose it is a convex combination with weights lambda and 1-lambda, where 0<lambda<1, of two feasible points whose first coordinates are u,v>=1/2. The first coordinate equality gives lambda*u+(1-lambda)*v=1/2. Both nonnegative quantities u-1/2 and v-1/2 must then vanish. The two feasible points are both the displayed optimum because their remaining coordinates are forced by their first coordinates.

The exact coordinate differences are (1/2,5,50). Therefore

\[
\|x_A^*-\bar x_A\|_\infty=50>30=3\cdot10=n\Delta.
\]

This already contradicts the explicit universal upper bound.

## Form B: inequalities only, unrestricted variables

Take variables (x,y,z) in Z^3, objective x with coefficient vector (1,0,0) and constant 0, no variable bounds, and A(x,y,z)^T<=b where

\[
A=\begin{pmatrix}
-2&0&0\\
-10&1&0\\
10&-1&0\\
0&-10&1\\
0&10&-1
\end{pmatrix},\qquad
b=\begin{pmatrix}-1\\0\\0\\0\\0\end{pmatrix}.
\]

The second and third inequalities together are equivalent to -10x+y=0. The fourth and fifth are equivalent to -10y+z=0. The first is unchanged from Form A. Thus the real and integer feasible sets and objectives are exactly those of Form A, and the same unique optima and vertex apply. This form has n=3, Delta=10, and distance 50>30. All five rows and all data are independently present in the Lean definition and exact arithmetic audit.

## Form C: inequalities only, nonnegative variables

Use exactly A, b and the objective of Form B, but with variables in Z_{≥0}^3; its relaxation uses R_{≥0}^3. The full domain data are the three lower bounds 0 and no upper bounds. These lower bounds are redundant, because the row constraints imply x>=1/2, y=10x>=5 and z=100x>=50. Thus the feasible sets, objectives, unique optima, and relaxation vertex again coincide with Form A. The number of coordinates is still n=3. Including the new finite bound data leaves Delta=10. The infinity distance is again 50>30.

## Form D: equalities only, nonnegative variables

Use four coordinates (x,y,z,s), objective x with coefficients (1,0,0,0) and constant 0, and the equality standard form

\[
\begin{pmatrix}
-10&1&0&0\\
0&-10&1&0\\
2&0&0&-1
\end{pmatrix}
\begin{pmatrix}x\\y\\z\\s\end{pmatrix}
=
\begin{pmatrix}0\\0\\1\end{pmatrix},
\qquad (x,y,z,s)\in\mathbb Z_{\ge0}^4.
\]

The relaxation changes the domain to R_{≥0}^4. The four finite lower bounds are 0; there are no upper bounds. All matrix and objective coefficients, all right-hand sides, the constant, and all finite bounds have absolute value at most 10, with -10 present. Thus Delta=10. The new slack is an actual decision coordinate, so n=4.

The real feasible set is precisely

\[
F_D=\{(t,10t,100t,2t-1):t\in\mathbb R,\ t\ge1/2\}.
\]

The third equality forces s=2x-1, and its lower bound s>=0 forces x>=1/2. The other equalities force y and z. Conversely this parametrization is nonnegative and satisfies every equality. The map

\[
(x,y,z)\longmapsto(x,y,z,2x-1)
\]

is a bijection between the real feasible sets of A and D, with inverse projection onto the first three coordinates. It preserves the objective and preserves integrality in both directions. The integer feasible set is consequently

\[
I_D=\{(k,10k,100k,2k-1):k\in\mathbb Z,\ k\ge1\}.
\]

Thus the unique optima are

\[
\bar x_D=(1/2,5,50,0),\qquad x_D^*=(1,10,100,1).
\]

The same first-coordinate convex-combination argument proves that the real optimum is a vertex in its four-coordinate feasible polyhedron. The exact difference vector is (1/2,5,50,1), so

\[
\|x_D^*-\bar x_D\|_\infty=50>40=4\cdot10=n\Delta.
\]

In particular, equality standard form with nonnegative integer variables does not rescue the asserted upper bound.

## Formal statement and coverage

The Lean structure `ILP n` records all rows, all finite domain bounds, the objective vector, and the objective constant. Its `feasible` predicate is the real system, and `intFeasible` restricts that exact same system to coordinatewise casts of integer vectors. `realOptimal` and `integerOptimal` require feasibility and comparison with every feasible point; their unique versions additionally require equality with every other optimum. `vertex` is the usual strict convex-combination definition of an extreme point. `data` lists all finite input entries, and `delta` is the maximum of their absolute values. The norm is Mathlib's standard norm on functions `Fin n -> Real`, namely the finite coordinate supremum norm.

The four `*_feasible` equivalences prove the real feasible-set descriptions in full. The optimum lemmas then prove global minimization and uniqueness over both integer and real domains. Each of the four `*_certificate` theorems proves, for its actual program and dimension:

1. the stated integer optimum is attained and unique;
2. the stated real optimum is attained and unique;
3. the real optimum is a vertex;
4. the full-data Delta is exactly 10;
5. the actual coordinate infinity distance is exactly 50;
6. that distance strictly exceeds n*Delta.

The explicit equivalence theorems check the three-coordinate row/domain conversions and the slack extension, inverse projection, integrality of extension, and preservation of the objective. Optima for all four forms are also proved directly from their own feasible predicates; the distance and n*Delta are checked in their own dimensions. No assertion is made that proximity is invariant under every possible encoding or change of variables.

The final theorem `Proximity.not_universalUpperBound` has actual type `Not Proximity.UniversalUpperBound`, where the latter quantifies over all finite integral-data programs and actual globally optimal integer and real solutions. The stronger restriction that both optima be unique and the real optimum be a vertex is separately refuted by `Proximity.not_uniqueVertexUpperBound`. Finally, `Proximity.not_source_conjunction` proves that adjoining any sharpness proposition to the explicit universal upper bound cannot produce a true conjunction. Its proposition parameter is not an assumed fact and is not used to supply any mathematics.

## Computational verification

The proof uses no unproved optimization oracle and no numerical approximation. Basic algebra and order reasoning characterize the full feasible sets. The fixed data magnitudes are computed by kernel-checked `decide`; arithmetic tactics produce proof terms. The exact norm proofs establish both a coordinatewise upper bound and the matching lower bound from the third coordinate.

The supplementary `exact_audit.py` uses only Python's standard-library rational arithmetic. It independently records every datum, evaluates both optima against every constraint and bound, calculates every coordinate difference and the infinity maximum, checks the strict inequality, and solves independent active-row systems to confirm full rank at the real optimum. It supports inspection; the Lean proof does not rely on its output for correctness.

The final local validation removed the project's own build directory, rebuilt successfully using the pinned stock library, and replayed `Audit.lean`, `Proximity.lean`, and `lakefile.lean` with warnings as errors. Actual theorem types and axiom dependencies are in `final-validation/22.log`; all final commands and their exit codes are in `final-validation/commands.json`. The four certificates and all three final negation/conjunction theorems depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
