# Initial independent semantic assessment: 00000001473

Status: the announced mathematical counterexample is valid under the supplied qualification scope. This is an initial source/mathematics assessment, not an approval of an unprovided Lean project, LaTeX report, PDF, auxiliary code, or submission compliance.

Review boundary: I read only the clean conjecture, both rules files, toolchain pin, dependency manifest, and supplied hash listing in `/private/tmp/tlmc1473-author-input`. I have not inspected other submissions, selectors, author work in progress, agent rosters, or app histories. This assessment predates access to the eventual frozen submission.

## Source statement and scope

The English and Chinese statements define proximity as the infinity-norm distance between an optimal integer solution and an optimal real-relaxation solution, and conjecture an upper bound n times Delta, where Delta is the maximal absolute value of the data, together with a sharpness claim. They do not state boundedness of the feasible region, full dimensionality, a determinant interpretation of Delta, a required representation, or any additional restrictions on the constraint matrix or objective. They do not explicitly define n; the supplied review scope takes n to be the number of decision coordinates, as is usual here.

The qualification used in this assessment is actual finite integral constraint and objective data, attained unique real and integer optima, a relaxed optimum that is a vertex, and Delta equal to the maximum absolute value of every finite numerical input: constraint coefficients, right-hand sides, objective coefficients and constant, and any finite bounds. No extra mathematical hypothesis is inferred from the name Ben-Tal–Nemirovski in the source.

## Direct three-coordinate instance

Minimize x subject to 2x >= 1, y = 10x, z = 10y, with all three coordinates integer. Relax all three coordinates to real numbers.

The real feasible points are exactly (t, 10t, 100t), t >= 1/2. The objective is t, so its unique minimum is attained at (1/2, 5, 50). This point is a vertex: in a nontrivial convex combination of feasible points giving first coordinate 1/2, each endpoint's first coordinate must be 1/2, and the equalities then fix the other coordinates.

An integer feasible point necessarily has x >= 1, since x is an integer and 2x >= 1. Conversely, each integer x >= 1 gives the integer feasible point (x,10x,100x). The integer optimum is therefore attained uniquely at (1,10,100).

The absolute coordinate differences are (1/2,5,50); the infinity distance is 50. There are n = 3 decision coordinates. The input coefficients have absolute values at most 10, and a coefficient of absolute value 10 occurs. The right-hand sides have absolute values at most 1, the objective is (1,0,0) with constant 0, and there are no finite upper bounds. Thus Delta = 10, including all finite input categories, and 50 > 3*10 = 30.

The numbers 50 and 100 in the solutions are derived values, not input coefficients, right-hand sides, or bounds. Keeping the two displayed linking equalities is important: replacing them by an input equality z = 100x would change the numerical input and hence its Delta.

## Explicit common representations

1. Mixed equality/inequality, free domains: the instance just analyzed has n=3 and Delta=10.
2. Mixed equality/inequality, nonnegative domains: adding x,y,z >= 0 changes neither feasible set nor optima, since positivity is already implied. Domain lower bounds are zero. Thus n=3 and Delta=10 still hold, with distance 50.
3. Only <= inequalities: use rows (-2,0,0), (10,-1,0), (-10,1,0), (0,10,-1), and (0,-10,1), with right-hand sides (-1,0,0,0,0). This is precisely the same three-coordinate feasible set. Optional explicit nonnegativity rows have coefficients -1 and right-hand sides 0. Delta=10 and n=3 remain unchanged. Negating every inequality gives an equivalent only >= representation with the same magnitudes.
4. Nonnegative equality standard form: use coordinates (x,y,z,s) >= 0 and equations 2x-s=1, -10x+y=0, -10y+z=0; minimize x. All four coordinates are integer in the integer program, and all four are relaxed to real numbers in the relaxation. The actual input is A = [[2,0,0,-1],[-10,1,0,0],[0,-10,1,0]], b=(1,0,0), c=(1,0,0,0), objective constant 0, and zero lower bounds. All input is integral, n=4, and Delta=10. The first three columns have determinant 2, so the equality matrix has full row rank, although no rank hypothesis is stated in the source.

For representation 4, feasible real points are exactly (t,10t,100t,2t-1) for t>=1/2. The unique relaxed optimum is (1/2,5,50,0); the unique integer optimum is (1,10,100,1). The relaxed point is again a vertex by the first-coordinate convex-combination argument. The absolute differences are (1/2,5,50,1), so the distance remains 50, and 50>4*10=40. The slack is automatically integral whenever the original coordinates are integral, and projection recovers exactly the original feasible set.

These are checks of the named representations only. They do not establish or assert invariance under arbitrary padding, variable splitting, extra slacks, coordinate elimination, rescaling, or replacement of coefficient magnitude by maximal subdeterminants. Such operations can change n, Delta, or the measured norm. In particular, adding explicit bounds involving 100 would change Delta; no such input bound is used here.

## Logical reach and remaining review

The candidate falsifies the universal upper-bound conjunct under the supplied scope. Therefore it falsifies the original conjunction, independently of the truth value of the separate existential sharpness claim. It does not purport to disprove or resolve that standalone existential claim.

The feasible region is unbounded, but both optimization problems have finite, attained, unique optima. Boundedness of the feasible region is not a source assumption. If an unstated alternative problem imposed such a requirement, that would require separate qualification rather than silently adding it to this source.

Both rules versions require full review of the entire report and full compilation/execution of Lean and any auxiliary code. Those checks remain pending until the frozen submission is supplied. The current mathematical assessment must not be used as evidence that these unperformed checks have passed.

## Exact clean-input hashes (SHA-256)

| Input | SHA-256 |
| --- | --- |
| conjectures/00000001473.md | bdceacf9b92330afb3ee49161d60a121e65ad4724d70bf332b76f7c843ba89d5 |
| RULES.en.md | 200d9a783c08a5edfd1b508e6942b3b851a63c726506291f6de6a59773f1163a |
| RULES.zh-CN.md | 7c5b49bb84403feea1eb14d23d48491400c7749d58db345cd317231949a9e82b |
| lean-toolchain | 55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea |
| lake-manifest.json | 56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637 |
| SHA256SUMS.json | 0f534b95af895ffe575cd78cad6407938bd5f8b4bae83100f6729a623e097c4d |

All five hashes recorded inside the supplied SHA256SUMS.json match independently computed file hashes. The toolchain is leanprover/lean4:v4.19.0 and the mathlib revision is c44e0c8ee63ca166450922a373c7409c5d26b00b. Dependency pins were read, not executed or modified.
