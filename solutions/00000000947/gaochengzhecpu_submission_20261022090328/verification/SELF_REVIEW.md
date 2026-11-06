# Author-agent adversarial self-review: 00000000947

Verdict: PASS

# 947 — the fixed-dimensional lower modulus envelope is zero

## Scope and source

The exact bilingual source is `round5/source/00000000947.md`, fetched by the parent from the current checked upstream commit. It asserts that the optimal lower envelope of the modulus of uniform convexity over spaces of fixed dimension is attained by an explicitly selected `l_q^n`, with `q` tending to 2 as epsilon tends to zero.

We disprove this already in dimension 2. The source imposes no restriction to uniformly convex norms. We also prove a stronger statement that addresses precisely that potential alternative reading: even among genuinely uniformly convex `l_q^2` spaces, the infimum is zero for every fixed `0 < epsilon < 2`, and every finite `1 < q < infinity` has strictly positive modulus. Thus no such finite q attains the lower envelope. Convergence of a proposed selected q to 2 forces finite q greater than 1 for sufficiently small positive epsilon, giving a direct contradiction. No conclusion about the source's separate large-epsilon asymptotics or endpoint slopes is needed.

## Definitions: all objects are the actual geometric ones

Let E be the real vector space `Fin 2 -> R`. Its dimension is 2. A function N:E->R is accepted by `IsNorm` precisely when it satisfies nonnegativity, positive definiteness, the triangle inequality, and absolute homogeneity. These are the usual real norm axioms, not an assigned modulus or a restricted family of norms.

For such a genuine norm define

```
P_N(epsilon) = {(x,y): N(x)=N(y)=1 and N(x-y)>=epsilon},
D_N(x,y) = 1 - N((x+y)/2),
delta_N(epsilon) = inf {D_N(x,y):(x,y) in P_N(epsilon)}.
```

This is the standard unit-sphere version of Clarkson's modulus. The actual Lean definition uses `sInf` of the image of the entire admissible unit-pair set. It is not restricted to selected symmetric test pairs. The standard definition and background can be cited to E. Llorens Fuster, *Moduli and Constants* (2006), section 1, https://www.uv.es/~llorens/Documento.pdf (the parent opened this primary author survey).

For every norm N and every epsilon<=2 the admissible set is nonempty: normalize any nonzero vector e to x=e/N(e), and use (x,-x), whose distance is 2. This fact is checked in `pairs_nonempty`; it explicitly excludes empty-infimum artefacts throughout the intended domain.

The triangle inequality gives N((x+y)/2)<=1 on the admissible pairs. Therefore every defect and every modulus is nonnegative. The outer lower envelope is the actual sInf over the set of the moduli of all genuine norms on E.

## First counterexample: exact zero envelope

For the standard sup norm, take

```
u=(1,epsilon/2), v=(1,-epsilon/2).
```

For 0<=epsilon<=2 both have norm 1, their distance is exactly epsilon, and their midpoint (1,0) has norm 1. Their defect is zero. Combining this admissible pair with the lower bound for every defect proves the exact identity

```
delta_infinity(epsilon)=0,
inf_all_two_dimensional_norms delta_N(epsilon)=0.
```

Lean theorems: `infinity_pair`, `infinity_modulus_zero`, and `envelope_zero`.

## Every finite l_q, q>1, has strictly positive actual modulus

The norm `lpNorm p x` is literally the Mathlib norm of x in `PiLp p (fun _:Fin 2 => R)`, pulled back by the canonical `WithLp.equiv`. For finite p with 1<p.toReal it is the genuine norm

```
N_p(x) = (|x_0|^p+|x_1|^p)^(1/p).
```

`lp_isNorm` checks all four norm axioms, `lpNorm_rpow` checks the exact sum-of-real-powers formula, and `continuous_lpNorm` uses the actual Mathlib topology.

For real a != b and p>1,

```
|(a+b)/2|^p < (|a|^p+|b|^p)/2.
```

If the absolute values differ, use strict convexity of the real p-th power on the nonnegative real axis, plus the absolute-value triangle inequality. If the absolute values are equal but a!=b, then a=-b!=0, and the left side is zero while the right side is strictly positive. The non-strict inequality holds without the distinctness assumption. These two scalar statements are proved in `abs_mid_rpow_le` and `abs_mid_rpow_lt` using the proved Mathlib theorem `strictConvexOn_rpow`.

For distinct unit vectors x,y at least one coordinate differs. Summing the coordinate inequalities gives N_p((x+y)/2)^p<1 and therefore N_p((x+y)/2)<1. This is `lp_mid_lt`.

For fixed positive epsilon<=2, the actual admissible pair set is nonempty, closed, and bounded in R^2 x R^2. The coordinate bounds follow from `PiLp.norm_apply_le`, so it is a closed subset of the ordinary sup-norm closed unit ball. It is compact. The actual continuous defect achieves a minimum there. All pairs have distinct entries because their distance is at least epsilon>0, so the attained minimum is strictly positive. The minimum is a lower bound on the genuine sInf. This proves `lp_modulus_pos`. There is no unproved general-p `UniformConvexSpace` assumption in this argument.

`lp_uniformConvex` subsequently constructs an actual Mathlib `UniformConvexSpace` instance from this proved positive modulus, with the norm-sum deficit twice the midpoint deficit. For epsilon>2 there can be no unit pairs, by the triangle inequality; that branch is proved separately.

It follows that no finite 1<p<infinity can attain the zero envelope at any epsilon in (0,2]. This is `no_finite_lp_minimizer`.

## Direct refutation of q(epsilon) -> 2

`no_selector_tending_two` allows arbitrary pointwise selection of extended exponents p(epsilon)>=1 and assumes only

```
(p(epsilon)).toReal -> 2 as epsilon -> 0+.
```

Eventually (p(epsilon)).toReal>1, and eventually epsilon<2. The right-neighborhood filter of zero is nontrivial, so some positive epsilon satisfies both. The strictly positive l_p modulus at this epsilon contradicts attainment of the zero envelope. Extended exponent infinity has real conversion zero, and therefore cannot appear among these eventual exponents. This is a necessary local consequence of the source's asserted limit, so refuting it refutes the source's conjunction.

## Stronger check: restricting the lower envelope to UC spaces does not repair it

For any finite p>1 set k=2^(1/p), and use the genuine l_p unit vectors

```
x=(1,1)/k, y=(1,-1)/k.
```

Their distance is 2/k, their midpoint norm is 1/k, and their defect is 1-1/k. Thus, whenever epsilon<=2/k,

```
delta_p(epsilon) <= 1-2^(-1/p).
```

This is only an upper bound; `lp_trial_bound` does not assert it equals the exact modulus. As p->infinity, 1/k->1. For every fixed 0<epsilon<2 and every eta>0, choose a real q>=2 large enough that 2/k>epsilon and 1-1/k<eta. Lean proves the real-power limit and these eventual inequalities and then produces this actual q, its actual `UniformConvexSpace (PiLp ...)` proof, and

```
0 < delta_q(epsilon) < eta.
```

This is `arbitrarily_small_uniformly_convex_lp`. Together with nonnegativity for every norm, it proves that even the envelope over only UC norms is zero on (0,2), while each finite q>1 remains strictly above it. The endpoint epsilon=2 is deliberately excluded from this stronger approximation statement; its geometry differs, and no assertion about it is needed.

## Author adversarial review (not an independent external review)

- Checked exact source quantifiers: fixed dimension includes dimension 2; no uniform convexity hypothesis is present. The additional UC result makes that interpretation immaterial on the relevant small-epsilon interval.
- The infimum is over all admissible unit pairs and over all genuine real norms; no proxy value is assigned to a modulus.
- Explicit `pairs_nonempty` checks all true norms in the physical domain. The proof does not obtain its zero value from Lean's convention for the infimum of an empty real set.
- Norms `infinityNorm` and `lpNorm` are the actual Mathlib sup and l_p norms on the actual fixed coordinate vector space. `IsNorm` is exactly the conventional real norm axiom list.
- Strict midpoint inequality is proved for arbitrary coordinate signs, including the equal-absolute-value/opposite-sign case, and then arbitrary distinct input vectors. It does not only cover a symmetric ansatz.
- Pointwise strictly positive defects alone would not prove a positive infimum. Compactness plus an attained minimum is used explicitly, avoiding this common gap.
- `lp_modulus_pos` proves the true infimum is positive without assuming the unavailable general-p uniformly-convex-space instance. The actual UC instance is then derived from the result.
- The proposed selected exponent need not equal 2 exactly; convergence to 2 merely forces it eventually into the entire open range 1<p<infinity. The proof handles that full range.
- For the UC strengthening, the selected pair supplies only an upper bound. Both its unit norms and its separation are checked exactly before it is used.
- The q->infinity limit in the UC strengthening is an actual proved real-power limit, not a numerical experiment. It is only used for fixed epsilon<2.
- Auxiliary computations and floating-point estimates are unnecessary. No Python verifier is needed.
- There is no `sorry`, `admit`, `native_decide`, custom axiom, private unsafe evaluator, or assumption of the desired conclusion in the Lean source. The final strict audit prints the axioms of all eight principal theorems.
- Parent adversarial review is still required before publication. This report is the proof author's self-review and must not be described as an independent review.

## Reproduction and handoff

Pinned environment: Lean 4.19.0 and official Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

`round13/other/check_947.py` runs the actual `lake build`, followed by the actual command `lake env lean -DwarningAsError=true Main.lean`. It stores unmodified build and strict output as `947-build.log` and `947-strict.log`, and timestamps, complete command arrays, return codes, elapsed times, and SHA-256 evidence in `947-checks.json`.

The parent must create the LaTeX/PDF, do its own adversarial review and clean fresh build, preserve exact bilingual source provenance, and handle any authorized one-problem PR. This agent did not author a PDF, publish anything, or touch global snapshot/publication state.

## Frozen verification evidence

- Main.lean SHA-256: `f5b3ff8ae00f914bd1c1b9be9ef601c5677cd4e0a7994412fb5ce774ed478472`
- Exact source SHA-256: `5605d421822f30e1768eec5caa9d6845e82862564fe85ae01a7c80465fd39fc8`
- Actual lake build: exit 0, 20.656 seconds.
- Actual strict Lean: exit 0, 20.281 seconds.
- Both checks ran on the same unchanged Main.lean hash.
- Eight printed principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.


Reviewed artifact hashes:

- Main.lean: `f5b3ff8ae00f914bd1c1b9be9ef601c5677cd4e0a7994412fb5ce774ed478472`
- main.tex: `91d605b273291b8670458ec6605b66f95deee5ea4bc0c3fda8b36df96c5f4d33`
- main.pdf: `e4d362cc921ec3dd7e9bfc21a22aef2f339d2b7369c0c29eeda38a28c59151ee`
- SOURCE.md: `5605d421822f30e1768eec5caa9d6845e82862564fe85ae01a7c80465fd39fc8`
