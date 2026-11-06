# Author-agent adversarial self-review: 00000007991

Verdict: PASS

# 7991 — a nonnegative exponent cannot have slope tending to minus infinity at infinity

## Exact source claim and disproof scope

The exact bilingual source is `round5/source/00000007991.md`, fetched and checked for previous submissions by the parent. It concerns the optimal exponent alpha(p) in C^{1,alpha} regularity for the p-Laplace equation and asserts, among other things, that the slope of the graph of alpha(p) tends to minus infinity as p tends to infinity.

That asserted endpoint behavior is impossible for **any** eventually lower-bounded real graph. In particular a regularity exponent is nonnegative, so it is impossible for the actual p-Laplace optimal exponent. The proof is a contradiction between necessary conditions in the source; it neither computes the actual optimal exponent nor substitutes a model PDE or proxy definition for it. It disproves one conjunct, which is enough to refute the conjunction.

The slope is interpreted in the usual sense of the graph y=alpha(p), namely the ordinary derivative d alpha/dp. It is not the derivative of the inverse graph, a logarithmic reparametrization, or a derivative taken only along an unspecified subset. The source does not introduce any such different convention. For the displayed constant-parameter scalar formula in the source we additionally prove actual eventual differentiability and the stronger derivative limit zero, eliminating any singular-function ambiguity for that formula.

## Main proof: genuine real-variable mean value theorem

Suppose f is eventually bounded below by a finite real L and suppose its ordinary derivative tends to minus infinity. There is therefore a real threshold a such that, for every real p>=a,

```
f(p)>=L,     f'(p)<=-1.
```

For an ordinary derivative limit on a real tail these are actual derivatives. In Lean `deriv f p` has the default value zero at a point where f is not differentiable. Thus the bound `deriv f p<=-1` itself implies differentiability at every such p, by `deriv_zero_of_not_differentiableAt`. No tail smoothness assumption or derivative continuity is imported without proof.

Set

```
b = a + (f(a)-L) + 1.
```

Then b>a, since f(a)>=L. The function is continuous on [a,b] and differentiable on (a,b). The actual real Lagrange mean value theorem gives a real c in (a,b) with

```
(f(b)-f(a))/(b-a) = f'(c) <= -1.
```

Because b-a>0, this implies

```
f(b) <= f(a)-(b-a) = L-1,
```

contradicting f(b)>=L. This argument is over the entire real interval; no sequence-difference surrogate is used.

The Lean theorem `not_eventually_deriv_le_neg_one` establishes this contradiction for every eventually lower-bounded f. `no_negative_infinite_slope_of_bddBelow` obtains the tail derivative bound from the actual filter limit `Tendsto (deriv f) atTop atBot`.

`no_nonnegative_regularity_exponent_cusp` specializes to the minimal source requirement `forall p>2, 0<=alpha(p)`. `no_nnreal_regularity_exponent_cusp` expresses the same fact with the nonnegative codomain R>=0. Finally `conjecture_cusp_impossible` is the direct negation of the existence of any graph satisfying these two necessary source conditions. Values below p=2 are irrelevant; any function originally defined only for p>1 can be extended arbitrarily to the remaining real line without changing a derivative on this open tail.

## Optional independent check of the displayed constant-parameter formula

The Lean file also contains the exact scalar expression

```
F_ell(p) = min((p-1)/(2p-2+p*ell), 1/(p-1)).
```

This supplements the general contradiction; the main proof above does not need any assumption about the eigenvalue parameter or this formula.

If F_ell(3)>=0 then ell>-2. Indeed, if ell<=-2, then 4+3ell<0, so the first entry of the minimum is 2/(4+3ell)<0, and the minimum is negative. This is `parameter_gt_neg_two`.

For ell>-2 put c=ell+2>0 and

```
A = max(3, ell+5, 4/c).
```

For p>A the denominator cp-2 is positive, as is p-1. Moreover

```
(p-1)^2-(cp-2) = p*(p-ell-4)+3 > 0.
```

Hence 1/(p-1) is no greater than the other branch, and the minimum is exactly 1/(p-1) throughout the whole open tail. This is `formula_eventually_reciprocal`.

The actual formula is therefore differentiable on a real tail with derivative

```
F_ell'(p) = -1/(p-1)^2 -> 0.
```

`formula_derivative_tends_zero` proves the eventual derivative equality using local equality of real functions and the genuine `HasDerivAt.inv` theorem, then proves the actual filter limit. `proposed_formula_cusp_impossible` contradicts the claimed minus-infinity limit already under the single necessary nonnegativity condition F_ell(3)>=0.

This optional statement treats ell as the displayed constant parameter. If an author intended an unspecified p-dependent eigenvalue, the optional calculation makes no claim about it; the main nonnegative-graph contradiction remains independent of that formula and of all eigenvalue data.

## Author adversarial review (not an external independent review)

- Checked the exact English and Chinese source: both explicitly assign the slope -infinity to the endpoint p->infinity, and neither changes the parameter of the graph.
- A Holder regularity exponent is nonnegative. No unproved quantitative p-Laplace bound, positive lower bound, formula for the optimal exponent, or PDE existence theorem is assumed.
- Proving that no graph at all satisfies these necessary conditions is stronger than proving the failure only for a p-Laplace subclass. It is a logical disproof of the stated conjunction, not an attempt to represent a PDE by arbitrary scalar data.
- The main result allows any finite lower bound L and only a tail lower bound. It therefore does not rely on a global bound alpha<=1 or any behavior near p=1 or p=2.
- The mean value theorem needs differentiability throughout the real interval, not just at a sparse set. That hypothesis is explicitly proved from the eventual strictly negative `deriv` values. Continuity on the closed interval follows from that differentiability.
- The proof uses no assumption that the derivative is continuous and no integration of an unverified derivative.
- A derivative limit taken only over the set of differentiable points would be a different hypothesis; the main theorem is the ordinary real-tail derivative limit. The optional formula calculation supplies a genuine whole differentiable tail for the displayed scalar expression, so singular-function interpretations cannot repair that formula's endpoint assertion.
- Multiplication by b-a uses its strict positivity. The chosen b is proved strictly greater than a from the actual lower bound f(a)>=L.
- The optional formula proof uses division only where its relevant denominators are strictly nonzero: for ell<=-2 the denominator at p=3 is strictly negative, and for ell>-2 both tail denominators are strictly positive. Lean's totalized division at zero is never exploited.
- The second endpoint p->1, strict monotonicity, exact exponent formula, harmonic limit, and any proposed eigenvalue identification need not be decided to refute the source's conjunction.
- No floating-point or auxiliary numerical verifier is needed. The proof uses only exact real calculus and algebra.
- There are no `sorry`, `admit`, `native_decide`, custom axioms, private evaluators, or assumptions of the desired endpoint contradiction. Eight principal theorem axiom audits are printed in the final source.
- This is the proof author's self-review. The parent must still perform its own adversarial review and fresh build before any publication.

## Reproduction and handoff

The project is `round5/drafts/00000007991/lean`, pinned to Lean 4.19.0 and official Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

`round14/other/check_7991.py` runs the actual full `lake build` and strict `lake env lean -DwarningAsError=true Main.lean`. It records complete commands, return codes, timing, timestamps and SHA-256 evidence in `7991-checks.json`; the unmodified output logs are `7991-build.log` and `7991-strict.log`.

This agent did not edit the parent's TeX, generate a PDF, create a PR, or mutate shared publication/snapshot state. No further work on 7991 is required from the author once the recorded final checks pass; parent review and publication remain separate.

## Frozen verification evidence

- Main.lean SHA-256: `927623e4d168dfa478aa9eff90c078c001937bd6002b9a8bc08c94c42966e3f0`
- Exact source SHA-256: `51b4bda4f4d9bcd0a761e41f0aef033ab6f3dcb99e653d465fb416413ca56e37`
- Actual lake build: exit 0, 12.188 seconds.
- Actual strict Lean: exit 0, 11.359 seconds.
- Both checks ran on the same unchanged Main.lean hash.
- Eight printed principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.


Reviewed artifact hashes:

- Main.lean: `927623e4d168dfa478aa9eff90c078c001937bd6002b9a8bc08c94c42966e3f0`
- main.tex: `e404db368389057a320f9e71110ec0cf5b1f0ee35a9d09f9d03492d3afc8a67e`
- main.pdf: `22c6eb560e29ddf289c89c744192f3b69abe5e5fc722f46e1b3e38b246421e52`
- SOURCE.md: `51b4bda4f4d9bcd0a761e41f0aef033ab6f3dcb99e653d465fb416413ca56e37`
