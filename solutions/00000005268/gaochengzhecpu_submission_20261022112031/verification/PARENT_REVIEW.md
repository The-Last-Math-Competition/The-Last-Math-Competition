# Parent adversarial review: conjecture 00000005268

Verdict: PASS

I read the unmodified bilingual source, the complete final Lean development, the complete paper and both rendered PDF pages. This is the coordinating agent's adversarial review of another agent's development, not a claim of external independent review.

Both source languages explicitly extend the asserted impossibility of finite-time three-vortex collisions to general circulation triples. The counterexample uses nonzero mixed-sign circulations, which are permitted by that claim. The submission does not conflate this with the different same-sign collision-exclusion statement. Refuting the universal impossibility directly is sufficient regardless of the additional relative integral suggested by the source.

The formal vector field is a genuine finite sum on three complex positions with the physical factor 1/(2 pi), the circulation of the other vortex in each summand, and the squared modulus in the denominator. The paper's normalized circulations are converted to physical circulations by multiplying by 2 pi; this scaling and nonvanishing of all strengths are proved in Lean. Thus the construction is not a change to a different differential equation.

I independently checked the rational configuration before authoring was authorized using exact rational arithmetic for real and imaginary parts. For the unscaled strengths (-1,-3/5,3/8), all three velocity-to-centered-position ratios are exactly -84/1073 - (6664/5365)i. The author's circulation rescaling gives precisely -1-(238/15)i. I also checked the paper's pairwise squared distances and its listed velocity products. These separate calculations support the model interpretation; the formal proof checks the actual rational identities again.

For t<1/2 the real logarithm has positive argument. The exponential scaling factor has squared norm 1-2t and derivative lambda times itself divided by 1-2t. The field's translation and similarity covariance then prove HasDerivAt for each actual trajectory coordinate at every pre-collision time. Injectivity follows from distinct shape points and the nonzero complex exponential. The norm tends to zero from the left, so all three coordinate limits equal the same finite center. The universal proposition being negated explicitly includes nonzero strengths, positive finite time, noncollision on [0,T), and the true ODE on that interval. None of those requirements is merely assumed for the witness.

A collision is defined by the common pre-collision limit. The ODE is singular at the collision, and no value of a globally extended exp/log expression at T is used to prove that limit. This avoids the endpoint-substitution error. The paper states the solution only on its valid time interval and does not claim continuation through the singularity or a classification of all collisions.

The fresh copied-project lake build and separate warnings-as-errors Lean check both returned zero, using clean commit-pinned Mathlib sources and official dependency artifacts. The audited results depend only on propext, Classical.choice and Quot.sound. The desktop LaTeX compiler also succeeded. Tectonic exported two pages with no warnings; I inspected every final page, including the exact velocity table, the derivative equations, the one-sided limit argument and reproduction command. The text and equations are legible and unclipped.


Reviewed artifact hashes:

- Main.lean: `9eaecefbb6e952354945aac5ebf59c9285b0f912f9ec9479328d08c0ad4849a9`
- main.tex: `731917b55d119fb0ee5fef12dff8f9d8a9a9af3095011093820fc899c2afe8e3`
- main.pdf: `86a9aa0d26e71bd2f2f2daf5140d9d2a30640f81becd6fb1aea13fe3f09406fc`
- SOURCE.md: `2cc17ccfc9aff87f83fdaf7591d36c2d3c1335b732befe8d5e2b653d9255d6fa`
