# Author adversarial self-review: conjecture 00000006640
Verdict: PASS

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. No external independent review is claimed.

1. **Source reading.** Both languages ask for an existential separation of
   identical static solution sets and different time spectra using master
   equations. The example supplies valid finite-state continuous-time master
   equations and covers both generator and propagation spectra. The phrase
   time-symmetric is addressed by actual symmetric generators/propagators and
   detailed balance with a common strictly positive stationary vector.
2. **Generator convention.** Columns are probability vectors and p'=Qp.
   The formal generator predicate requires nonnegative off-diagonal entries
   and zero column sums. These are verified, not assumed. Symmetry makes the
   row/column convention immaterial for these matrices.
3. **Genuine statics.** `Static` requires an actual probability vector and
   actual matrix-vector product zero. `static_iff` proves that for every
   nonzero rate this is exactly the singleton uniform vector. `kernel_iff`
   also identifies the entire unnormalized kernel, so no difference can be
   hidden by the normalization restriction.
4. **Genuine dynamics.** The propagator is an explicit matrix-valued function
   of time. The proof verifies P(0)=I, P(s+t)=P(s)P(t), nonnegativity for
   nonnegative times, and column sums one. Actual `HasDerivAt` statements
   establish P'=QP and the vector master equation for every initial vector.
   `flow_probability` and `flow_initial` provide the probability and initial
   conditions. This is not a comparison of abstract assigned numerical labels.
5. **Real spectra.** Both exact spectral formulas use Mathlib `spectrum ℝ` of
   the actual matrix. Membership is reduced through noninvertibility and
   the determinant. The generator determinant is mu*(mu+2r); the propagation
   determinant is (mu-1)*(mu-exp(-2rt)). No preassigned eigenvalue table is used.
6. **Strict difference at positive time.** The generator spectra differ by
   the element -2. For each t>0, exp(-2t) belongs to the first propagation
   spectrum and equals neither 1 nor exp(-4t), using exponential injectivity.
   At t=0 the propagator spectra agree, so the theorem explicitly excludes it.
7. **Time symmetry and nondegeneracy.** Both generators are Hermitian and
   obey detailed balance with uniform probability. The transition matrices
   are also Hermitian. The selected rates 1 and 2 are positive, so both states
   communicate and the common stationary vector is strictly positive.
8. **Rescaling.** The two equations differ by an overall factor in their
   rates. This is a valid example of the requested existence statement,
   which includes no identification under time reparameterization. The paper
   states the fixed-time convention openly. It does not claim a stronger
   inequivalence under arbitrary changes of time units.
9. **Full claim.** The final theorem proves an existential proposition over
   actual matrices, matrix-valued semigroups, and a probability vector. It
   includes validity of both master systems, reversibility, equality of both
   kinds of statics, and inequalities of the actual spectra. It strengthens
   the source by asserting propagator difference at every t>0.
10. **Scope honesty.** A general stochastic-process path construction, general
    matrix-exponential identity, and general ODE uniqueness theorem are not
    needed or claimed. The explicit semigroups satisfy the displayed master
    equation directly. Every mathematical property required by the theorem
    is formalized. The paper's eigenvector explanation supplements the formal
    determinant proof and is not a hidden dependency.
11. **Axioms and evidence.** Strict Lean 4.19.0 compilation passes with warnings
    as errors. The main theorem and flow/spectrum bridge audits contain only
    propext, Classical.choice, and Quot.sound. No custom axioms or placeholders
    occur. Parent fresh build and PDF inspection are separate follow-up checks.
12. **Provenance and prior submissions.** The exact bilingual source hash
    matches the current parent source record. Parent snapshot reports no
    prior PR or solution path. This is an author self-review, not an external
    independent review.


Reviewed artifact hashes:

- Main.lean: `aa408eca5afae0053ef184bca83a268f22565de36f99cd6be81536ca367ea853`
- main.tex: `537f436c10129783eac19c95cd0dff661084ef83c82f33b80182365a41b89763`
- main.pdf: `2934956d48c25d300f360c846cc5d08f1c2058ac695d9c8e81cae7bbe4c87f40`
- SOURCE.md: `e621af45a6d89f6bdf3b2a6d10a744aa35cd110fe060c378e11f34123a73369c`
