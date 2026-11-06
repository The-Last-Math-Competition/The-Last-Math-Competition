# Parent adversarial review: 00000002362

Verdict: PASS

I read the exact bilingual source, the entire frozen 381-line Lean proof, the author derivation with all twelve adversarial points and actual check records, and the complete final paper. I inspected all four final rendered pages. I also opened the author-hosted Batty-Haase-Mubeen primary paper supporting the standard sectorial definition and calculus norm terminology. This is a separate internal parent review of agent development, not an external independent review.

The source claims a calculus bound as a function of the sector angle. The submitted scope is precisely that angle-only finite uniformity assertion. The construction fixes the Hilbert space, genuine operator norm, positive admissible class angle pi/3 and larger calculus-domain angle pi/2, and refutes every finite uniform constant. It does not refute estimates involving operator-specific resolvent bounds. All constructed operators actually have stronger angle-zero sectoriality; the paper correctly does not claim pi/3 is their least angle. Thus neither changing dimension nor choosing different operator angles supplies the discrepancy.

I checked the actual matrix and operator semantics. Matrix.L2OpNorm is active. E has Euclidean operator norm exactly one through the C-star identity and its rank-one projection. The resolvent is the genuine Mathlib resolvent, not a proxy inverse: z-A is proved a unit for every z!=1 by an explicit left inverse. The actual spectrum is consequently contained in {1}. The all-larger-sector predicate uses spectral containment and resolvent norms for every larger theta<pi. The geometry is valid: for c=cos(theta)>=0, (r-c)^2+1-c^2 >= (1-c)^2, while for c<0 the real part is nonpositive. This yields a strictly positive distance eta and the finite bound (1+1/eta)(1+N/eta) for each N. The bound is uniform over z, as required, but not over N, which is allowed in sectoriality.

The test g(z)=z/(1+z)^3 is holomorphic on the whole actual right half-plane and its only pole is outside that domain. The norm estimates establish both scalar sup<=1 and standard H0-infinity decay, eliminating regularization or nondecaying-test loopholes. The actual unit I+A has the stated inverse, so no totalized singular inverse is used. Nilpotency gives g(A)=I/8-NE/16; its growing norm follows from the triangle inequality and norm E=1. The chosen N=16(max(C,0)+1) beats every real C with a strict margin.

The norm-preserving star algebra equivalence to continuous linear maps on genuine Euclidean C^2 explicitly transports units, inverse, spectrum, resolvent, sectoriality and the rational value. The final theorem therefore concerns true bounded operators, not entrywise matrix norms or an invented calculus. I read these bridge proofs rather than accepting only the report's description.

The Lean theorem refutes a necessary ordinary rational-test consequence of a bounded H-infinity estimate. The paper makes this scope explicit and supplies the standard rational consistency bridge in mathematical prose; it does not purport to construct the whole contour calculus in Lean. I independently checked the additional full-calculus justification: substituting the actual resolvent in the contour formula gives f(A)=f(1)I+N f'(1)E, and the radius-1/2 circle in the right half-plane gives norm f(A)<=(1+2N)norm f. Thus each individual example does have a finite bounded calculus, so the argument is not a failure to belong to the intended class. These elementary contour/Cauchy facts are clearly distinguished from the formal rational-subclass proof.

The fresh build excludes submission artifacts and checks clean pinned official dependency sources. Actual full lake build and strict warningAsError compilation pass, with only standard foundational axiom dependencies. No numerical verifier or computation oracle is required. Both Tectonic and the native editor compiler successfully compiled the current exact TeX. The four final pages have readable equations, complete text, adequate margins and no overlap or clipping, with zero TeX warnings. All semantic and artifact checks support the stated disproof, subject to the separate source-freshness, duplicate and immutable-package gates before publication.


Reviewed artifact hashes:

- Main.lean: `fce8c54edd9bb93ca9f1f27eb6f47b790ad771838b09b766b36068abaca92b1d`
- main.tex: `a2c2ec70c35dbdebee456b703bdd49fd82c9f92dca154df91e5adc992a20487b`
- main.pdf: `179a6f31a58b4d0d604d9685b838bb4e7397338600c5bd757e55c313087d07ae`
- SOURCE.md: `8553ea0727bb80969fb77cd741be8834ec6d58d03efd0ba70d20b49b6f24f5a0`
