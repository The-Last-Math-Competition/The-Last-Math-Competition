# Parent adversarial review: 00000008262

Verdict: PASS

I read both exact source languages, the entire Lean file, all paper sections and the author self-review. Both languages state a universal upper bound depending only on the system/observation noise ratio. The example uses equal, strictly positive isotropic noises, so that ratio is one regardless of whether the noise symbols mean amplitudes or variances. Its anisotropy comes from the allowed dynamics A, not an unmentioned anisotropic noise covariance.

The matrices are actual Mathlib real matrices. I checked the entries of the full algebraic Riccati equation: AP+PA^T=diag(3,-3/4), I-P^2=diag(-3,3/4). Their sum is zero. Positive definiteness uses Matrix.PosDef rather than a list of positive numbers. The closed-loop matrix is -(5/4)I, and its complex spectrum is proved Hurwitz with all eigenvalues having negative real part. The real spectrum of the actual covariance is exactly {2,1/2}; IsLeast/IsGreatest establish the correct extremal eigenvalues and the genuine spectral condition ratio four. Thus the result is not an arithmetical inequality with a hardcoded proxy for condition number.

I checked that the exhibited root is a genuine filtering steady state. The paper gives the standard fully observed Brownian model, the full covariance ODE, and an explicit diagonal solution starting from zero. The scalar equations are p1'=(2-p1)(p1+1/2) and p2'=(1/2-p2)(p2+2). The supplied formulas with exp(-5t/2) solve them, have positive denominators on t>=0, and converge to the claimed covariance. Initializing at that covariance also gives a stationary solution. These stochastic and time-dependent identifications are correctly labeled paper-only; the actual algebraic steady equation and stability conditions are fully proved in Lean.

My separate fresh build and direct strict Lean check returned zero, with only propext, Classical.choice and Quot.sound in the principal theorem dependencies. Native desktop compilation and Tectonic export both actually succeeded. I inspected all three final PDF pages, including matrix displays, explicit time solution and page-three reproduction text: no cropping, missing text or footer collision. The reviewed source, Lean and TeX hashes match the frozen handoff. No interpretation of the other transient or robustness clauses is needed to refute the conjunction. Development self-review and this parent review are distinct; no external independent reviewer is claimed.


Reviewed artifact hashes:

- Main.lean: `ece2d7b5939a6abf851bae3fa191a6b59e7b1444fc530fbef5601a47917ea0d3`
- main.tex: `960556de502dc097106aee71d1c0b0cd64b3fae8e5cf6343d83956cd773d4355`
- main.pdf: `e3ae3a9cbdf9e4317d9e314e42ffc60e848579766673667c4c7842ff9d335977`
- SOURCE.md: `8d68f65e041c22f26a85179d56af0a4e78c751a94486a6965973854931f24074`
