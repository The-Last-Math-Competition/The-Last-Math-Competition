# Adversarial self-review: 8262
Verdict: PASS (mathematics and direct Lean; parent fresh build/PDF pending).

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately.

1. Source: both languages unambiguously assert the condition number is at most the squared observation/system noise ratio. We disprove this first conjunct only.
2. Nondegeneracy: dimension two, H=I, both noise amplitudes one. The proposed upper bound is one, so the contradiction is not the technical issue that a claimed bound is less than the universal minimum one.
3. Filtering conventions: Q=I and R=I under either noise-amplitude or noise-variance notation; the covariance equation is AP+PA^T+Q-PH^TR^-1HP. No convention can reverse the result when both noises equal one.
4. Matrix arithmetic: AP+PA^T=diag(3,-3/4), P^2=diag(4,1/4). Their difference plus identity vanishes exactly. P has positive diagonal 2,1/2. Closed-loop A-P=-(5/4)I.
5. Actual steady state: the solution is positive definite and stabilizing. Paper additionally provides explicit zero-initial covariance trajectory with exponential e=exp(-5t/2), converging to P. Scalar roots are (2,-1/2) and (1/2,-2), and the displayed formulas are their standard separated-variable solutions. No arbitrary Riccati root is substituted.
6. Spectral condition number: formal definition uses IsLeast and IsGreatest of the genuine real matrix spectrum, not a named numerical constant. Mathlib spectrum_diagonal proves the spectrum; positivity and ratio yield exactly four. For SPD matrices this is the standard spectral 2-norm condition number.
7. Stability: formal Hurwitz property uses the complete complex spectrum of the complexified closed-loop matrix. It is not a check of a selected list of real eigenvalues.
8. Universal claim: ClaimedBound quantifies over dimensions, actual matrices, positive noises, SPD covariance, actual ARE, Hurwitz closed loop and its spectral condition number. Its negation is proved by this concrete member. No sorry, admit, native_decide or extra axiom appears.
9. Formal scope: Brownian filtering interpretation and time-dependent ODE trajectory are paper-only, explicitly stated. All steady objects needed for the algebraic contradiction are formalized.
10. Checks and prior work: direct Lean warningAsError check passed; printed axioms are only propext, Classical.choice, Quot.sound. Parent froze the source and checked full PR history with no prior submission. No GitHub operations performed by this agent.


Reviewed artifact hashes:

- Main.lean: `ece2d7b5939a6abf851bae3fa191a6b59e7b1444fc530fbef5601a47917ea0d3`
- main.tex: `960556de502dc097106aee71d1c0b0cd64b3fae8e5cf6343d83956cd773d4355`
- main.pdf: `e3ae3a9cbdf9e4317d9e314e42ffc60e848579766673667c4c7842ff9d335977`
- SOURCE.md: `8d68f65e041c22f26a85179d56af0a4e78c751a94486a6965973854931f24074`
