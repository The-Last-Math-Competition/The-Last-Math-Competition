# Self-review: conjecture 00000005512

Verdict: PASS (development self-review; parent review and fresh build pending).

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. Both source languages were read. Main interpretation risk is that "power law in selection count" could mean a d-th-power recursion rather than a genuine polynomial tail. The paper foregrounds the distinction, acknowledges the correct recursion, and treats both queue-length and selection-count asymptotic variables.
2. The model is the actual classical supermarket mean-field ODE, with arrival load rho and unit exponential service. Its arrival term is rho(q_k^d-q_{k+1}^d), service term q_{k+1}-q_{k+2}. The model is derived on paper and linked to the primary Budhiraja–Mukherjee–Wu article. No finite-server limit theorem is presented as formalized.
3. Lean drift and driftD contain these exact terms at every natural coordinate. Fixed-point predicates retain q0=1, nonnegativity, monotonicity, limit zero, and all drift equations. The d-choice family includes actual normalized probability and survival-tail sums.
4. The two-choice sequence is defined recursively, and its closed form is proved for all k, not a finite sample. Its uniqueness in the admissible tail class follows formally by the constant-flux argument and the limit-zero boundary condition.
5. Probability is substantive: masses are adjacent tail differences, formally nonnegative. HasSum proves total mass one; tail_is_survival and tailD_is_survival prove the entire survival-tail identity at every queue length. The example is not an arbitrary scalar recurrence without a probability law.
6. The infinite asymptotics are actual filter limits. For every m, k^m q_k tends to zero by comparison with k^m 2^-k. no_polynomial_tail retains arbitrary positive c and an arbitrary eventual cutoff. Thus it excludes the lower bound required by every genuine finite power law; the elementary comparison with a larger integer exponent is explained accurately on paper.
7. The selection-count treatment uses genuine d-choice fixed points for every d>=1. It proves q_d(2)=2^(-d-1) and actual d^m q_d(2) limit zero, not just a symbolic claim that double-exponential queue tails differ from polynomial queue tails.
8. The paper does not falsely claim that the corrected d-th-power recursion is wrong. It expressly leaves that interpretation unrefuted, so organizer intent remains the key review consideration.
9. The final Lean warning-as-error run passes with only propext, Classical.choice, Quot.sound. No added axiom, placeholder, native_decide, finite oracle or table is used.
10. The parent checked current source and complete PR history and locked 5512. No existing draft or blocked ID was overwritten. ID 5556 is separately locked for the next deliverable; 5712 was rejected for high formalization cost. No GitHub or shared pipeline changes were performed.


Reviewed artifact hashes:

- Main.lean: `60cc2d28f49bff3bbb21c0c8ede7e7f78efc4816f70e5256843ea60cc3b6b252`
- main.tex: `95e4ceca875b8e7a069088da48b2974d3ee6783a18062e2f19bae500f220cafa`
- main.pdf: `911906e225346430381f5eaa888eed109460b27639a3c67532ebbe5c8c119d6d`
- SOURCE.md: `4e70f876f349dc4bf7e377687f8d1f2295d13acbc6c440626c87a726ec54570f`
