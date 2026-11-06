# Parent adversarial review: 00000005501

Verdict: PASS

I read the exact bilingual conjecture, the complete frozen Main.lean, the author derivation, explicit scope and self-review, the actual build records, and the final four-page paper. I inspected all four final rendered pages individually. This is an internal parent adversarial review of agent-developed work, not an external independent review.

The source defines an open network as a Markovian network with exponential service and imposes no minimum station count. A single M/M/1 queue with external arrival rate rho, service rate one, and departures from the network is therefore a valid instance. The usual utilization is exactly rho, so the stable deficit is 1-rho without a parameter-normalization ambiguity. A false queue-length exponent suffices to refute the conjunction without assigning meaning to its unspecified bottleneck redistribution coefficient.

I checked that the geometric variable is connected to an actual queue model. The Bool clock PMF has genuine normalized nonnegative arrival and potential-service masses. Mapping its outcomes gives a PMF on n+1 and Nat(n-1), including the correct idle clock at zero. The real transition matrix is proved to equal these actual PMF masses. Every entry of Q=(1+rho)(T-I) is checked: arrivals rho, nonempty departures one, empty diagonal -rho, busy diagonal -(1+rho), and every remaining entry zero. Repeated transitions are real PMF binds and their mixture is the actual Poisson PMF at rate (1+rho)t. This is a standard Poisson-uniformization construction of the M/M/1 queue, not merely a chosen stationary sequence named as a queue. The paper correctly discloses that a separate holding-time path construction and a semigroup derivative at zero are not formalized.

The normalized geometric PMF has actual masses (1-rho)rho^n. Detailed balance is proved for every state pair, then summed using PMF normalization to prove one-step invariance. Induction and Poisson mixing establish all-time stationarity. Thus the counterexample concerns a legitimate stationary regime. The mean is the actual nonnegative Lebesgue integral against this measure, evaluated through a convergent weighted geometric series. Its real conversion occurs only after finite-value equality is proved, excluding the infinity-toReal=0 loophole. The exact identity (1-rho)E[N]=rho and mean rho/(1-rho) are correct.

A divergent mean alone would not settle a typical-scale claim. The proof therefore also gives actual finite-cutoff probabilities, using the genuine measure of the finite initial state segment and its exact sum. Every atom is at most delta. Along rho_k=1-(k+2)^(-2), all loads are strictly stable and tend to one; the exact square-root deficit is 1/(k+2). For every fixed integer M, the true probability of N<=M(k+2) is at most (M+1)/(k+2), hence tends to zero. Taking a larger integer covers any fixed finite real cutoff. Therefore the proposed normalized distribution escapes to infinity in probability and is not tight, an obstruction to a finite half-power stationary scale independent of rare mean tails. A sequence of stable loads suffices to contradict a universal near-boundary statement.

The second conventional queue-length definition is also handled: waiting is the actual PMF pushforward by n->Nat(n-1), and the event identity W<=K iff N<=K+1 is proved before transferring the bound. Thus excluding the in-service customer cannot repair the conjecture. The paper accurately restricts its conclusions to stationary lengths and does not confuse them with centered fluctuations, transient diffusions or a claimed full heavy-traffic limiting distribution.

The fresh parent build excludes this submission's build cache, checks pinned dependency sources, and actually passes both full lake build and warningAsError checking. All eighteen printed axiom checks use only standard foundational axioms. No auxiliary computation oracle is used. The current final paper compiles successfully with both Tectonic and the native editor compiler, has zero TeX warnings, and every page was reviewed for equations, completeness, margins and readability. A crowded reference/footer area was shortened and the final four pages re-inspected. Frozen semantics, source, paper and actual verification evidence agree. Separate immutable-package, source-freshness and duplicate checks remain required before publishing.


Reviewed artifact hashes:

- Main.lean: `31fcdc1eb502f1129d18eca082d9961f47202e00e267acdad226717daf2041ad`
- main.tex: `795a316e2f2300da9f2e261fd40c31a4f6b3e8fe31b13e74454fc4d019ee7d4d`
- main.pdf: `e547441d3de30cee75ba240449d83e8daef3753cb547cb136a0904c62fe85caa`
- SOURCE.md: `53a7af6f2881735a3b5ff0bea6ab11b493ad70b67e414d4d975d65e00387eded`
