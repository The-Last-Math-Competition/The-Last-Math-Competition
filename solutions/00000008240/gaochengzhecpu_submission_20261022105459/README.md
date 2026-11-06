# Conjecture 00000008240 — Disproof

The first conjunct equates the cooperation discount threshold with the raw one-period defection payoff divided by the cooperation payoff. In the repeated prisoner's dilemma with T=3, R=2, P=1, S=0, grim trigger is a cooperative subgame-perfect equilibrium at discount 1/2, so the critical discount over all cooperative pure history-dependent SPE is at most 1/2. The proposed raw ratio is 3/2.

The counterexample is classical, not a new folk theorem. The paper cites Jonathan Levin's *Repeated Games I: Perfect Monitoring*, Proposition 1, and a Northwestern course handout giving the exact stage-payoff table. The argument is independent of those references and is reproduced completely.

## Formal content

`lean/Main.lean` defines the real stage game, finite joint-action histories, arbitrary two-player pure history-dependent profiles, recursive deviation trajectories, convergent infinite discounted payoffs, compliance, cooperation and subgame perfection. A Bellman inequality with continuation values 4 and 2 bounds every infinite unilateral deviation at every history. `grim_is_spe` and `grim_cooperates` exhibit the actual equilibrium. `critical` is the infimum of discounts permitting **any** cooperative pure SPE, not just grim-trigger profiles. `critical_le_half` proves the bound, and `conjecture8240_false : ¬ ClaimedRatio` negates the first equality specialized to this game.

The paper additionally explains mixed deviations via pathwise bounds, and additive-shift invariance. Those observations are not separately formalized. No exact critical discount is asserted. No noise correction or spectrum assertion is separately resolved. The reading is the source's literal raw-payoff ratio; a formula using normalized payoff differences is a different assertion.

## Reproduction

Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. In `lean/`, run `lake build` or `lake env lean -DwarningAsError=true Main.lean`. The printed audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

`SOURCE.md` is the unchanged bilingual source at upstream b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. The coordinator's refreshed intake found no prior PRs or solution paths for this ID.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. Review mode: agent development with parent adversarial review; no external independent review.
