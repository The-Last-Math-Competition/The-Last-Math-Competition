# Parent adversarial review: 00000001251

Verdict: PASS

Review type: internal parent review of agent-authored work; no external independent review is claimed.

Main.lean SHA-256: `b840c67d66d99a4ff6489febfdc556315391535e9041a187045acd3d874677e5`

main.tex SHA-256: `d3aa9914b7d062b6ae8754d37c496fb8a1410fc1687c7ff030d8699c30f94718`

main.pdf SHA-256: `c82537f1d6b60737841e35dfaa7998ca5c8681ec55967d349344a2410912e8d9`

SOURCE.md SHA-256: `cf780e6dd2045e341b12579327a45dee5f0fa239dd4d3b74c5cf9116a6bef5b4`

Recorded at UTC: 2026-10-10T00:12:38.425740+00:00

The parent read the exact bilingual source, complete Lean proof, final paper, README, author review and publication scope. The parent inspected the actual fresh-build and direct warnings-as-errors axiom logs and checked that the current source/PDF hashes match the recorded builds.

1. The source defines capacity k without imposing an extremal law or a fixed particle-number sector. A grand-canonical law is therefore admissible. All 27 occupation states have positive probability, so the example is not an empty or frozen configuration.
2. Moves really decrease one occupied source coordinate and increase one unfilled destination coordinate, preserving the third site. The three-site cycle makes every pair of distinct sites adjacent. Both eta_i(2-eta_j) rates and unit-rate legal jumps are explicitly checked, removing the main rate-convention ambiguity.
3. The actual normalized Mathlib PMFs, product formula, binomial marginals, detailed balance, generator conditions and pi Q=0 equations were read in Lean. The three-point deficit is actually zero. Finite-chain stationarity via the exponential power series is explained in the paper; no separate continuous-time sample-path construction is claimed.

Both final rendered PDF pages were visually inspected by the parent. The formulas and proof text are complete and readable, without clipping or overflow. The Tectonic log has no warnings, and the current LaTeX hash also has a successful desktop compiler record.

Only standard Lean logical axioms occur. The fresh project build and direct proof check succeeded; official pinned dependency caches were reused, but no compiled artifact from this submission was reused in the fresh build.
