# Disproof of conjecture 00000000145

The written statement does not require α to be irrational. Choose α = 1/2 and f(x) = cos(2πx) on [0,1]. This nonconstant function has mean zero. Every odd prime p satisfies {p/2} = 1/2, so its summand is −1; the prime 2 contributes f(0) = 1. Thus for x ≥ 2 the centered sum is exactly 2 − π(x). Since there are infinitely many primes, the sum is eventually negative and has no positive fluctuations at any positive scale, contradicting the claimed two-sided Ω± statement. If irrational α was intended, that condition is absent from both displayed versions.

The Lean project formalizes the arithmetic core that every prime greater than 2 is odd. The report proves the fractional-part evaluation and explains the integral, infinitude-of-primes, and Ω± steps; those analytic steps are not formalized in Lean.

## Contents

- main.tex and main.pdf: full disproof.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
