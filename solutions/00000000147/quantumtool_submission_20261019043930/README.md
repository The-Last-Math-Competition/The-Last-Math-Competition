# Disproof of conjecture 00000000147

## The statement is undefined as written
The conjecture writes P(g_n > t log p_n) but does not specify a probability space, random variable, or sampling rule. Prime gaps g_n and primes p_n are deterministic. Thus the probability in the displayed expression is not defined by the data of the conjecture.

Even if one assigns the deterministic event its natural point-mass probability for each n, its value is either 0 or 1. For every fixed t > 0, e^(−t) is strictly between 0 and 1. A sequence of values confined to {0,1} cannot converge to this interior value: each term stays at least min(e^(−t), 1−e^(−t)) away from it. A meaningful tail conjecture would need to specify a random model or an empirical distribution over a growing range of indices; these choices define different statements.

## Formalization scope
The Lean file checks the arithmetic core of the point-mass interpretation: a deterministic event probability, encoded as 0 or 1, cannot lie in the central interval around 1/2. The absent probability space and this interpretation choice are explained in the report, not represented as a Lean measure-theory theorem.

## Contents
- main.tex and main.pdf: written disproof and interpretation notes.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
