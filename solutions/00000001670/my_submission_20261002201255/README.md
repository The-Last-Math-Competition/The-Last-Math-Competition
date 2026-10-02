# Disproof of conjecture `00000001670`

**Verdict: FALSE — the conjecture's two descriptions of P₃ contradict each
other.**

## The conjecture (verbatim from `conjectures/00000001670.md`)

> Definition: M_d is the max-cut ratio of the random d-regular graph.
> Conjecture: M_d = 1/2 + P_d/√d + O(1/d), where P_d is a Dembo–Montanari–Sen
> type constant with the analytic characterization **P₃ = 0.918**: the closed
> form **P₃ = (2/π)·arctan(√2)**; the concentration width is n^(−1/2).

**Object consistency.** We attack exactly the two asserted descriptions of
P₃: the numeric value 0.918 and the displayed closed form (2/π)·arctan(√2).

## The refutation (self-inconsistency, certified by integer arithmetic)

The closed form the conjecture itself displays satisfies

    (2/π)·arctan(√2) < (2/π)·arctan(√3)     (arctan strictly increasing; √2 < √3 ⟺ 2 < 3)
                   = (2/π)·(π/3)             (arctan(√3) = π/3, standard)
                   = 2/3
                   < 459/500 = 0.918          (2·500 = 1000 < 1377 = 3·459).

So **(2/π)·arctan(√2) < 2/3 < 0.918**: the closed form evaluates strictly
below the 0.918 the conjecture simultaneously asserts. The two clauses
cannot both hold — the conjecture is self-inconsistent.

(For the record, the actual evaluation is (2/π)·arctan(√2) ≈ 0.608, and the
true Dembo–Montanari–Sen constant for d = 3 is P* ≈ 0.763, disagreeing
with both stated numbers; this is extra information, not needed for the
refutation.)

Cited standard facts: arctan strictly increasing on [0,∞), arctan(√3) =
π/3, π > 0. Everything else is kernel-certified integer arithmetic
(`two_lt_three`, `two_thirds_lt_0918`, `values`).

## Reproduce

`python3 reproduce.py` — evaluates (2/π)·arctan(√2) numerically (≈ 0.608),
checks the chain 0.608 < 2/3 < 0.918, and the integer cross-multiplication
1000 < 1377. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 3 theorems,
all `does not depend on any axioms`.

## Boundary

Only the P₃ characterization clauses are refuted. The M_d asymptotic shape
and the n^(−1/2) concentration clause are not addressed.
