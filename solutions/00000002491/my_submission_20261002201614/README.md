# Disproof of conjecture `00000002491`

**Verdict: FALSE — the Möbius value at a partition with repeated block
sizes is 1, not 0.**

## The conjecture (verbatim from `conjectures/00000002491.md`)

> Definition: Möbius inversion of partitions: poset inversion. Conjecture:
> The Möbius function of the partition lattice is governed by squarefree
> partitions: the inversion formula closes on partitions without repeated
> parts, and the Möbius values vanish otherwise.

**Object consistency.** We attack exactly: "the Möbius values vanish [on
partitions with repeated block sizes]", i.e. μ(0̂,σ) = 0 whenever σ has two
blocks of the same size.

## The refutation (n = 4, exact)

σ = **{{1,2},{3,4}}** has a repeated block size (2, 2). The interval
[0̂, σ] consists of exactly four partitions:

    {1|2|3|4}  <  {12|3|4}, {1|2|34}  <  {12|34}

(a Boolean lattice B₂ in disguise). The Möbius recursion
μ(x,x) = 1, μ(x,y) = −Σ_{x≤z<y} μ(x,z) gives

    μ(0̂, {12|3|4}) = −1,  μ(0̂, {1|2|34}) = −1,
    μ(0̂, σ) = −(1 + (−1) + (−1)) = **1 ≠ 0**.

So the Möbius value at a partition with repeated parts is **1, not zero**
— the vanishing clause is false. (Cross-check: the classical product
formula μ(0̂,σ) = ∏_B (−1)^{|B|−1}(|B|−1)! gives (−1)(1)·(−1)(1) = 1.)

Lean: the 4-element interval is hardcoded as an explicit order matrix, and
the recursion (with fuel 4) is kernel-evaluated: `mu_sigma` = 1,
`not_zero`. All 4 theorems `does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — computes Möbius values on the full partition
lattice Π₄ (15 elements) by recursion, verifies μ(0̂, {12|34}) = 1, lists
all repeated-size partitions and their nonzero Möbius values. Exit 0.

## Boundary

Only the vanishing clause is refuted. The "inversion formula closes on
squarefree partitions" clause is not addressed.
