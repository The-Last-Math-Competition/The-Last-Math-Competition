# Disproof of conjecture `00000002212`

**Verdict: FALSE — c(⟨5,6,7⟩) = 4 and c(⟨5,6,25⟩) = 5 share
min(a,b,c) = 5; c(⟨6,7,8⟩) = 4 and c(⟨6,7,35⟩) = 7 share min = 6.
The catenary degree of a 3-generated numerical semigroup is not a
function of min(a,b,c), so the conjectured "explicit function" does
not exist.**

## The conjecture (verbatim from `conjectures/00000002212.md`)

> Definition: The catenary degree c(H) is the diameter of the
> factorization graph. Conjecture: The catenary degree of the
> three-generated numerical semigroup ⟨a, b, c⟩ is an explicit function
> of min(a, b, c) (three-generated catenary).

## The refutation

The catenary degree c(H) = sup{c(n)} where c(n) is the minimal
threshold t such that any two factorizations of n are joined by a
chain of factorizations of n with consecutive sup-norm distances ≤ t.
Direct computation (exhaustive incremental factorization-set dynamic
programming, verified stable over the window [abc/2, abc+gens] and
grounded in the classical fact that c(H) is attained on Betti
elements, which for 3-generated semigroups lie below lcm(a,b,c)):

| semigroup | min | c(H) | witness |
|---|---|---|---|
| ⟨5,6,7⟩ | 5 | **4** | Z(30) = {(6,0,0),(2,1,2),(1,3,1),(0,5,0)}: (6,0,0) isolated at t=3, chained at 4 |
| ⟨5,6,25⟩ | 5 | **5** | Z(25) = {(5,0,0),(0,0,1)}: two-point set at sup-distance 5 |
| ⟨6,7,8⟩ | 6 | **4** | Z(24) = {(4,0,0),(0,0,3)}: two-point set at distance 4 |
| ⟨6,7,35⟩ | 6 | **7** | Z(42) ∋ (7,0,0),(0,6,0) at distance 7, isolated at 6 |

Equal minima, unequal catenary degrees — twice. c is not a function of
min(a,b,c).

## Verification

* `reproduce.py` — independent recomputation of all four catenary
  degrees (exhaustive DP to n = abc + gens, with stability windows),
  the five kernel witness factorization sets, and the witness distance
  tables.
* Lean 4 (core, v4.33.1), `lean4/` (2050 lines, generated and
  self-checked by the same exhaustive enumeration) — kernel-certified:
  the complete factorization sets Z(30), Z(35), Z(42) of ⟨5,6,7⟩
  (generic: Betti elements are exactly {30,35,42}, so c = max of the
  three c(n)'s) and Z(25), Z(30) of ⟨5,6,25⟩ (Betti elements
  {25,30}); each enumeration closes every (z1,z2) leaf with an exact
  divisibility two-sided bound; plus the equal-minima/4<5 comparison
  and the witness distance tables. All 10 audited theorems report
  `does not depend on any axioms`. (Core's Nat.mul_assoc/Nat.add_mul
  and the `omega` tactic carry axioms, so the package rebuilds the
  needed associativity/cancellation facts by induction and uses
  explicit lemma chains.)

## Boundary

The kernel certifies the complete finite factorization sets and
distance tables. The transport from these to the catenary-degree
values rests on the classical identification "c(H) = max of c(n) over
Betti elements" (Chapman–García-Sánchez–Llena) and the generic-semigroup
Betti characterization {gᵢ·gⱼ} for pairwise-coprime generators, cited
in prose; the ≤-direction (no larger c(n) anywhere) is carried by the
exhaustive script with its stability window. The second pair
⟨6,7,8⟩/⟨6,7,35⟩ is script-verified only. The refutation of the stated
"explicit function of min(a,b,c)" claim is complete through the first
pair.
