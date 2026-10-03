# Disproof of conjecture `00000004163`

**Verdict: FALSE — both claims. Prime cubes mod 9 lie in exactly
{0, 1, 8} (3³ = 27 ≡ 0; for p not divisible by 3, p³ ≡ ±1: 2³ = 8,
4³ = 64 ≡ 1), and sums of SEVEN such residues cover ALL NINE
residue classes mod 9 (k·1 + m·8 with k + m ≤ 7 reaches every
class: 0..7 as k copies of 1, and 8 as one 8 plus six 0s): there
are ZERO local obstruction classes, not three.  The genuine
obstruction belongs to THREE variables, which miss exactly TWO
classes {4, 5} — and FOUR variables already suffice to remove all
obstructions, so "adding one variable removes all obstructions"
mislocates the phenomenon by four variables.**

## The conjecture (verbatim from `conjectures/00000004163.md`)

> Definition: The local obstruction of Waring-Goldbach is a
> congruence class with no representation modulo q. Conjecture: For
> sums of seven cubic powers of primes the local obstruction
> classes are exactly the three non-representable classes modulo 9,
> and adding one variable removes all obstructions. (exact table of
> WG cubic local obstructions)

## The refutation

The residue arithmetic is completely determined by the cube map on
Z/9: the cubes of primes are {0 (p = 3), ±1 (p ≢ 0 mod 3)}, since
the unit group (Z/9)* is cyclic of order 6 and cubing maps it into
{±1}.  A seven-term sum is k·1 + m·8 with k + m ≤ 7 (k terms ≡ 1,
m terms ≡ −1, the rest ≡ 0); the reachable classes are k − m for
0 ≤ k − m ≤ 7 plus 8 = −1 — i.e. **every** class mod 9.  The
claimed "three non-representable classes" do not exist at seven
variables.

The true obstruction table (exhaustive):

| s variables | missing classes mod 9 |
|---|---|
| 3 | {4, 5} — exactly two |
| 4 | ∅ — no obstruction |

So the obstruction-dying point is at four variables, not eight:
"adding one variable removes all obstructions" is off by four, and
the claimed count "three classes" is off by the entire table.

## Verification

* `reproduce.py` — the cube-residue set {0, 1, 8}; exhaustive
  7-term coverage of all 9 classes; the missing-class table for
  s = 3..7 ({4,5} at s = 3; ∅ from s = 4).
* Lean 4 (core, v4.33.1), `lean4/` — `cube_residues` (8, 0, 1 mod
  9), `seven_cover` (explicit witnesses for all 9 classes via
  cases on the residue), `no_obstruction`, `three_missing`,
  `conjecture_refuted`.  All 5 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the cube residues, the nine explicit
(k, m)-witnesses covering every class with k + m ≤ 7, and the
three-term missing set; the exhaustive cover table is in the
script.  Both the obstruction table and the variable-count claim
are refuted at modulus 9.
