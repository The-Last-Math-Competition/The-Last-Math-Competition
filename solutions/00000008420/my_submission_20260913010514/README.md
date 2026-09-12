# Disproof of TLMC conjecture 00000008420 — verdict: FALSE

**Conjecture** (`conjectures/00000008420.md`). A Kirkman triple system (KTS) is a
resolvable Steiner triple system. The conjecture states: (i) KTS(n) exists iff
n ≡ 3 mod 6 (known); (ii) the number of parallel classes is exactly (n−1)/2;
(iii) the smallest order of a KTS with a transitive automorphism is the
point-transitive type of order 15; and (iv) no KTS has automorphism group a
cyclic group of prime order.

**Verdict: FALSE.** Clause (iii) is refuted by an explicit counterexample: the
line system of the affine plane AG(2,3) is a KTS of order 9 whose translation
group F₃² acts transitively on the 9 points, and 9 < 15.

**Scope of the disproof.** Only clause (iii) is attacked. Clauses (i) and (ii)
are consistent with the counterexample — indeed n = 9 ≡ 3 (mod 6) and the
system has exactly 4 = (9−1)/2 parallel classes — and we make no claim about
clause (iv).

## The counterexample: KTS(9) = lines of AG(2,3)

- Point set: F₃² = {(x, y) : x, y ∈ F₃}, 9 points.
- Line set (12 lines, 3 points each), written as triples:
  - for each slope m ∈ F₃ and intercept b ∈ F₃ (9 non-vertical lines):
    L₍ₘ,ᵦ₎ = {(x, mx + b) : x ∈ F₃};
  - for each c ∈ F₃ (3 vertical lines): V_c = {(c, y) : y ∈ F₃}.

### The 12 lines

| k | type | points |
|----|------|--------|
| 0 | m=0, b=0 | (0,0) (1,0) (2,0) |
| 1 | m=0, b=1 | (0,1) (1,1) (2,1) |
| 2 | m=0, b=2 | (0,2) (1,2) (2,2) |
| 3 | m=1, b=0 | (0,0) (1,1) (2,2) |
| 4 | m=1, b=1 | (0,1) (1,2) (2,0) |
| 5 | m=1, b=2 | (0,2) (1,0) (2,1) |
| 6 | m=2, b=0 | (0,0) (1,2) (2,1) |
| 7 | m=2, b=1 | (0,1) (1,0) (2,2) |
| 8 | m=2, b=2 | (0,2) (1,1) (2,0) |
| 9 | vertical, c=0 | (0,0) (0,1) (0,2) |
| 10 | vertical, c=1 | (1,0) (1,1) (1,2) |
| 11 | vertical, c=2 | (2,0) (2,1) (2,2) |

### Verification of the defining properties

(a) **Steiner triple system.** The 12 lines contain 12 · 3 = 36 point-pairs.
    A direct enumeration (independent recomputation in `reproduce.py`, and
    machine-checked in `lean4/`) shows that each of the 36 unordered pairs of
    distinct points lies in exactly one line (equivalently: all 81 ordered
    pairs (p, q), p ≠ q, are covered exactly once). So the 36 line-pairs are
    pairwise distinct and every pair of points is covered: STS(9).

(b) **Resolvable (Kirkman).** The 12 lines split into 4 parallel classes:
    C₀ = {k=0,1,2} (m = 0), C₁ = {k=3,4,5} (m = 1), C₂ = {k=6,7,8} (m = 2),
    C₃ = {k=9,10,11} (vertical). In each class the 3 lines are pairwise
    disjoint and their union is all 9 points; the 4 classes partition the 12
    lines. The number of parallel classes is 4 = (9−1)/2, consistent with
    clause (ii) of the conjecture.

(c) **Translations are automorphisms.** For each v ∈ F₃² the translation
    t_v(p) = p + v maps the line set onto itself: the image of each of the 12
    lines under t_v is again one of the 12 lines (verified for all 9 · 12
    pairs by enumeration).

(d) **Transitivity.** For all p, q ∈ F₃² the translation by v = q − p maps p
    to q. Hence the translation group F₃² (of order 9) acts transitively on
    the point set: the system is point-transitive.

**Conclusion.** KTS(9) is a point-transitive Kirkman triple system of order
9 < 15, so the smallest order of a KTS with a transitive automorphism is at
most 9, not 15. Clause (iii) of conjecture 00000008420 is false.

(Remark: the full automorphism group of this system is AGL(2,3) of order
9 · 48 = 432; only the transitivity of its translation subgroup is needed
here.)

## Files

- `reproduce.py` — dependency-free independent recomputation: builds the 12
  lines explicitly and checks (a)–(d); prints
  "KTS(9) is a point-transitive Kirkman triple system of order 9 < 15".
  Run: `python3 reproduce.py`.
- `lean4/` — machine-checked Lean 4 formalization (toolchain
  `leanprover/lean4:v4.33.1`, no dependencies): `lake build` then
  `lake env lean Check.lean`; all five theorems (`sts_property`,
  `resolvable`, `translation_invariant`, `transitive`, `refute`) are proved
  by `decide` and depend on no axioms. See `lean4/README.md`.
- `main.tex`, `build/main.pdf` — formal write-up (definitions, the
  construction, the 12-line table, verification of all four properties,
  conclusion).
- `build/log.txt` — LaTeX build log.

## Reproduction summary

```
$ python3 reproduce.py
(a) STS: each of the 36 point pairs lies in exactly one of the 12 lines  [OK]
(b) resolvable: 4 parallel classes, each 3 pairwise disjoint lines covering all 9 points; 4 = (9-1)/2  [OK]
(c) all 9 translations t_v(p) = p + v map the 12-line set onto itself  [OK]
(d) the translation group acts transitively on the 9 points  [OK]

KTS(9) is a point-transitive Kirkman triple system of order 9 < 15
```

```
$ cd lean4 && lake build && lake env lean Check.lean
true
true
true
true
9
12
'Tlmc8420.sts_property' does not depend on any axioms
'Tlmc8420.resolvable' does not depend on any axioms
'Tlmc8420.translation_invariant' does not depend on any axioms
'Tlmc8420.transitive' does not depend on any axioms
'Tlmc8420.refute' does not depend on any axioms
```
