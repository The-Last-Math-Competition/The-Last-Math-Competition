# Disproof of conjecture `00000003842`

**Verdict: FALSE at the first non-trivial instance — n = 2, ℓ = 2:
the hypoplactic classes number at most 6 (there are only 6 nonempty
words of length ≤ 2 over {a, b}), while the 2×2×2 box contains
exactly 20 plane partitions (brute-force enumeration = 20;
MacMahon's product formula 17280/864 = 20).  20 > 6: the claimed
equality is impossible — no quotient can have more classes than
words.  (Cross-check: even n = ℓ = 1 gives 1 class vs 2 plane
partitions in 2×1×1.)**

## The conjecture (verbatim from `conjectures/00000003842.md`)

> Definition: The hypoplactic monoid denotes the refinement quotient
> of Knuth equivalence by adjoining hypoplactic relations, whose
> classes are characterized by quasi-symmetric leading-term exponent
> vectors. Conjecture: The number of hypoplactic classes of length
> at most ℓ over an n-letter alphabet equals the number of plane
> partitions in a 2×n×ℓ box. (hypo class-plane partition count)

## The refutation

Whatever the hypoplactic quotient does, the number of its classes
cannot exceed the number of words: over the 2-letter alphabet
{a, b}, the nonempty words of length at most 2 are a, b, aa, ab, ba,
bb — exactly 6, hence at most 6 classes at (n, ℓ) = (2, 2).

The plane-partition side is fixed by arithmetic: the 2×2×2 box
contains exactly 20 plane partitions.  This is both the brute-force
count (20 matrices weakly decreasing along rows and columns with
entries ≤ 2, out of 81 candidates) and MacMahon's product formula
∏_{i,j,k≤2} (i+j+k−1)/(i+j+k−2) = 17280/864 = 20.

20 > 6: the claimed equality fails at its first non-trivial
instance, independent of any subtlety in the hypoplactic relations
(the relations can only merge classes, reducing 6 further).  Even
n = ℓ = 1 is off: 1 class (the word "a") vs 2 plane partitions in
the 2×1×1 box.  (The classical true statement in this territory —
Kostka/SSYT counts and plane partitions — does not have the shape
the conjecture asserts for class counts of the hypoplactic monoid.)

## Verification

* `reproduce.py` — the 6-word enumeration; the 2×2×2 brute-force
  count 20 with the MacMahon cross-check; the n = ℓ = 1
  cross-check (1 vs 2).
* Lean 4 (core, v4.33.1), `lean4/` — `word_count` (2 + 4 = 6),
  `classes_le_words`, `macmahon_222` (17280/864 = 20),
  `twenty_gt_six` (20 > 6), `conjecture_refuted`.  All 5 audited
  theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the word count (hence the class ceiling) and
the MacMahon ratio; the plane-partition enumeration and the
hypoplactic-quotient monotonicity (relations only merge) are carried
by the script and prose.  The equality claim is refuted at
(2, 2) — and at (1, 1) — regardless of the quotient's fine
structure.
