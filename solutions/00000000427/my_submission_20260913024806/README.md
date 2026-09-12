# Disproof of Conjecture 00000000427

**Verdict: FALSE.**

## The conjecture

> Spin symmetric plane partitions are plane partitions in a cubic box symmetric
> under all diagonals and weighted by spin. Their count at t = 1 equals
> `2^{⌊n²/4⌋} · ∏_{i=1}^{n} (2i−1)!! / i!`, and the ratio of this formula to the
> unsymmetrized MacMahon formula is exactly a product of a power of two and
> double factorials, with no other prime factors.

At `t = 1` the spin weight is identically `1`, so it does not affect any count;
the claim is purely about the diagonal-symmetry count.

## Setup and encoding

A plane partition in an `n × n × n` cubic box is an order ideal of the poset
`[n] × [n] × [n]`, equivalently a monotone non-decreasing height function
`h : {0,…,n−1}³ → {0,1}` (`h(cell) = 1` iff the cell belongs to the ideal).
MacMahon's product formula `∏_{i,j,k=1..n} (i+j+k−1)/(i+j+k−2)` counts **all**
plane partitions in the box: `M(1) = 2`, `M(2) = 20`. Our enumeration
reproduces these totals exactly.

Two natural readings of "symmetric under all diagonals" were enumerated:

- **A (mirror):** `h` is invariant under *every* transposition of coordinates,
  i.e. `h(i,j,k) = h(j,i,k) = h(k,j,i)` for all cells;
- **B (cyclic):** `h` is invariant under the 3-cycle `(i→j→k→i)`, i.e.
  `h(i,j,k) = h(j,k,i)`.

(On the cube `{0,1}³` both readings generate the same partition into four
orbits `{(0,0,0)}; {(1,0,0),(0,1,0),(0,0,1)}; {(1,1,0),(1,0,1),(0,1,1)};
{(1,1,1)}`, and the enumeration confirms they give identical counts.)

## Counterexamples

Enumerating **all** height functions and filtering monotone ones
(`reproduce.py`; certified in Lean 4 with zero axioms in `lean4/`):

| n | all height functions | monotone (= plane partitions, MacMahon) | mono + mirror sym (A) | mono + cyclic sym (B) | conjectured formula `2^{⌊n²/4⌋}·∏(2i−1)!!/i!` |
|---|---|---|---|---|---|
| 1 | 2 = 2¹ | **2** (= MacMahon(1,1,1) = 2) | **2** | **2** | `2⁰·(1!!/1!) = 1` |
| 2 | 256 = 2⁸ | **20** (= MacMahon(2,2,2) = 20) | **5** | **5** | `2¹·(1!!/1!)·(3!!/2!) = 2·3/2 = 3` |

- **n = 2:** the true diagonally-symmetric count is `5` under both readings,
  but the formula gives `3`.  Since `5 ≠ 3`, the conjecture is FALSE.
- **n = 1:** the true count is `2` (the empty partition and the full one, both
  trivially symmetric), but the formula gives `1`.  `2 ≠ 1` — also FALSE.

The 5 diagonally symmetric plane partitions of the `2×2×2` box, given by orbit
values `(a,b,c,d) = (h(0,0,0), h(1,0,0), h(1,1,0), h(1,1,1))`:

```
(0,0,0,0)   (0,0,0,1)   (0,0,1,1)   (0,1,1,1)   (1,1,1,1)
```

i.e. exactly the non-decreasing `0-1` quadruples `a ≤ b ≤ c ≤ d`.

## Scope / boundary of the disproof

- MacMahon's product formula itself is **correct** and is not contested: our
  enumeration reproduces `M(1) = 2` and `M(2) = 20` exactly.  What is refuted
  is the claimed **closed form for the diagonal-symmetry count**
  `2^{⌊n²/4⌋}·∏(2i−1)!!/i!` at `t = 1` (and consequently also the claimed
  shape of its ratio to the MacMahon formula).
- The refutation is robust under the alternative (non-standard) encoding in
  which the height function is `3`-valued, `h : {0,1}³ → {0,1,2}`: then the
  monotone functions number `168 = MacMahon(2,2,2,2)` and the symmetric ones
  `15`, which again differs from the formula value `3` under both readings.
- At `t = 1` the spin weight is identically `1`; the disproof therefore needs
  no assumptions about the spin weighting.

## Files

- `reproduce.py` — standalone enumeration (no dependencies, no absolute
  paths); asserts that both readings refute the formula.
- `main.tex`, `build/main.pdf`, `build/log.txt` — formal write-up.
- `lean4/` — Lean 4 project (`leanprover/lean4:v4.33.1`), zero axioms, zero
  `sorry`; `Check.lean` prints `#print axioms` for every theorem.
