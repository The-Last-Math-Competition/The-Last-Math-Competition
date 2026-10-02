# Disproof of TLMC conjecture 00000001046

**Verdict: FALSE.**

**Conjecture (00000001046).** The differential uniformity of `x ↦ x + x^(q−2)`
is 2 for large q (uniqueness of the optimal almost perfectly nonlinear (APN)
function for large q).

## Attack

Take the natural family `q = 2^m`, `F_q = GF(2)[α]/(f)`, `f` primitive of
degree `m`.  For `x ≠ 0`, `x^(q−2) = x^(−1)`, so
`F(x) = x + x^(q−2) = x + x^(−1)` and `F(0) = 0`.

**Claim.** For every `m` (hence for arbitrarily large `q`):

```
δ(F) = 4  if m is even,      δ(F) = 2  if m is odd,
```

where `δ(F) = max_{a≠0, b} #{x ∈ F_q : F(x+a) + F(x) = b}`.

**Proof.**

1. *Shift invariance.*  `x ↦ x` is `F_2`-linear, so for every `a ≠ 0`,
   `F(x+a) + F(x) = a + (x^(q−2) evaluated differentially)`, i.e. adding the
   linear map translates each derivative multiset by the constant `a`.
   Translation does not change maximum multiplicities, hence
   `δ(x + x^(q−2)) = δ(x^(q−2))`.  So we may analyse `G = x^(q−2)`.
2. *General upper bound 4.*  For `x ∉ {0, a}`:
   `G(x+a) + G(x) = (x+a)^(−1) + x^(−1) = a / (x² + a x)`.  For any value
   `b` this is a quadratic equation in `x`: at most 2 solutions.  The two
   special points give `G(a) + G(0) = a^(−1)` twice, so only the value
   `b₀ = a^(−1)` can exceed 2 solutions.  Hence `δ ≤ 4` always.
3. *Even `m` gives exactly 4.*  The extra solutions of `b₀` satisfy
   `x² + ax = a²`, i.e. `(x/a)² + (x/a) + 1 = 0`, which has 2 roots in `F_q`
   iff `GF(4) ⊆ F_q` iff `2 | m`.  Hence `b₀` has `2 + 2 = 4` solutions and
   `δ = 4`.
4. *Odd `m` gives exactly 2.*  `GF(4) ⊄ F_q`, so `b₀` has exactly 2
   solutions and every value has ≤ 2 solutions: `δ = 2`.  ∎

Consequently, for arbitrarily large `q` with even `m`, `δ(F) = 4 ≠ 2`.
The conjecture "δ = 2 for large q" is **false**; the correct statement is
parity-dependent, and the even-`m` subfamily has no large-`q` exceptions.

## Exhaustive verification (`reproduce.py`)

Independent recomputation (own carry-less multiplication; the inverse table
is verified elementwise; primitive polynomials are found and verified by
order checks).  `numpy` is used only to speed up the enumeration, with a
pure-Python fallback.

| m | q | parity | δ(F) |
|---|---|---|---|
| 4 | 16 | even | **4** |
| 5 | 32 | odd | 2 |
| 6 | 64 | even | **4** |
| 7 | 128 | odd | 2 |
| 8 | 256 | even | **4** |
| 9 | 512 | odd | 2 |
| 10 | 1024 | even | **4** |
| 11 | 2048 | odd | 2 |
| 12 | 4096 | even | **4** |

Concrete smallest attack instance (`q = 16`, `α⁴ = α + 1`): `a = 1`, `b = 0`;
`F(x+1) + F(x) = 0` has the four solutions
`x ∈ {0, 1, α⁵, α¹⁰} = {0, 1, 6, 7}` — the two special points `0, a` plus
the two roots of `y² + y + 1 = 0` in `GF(4)`.

```sh
python3 reproduce.py    # ~1 min; numpy optional
```

## Lean verification (`lean4/`)

Core Lean 4.33.1, no Mathlib, **zero axioms, zero `sorry`**
(`lake env lean Check.lean` reports "does not depend on any axioms" for all
theorems):

* `delta_16 : delta16 = 4` — full 15 × 16 enumeration of the differential
  uniformity of `x ↦ x + x^(q−2)` over `GF(16)`;
* `attack_instance_16 : diffCount16 1 0 = 4` and
  `attack_solutions_16` — the solutions are exactly `0, 1, 6, 7`;
* `delta_32 : delta32 = 2` — full enumeration over `GF(32)` (odd-`m`
  boundary control);
* `gf_inv16_ok`, `gf_inv32_ok` — the inverse tables are checked against an
  independently written carry-less multiplication, so the model really is
  `GF(2^m)`.

## Conclusion

The differential uniformity of `x ↦ x + x^(q−2)` over `F_{2^m}` equals 4 for
every even `m` and 2 for every odd `m` — proved above and confirmed by
exhaustive computation for `q` up to `4096`.  Since even `m` is unbounded,
there are arbitrarily large `q` with `δ = 4 ≠ 2`, disproving the conjecture.

## Reproduction summary

1. `python3 reproduce.py` — recomputes the table above from scratch.
2. `cd lean4 && lake build && lake env lean Check.lean` — machine-checked
   counterexample instance with zero axioms.
