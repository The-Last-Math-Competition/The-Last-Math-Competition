# Disproof of conjecture 00000001046

**Verdict: FALSE.**

## 0. Verbatim definition and object correspondence

Original conjecture (quoted verbatim from `conjectures/00000001046.md`):

> **English.** Conjecture: The differential uniformity of x ↦ x + x^{q−2} is 2 for large q (uniqueness of the optimal almost perfectly nonlinear (APN) function for large q).

Object-discipline declaration. We attack exactly the object named in this sentence:

- Map: `f : F_q → F_q`, `f(x) = x + x^{q−2}` over `F_q = GF(2^m)` (APN context, so `q = 2^m`).
  For `x ≠ 0`, `x^{q−2} = x^{−1}`, and `f(0) = 0` since `0^{q−2} = 0^{2^m−2} = 0`. So `f(x) = x + x^{−1}` (with `f(0)=0`) — the same map.
- Invariant: standard differential uniformity `δ(f) = max_{a ∈ F_q*, b ∈ F_q} #{x ∈ F_q : f(x+a) + f(x) = b}` (in characteristic 2, `f(x+a) − f(x) = f(x+a) + f(x)`).
- Claim attacked: "is 2 for large q", i.e. there is a threshold `q₀` with `δ(f) = 2` for all `q ≥ q₀`.

No renaming, no re-encoding: the function computed below is literally `x + x^{q−2}` on the full domain `F_q`, including the point `x = 0`.

## 1. Attack

Input difference `a = 1`, output difference `b = 0`:

- `f(x+1) = f(x)` ⇔ `1 = x^{−1} + (x+1)^{−1}` ⇔ `x(x+1) = 1` ⇔ `x² + x + 1 = 0` (for `x, x+1 ≠ 0`),
- plus the two degenerate solutions `x = 0` and `x = 1` (`f(0) = 0 = 1 + 1 = f(1)`).
- `x² + x + 1 = 0` has exactly two roots in `F_{2^m}` iff `3 | 2^m − 1` iff **m is even**.

Hence for **every even m**: `#{x : f(x+1) + f(x) = 0} = 4`, so `δ(f) ≥ 4 ≠ 2` — an infinite family of counterexamples with `q = 2^m` arbitrarily large. For odd `m` only `x = 0, 1` occur, consistent with `δ = 2`.

### Recomputed values (full enumeration over all a ∈ F_q*, b ∈ F_q)

| m | q | δ(f) | even/odd |
|---|---|------|----------|
| 4 | 16 | **4** | even |
| 5 | 32 | 2 | odd |
| 7 | 128 | 2 | odd |
| 8 | 256 | **4** | even |
| 9 | 512 | 2 | odd |
| 10 | 1024 | **4** | even |

Witness at q = 16: `(a, b) = (1, 0)` attained at `x ∈ {0, 1, 6, 7}`. At q = 256 and q = 1024 the same `(a, b) = (1, 0)` is attained 4 times (this count is field-representation-invariant: a field isomorphism preserves `+`, `·`, `⁻¹`, so it conjugates `f` to itself and preserves the count).

Even `m` gives arbitrarily large `q` (16, 256, 1024, …) with `δ = 4 ≠ 2`; therefore "δ(f) = 2 for large q" is **false**.

## 2. Lean certificate (`lean4/Main.lean`, checked by `lean4/Check.lean`)

- `TLMC1046.delta16_eq_4`: at `q = 16`, every derivative value occurs at most 4 times over all `a ≠ 0` **and** `(a,b) = (1,0)` occurs exactly 4 times — the full computation of `δ(f16) = 4`, kernel-decided (`decide` on table-driven concrete `Nat` arithmetic).
- `TLMC1046.cnt256_1_0 : cnt256 1 0 = 4` and `TLMC1046.cnt1024_1_0 : cnt1024 1 0 = 4`: the 4-fold occurrence of `(1, 0)` persists at q = 256 (GF(2)[X]/(X⁸+X⁴+X³+X+1)) and q = 1024 (GF(2)[X]/(X¹⁰+X³+1)).
- `TLMC1046.disproof` packages the exhibits.
- Zero `sorry`, zero `native_decide`; `Check.lean` prints `#print axioms` for all 9 theorems — axiom audit: 9/9 axiom-free (no `propext`, `Quot.sound`, `Classical.choice`).

## 3. Reproduction

- `python3 reproduce.py` — self-contained recomputation: irreducibility of all six field polynomials, full `δ` enumeration for q ∈ {16, 32, 128, 256, 512, 1024}, witness counts, and cross-checks of the exact tables embedded in `Main.lean`. Exits 0 iff all checks pass.
- Lean: `cd lean4 && lake build && lake env lean Check.lean`.

## 4. Boundaries

- The disproof does **not** claim `δ(f) = 4` for every even m from the enumerations alone; the infinite-family statement rests on the elementary algebra above (`x²+x+1=0` has 2 roots iff m even, giving `δ ≥ 4` for every even m), which is fully verified computationally at m = 4, 8, 10 and is consistent with the classical fact that `x + x^{−1}` is APN iff m is odd.
- For odd m the conjectured value `δ = 2` genuinely holds (verified at q = 32, 128, 512). The conjecture fails as stated because it ignores the even-m family.
- No claim is made about the APN-uniqueness part beyond what `δ ≠ 2` already refutes (the conjectured premise "δ = 2 for large q" is false).
