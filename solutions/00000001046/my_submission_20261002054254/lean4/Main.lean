/-!
# Disproof of TLMC conjecture 00000001046

Conjecture: the differential uniformity of `x ↦ x + x^(q-2)` is `2` for
large `q`.

This file formalizes concrete counterexample instances in core Lean
(no Mathlib).  Elements of `GF(2^m) = GF(2)[α]/(f)` are encoded as `Nat`
literals in the polynomial basis `α^i ↦ bit i`; addition in `GF(2^m)` is
bitwise XOR (implemented by structural recursion on a fuel parameter, so
that every definition reduces by pure kernel evaluation without any
tactic-generated proofs).

* `GF(16)`, `f = α^4 + α + 1`:  `delta_16` proves that the differential
  uniformity of `F16 x = x + x^(q-2)` (`q = 16`) is exactly `4`, and
  `attack_instance_16` proves that the attack instance `a = 1`, `b = 0`
  has four solutions `x ∈ {0, 1, 6, 7}` (= `0, 1, α^5, α^10`, the roots of
  `y^2 + y + 1 = 0` in the subfield `GF(4)`).  Hence `δ(F16) ≥ 4 > 2`.
* `GF(32)`, `f = α^5 + α^2 + 1`:  `delta_32` proves that the differential
  uniformity is exactly `2` (odd-`m` boundary control).

Together with `reproduce.py` (exhaustive enumeration up to `q = 4096`:
even `m` gives `δ = 4` for `q = 16, 64, 256, 1024, 4096`, odd `m` gives
`δ = 2` for `q = 32, 128, 512, 2048`), this disproves the conjecture: for
arbitrarily large `q = 2^m` with even `m`, the differential uniformity is
`4 ≠ 2`.

All proofs are `rfl`: the kernel checks each closed literal equality by
direct evaluation.  No `sorry`, no `decide` instances, and (audited in
`Check.lean`) no axioms at all.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-! ## Bitwise XOR on `Nat`, by structural recursion on fuel -/

/-- XOR of two bits. -/
def bit2 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0

/-- XOR of `m`-bit values, recursing on the fuel. -/
def xorF : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, x, y => bit2 (x % 2) (y % 2) + 2 * xorF n (x / 2) (y / 2)

/-- XOR of 4-bit values: addition in `GF(16)`. -/
def xor16 (x y : Nat) : Nat := xorF 4 x y

/-- XOR of 5-bit values: addition in `GF(32)`. -/
def xor32 (x y : Nat) : Nat := xorF 5 x y

/-! ## GF(16) = GF(2)[α]/(α^4 + α + 1) -/

/-- Multiplication by `α`: double, reduce `α^4 = α + 1` (xor `3`) on overflow. -/
def xtime16 (x : Nat) : Nat :=
  if x / 8 % 2 == 1 then xor16 (x + x - 16) 3 else x + x

/-- Carry-less multiplication in `GF(16)` by shift-and-add. -/
def gfMul16 (x y : Nat) : Nat :=
  xor16 (xor16 (if y % 2 == 1 then x else 0)
               (if y / 2 % 2 == 1 then xtime16 x else 0))
       (xor16 (if y / 4 % 2 == 1 then xtime16 (xtime16 x) else 0)
               (if y / 8 % 2 == 1 then xtime16 (xtime16 (xtime16 x)) else 0))

/-- Multiplicative inverse in `GF(16)` (`0 ↦ 0`), as a table. -/
def gfInv16 (x : Nat) : Nat :=
  match x with
  | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 14
  | 4 => 13 | 5 => 11 | 6 => 7 | 7 => 6
  | 8 => 15 | 9 => 2 | 10 => 12 | 11 => 5
  | 12 => 10 | 13 => 4 | 14 => 3 | _ => 8

/-- The conjecture function `F x = x + x^(q-2)` over `GF(16)`. -/
def F16 (x : Nat) : Nat := xor16 x (gfInv16 x)

/-- Differential multiplicity: `#{x : F16 (x + a) + F16 x = b}` (XOR is
addition in characteristic 2). -/
def diffCount16 (a b : Nat) : Nat :=
  (List.range 16).countP
    (fun x => xor16 (F16 (xor16 x a)) (F16 x) == b)

/-- Differential uniformity of `F16`: max over all `a ≠ 0` and `b`. -/
def delta16 : Nat :=
  ((List.range 15).flatMap (fun i => (List.range 16).map (fun j => (i + 1, j)))).foldl
    (fun acc p => max acc (diffCount16 p.1 p.2)) 0

/-- The inverse table is consistent with the carry-less multiplication. -/
theorem gf_inv16_ok :
    (List.range 16).all (fun x =>
      (gfMul16 x (gfInv16 x) == 1) || (x == 0)) = true := by
  rfl

/-- Attack instance: `a = 1`, `b = 0` has exactly four preimages, so
`δ(F16) ≥ 4 > 2`. -/
theorem attack_instance_16 : diffCount16 1 0 = 4 := by
  rfl

/-- The four solutions of `F16 (x + 1) + F16 x = 0` are exactly
`0, 1, 6, 7` (= `0, 1, α^5, α^10`). -/
theorem attack_solutions_16 :
    (List.range 16).all (fun x =>
      (xor16 (F16 (xor16 x 1)) (F16 x) == 0)
        == (x == 0 || x == 1 || x == 6 || x == 7)) = true := by
  rfl

/-- Full enumeration: the differential uniformity of `x ↦ x + x^(q-2)` over
`GF(16)` is exactly `4`, not `2`. -/
theorem delta_16 : delta16 = 4 := by
  rfl

/-! ## GF(32) = GF(2)[α]/(α^5 + α^2 + 1) -/

/-- Multiplication by `α`: double, reduce `α^5 = α^2 + 1` (xor `5`) on overflow. -/
def xtime32 (x : Nat) : Nat :=
  if x / 16 % 2 == 1 then xor32 (x + x - 32) 5 else x + x

/-- Carry-less multiplication in `GF(32)` by shift-and-add. -/
def gfMul32 (x y : Nat) : Nat :=
  xor32
    (xor32 (xor32 (if y % 2 == 1 then x else 0)
                  (if y / 2 % 2 == 1 then xtime32 x else 0))
           (xor32 (if y / 4 % 2 == 1 then xtime32 (xtime32 x) else 0)
                  (if y / 8 % 2 == 1 then xtime32 (xtime32 (xtime32 x)) else 0)))
    (if y / 16 % 2 == 1 then xtime32 (xtime32 (xtime32 (xtime32 x))) else 0)

/-- Multiplicative inverse in `GF(32)` (`0 ↦ 0`), as a table. -/
def gfInv32 (x : Nat) : Nat :=
  match x with
  | 0 => 0 | 1 => 1 | 2 => 18 | 3 => 28
  | 4 => 9 | 5 => 23 | 6 => 14 | 7 => 12
  | 8 => 22 | 9 => 4 | 10 => 25 | 11 => 16
  | 12 => 7 | 13 => 15 | 14 => 6 | 15 => 13
  | 16 => 11 | 17 => 24 | 18 => 2 | 19 => 29
  | 20 => 30 | 21 => 26 | 22 => 8 | 23 => 5
  | 24 => 17 | 25 => 10 | 26 => 21 | 27 => 31
  | 28 => 3 | 29 => 19 | 30 => 20 | _ => 27

/-- The conjecture function `F x = x + x^(q-2)` over `GF(32)`. -/
def F32 (x : Nat) : Nat := xor32 x (gfInv32 x)

/-- Differential multiplicity for `F32`. -/
def diffCount32 (a b : Nat) : Nat :=
  (List.range 32).countP
    (fun x => xor32 (F32 (xor32 x a)) (F32 x) == b)

/-- Differential uniformity of `F32`: max over all `a ≠ 0` and `b`. -/
def delta32 : Nat :=
  ((List.range 31).flatMap (fun i => (List.range 32).map (fun j => (i + 1, j)))).foldl
    (fun acc p => max acc (diffCount32 p.1 p.2)) 0

/-- The inverse table is consistent with the carry-less multiplication. -/
theorem gf_inv32_ok :
    (List.range 32).all (fun x =>
      (gfMul32 x (gfInv32 x) == 1) || (x == 0)) = true := by
  rfl

/-- Attack instance: `a = 1`, `b = 0` has exactly two preimages. -/
theorem attack_instance_32 : diffCount32 1 0 = 2 := by
  rfl

set_option maxHeartbeats 10000000

/-- The solutions of `F32 (x + 1) + F32 x = 0` are exactly `0, 1`. -/
theorem attack_solutions_32 :
    (List.range 32).all (fun x =>
      (xor32 (F32 (xor32 x 1)) (F32 x) == 0)
        == (x == 0 || x == 1)) = true := by
  rfl

/-- Full enumeration: over `GF(32)` (odd `m`), the differential uniformity
of `x ↦ x + x^(q-2)` is exactly `2`. -/
theorem delta_32 : delta32 = 2 := by
  rfl
