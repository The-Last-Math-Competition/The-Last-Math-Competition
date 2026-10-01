/-!
# Disproof of TLMC conjecture 00000000591

New-direction conjecture attached to Wilf's conjecture, restricted to numerical
semigroups of embedding dimension e = 3:

  with  n(S) = #{s in S : 0 <= s <= g(S)}  (nongaps up to the Frobenius number g),
  claim:  (e*n(S) - g(S) - e) / g(S) -> 0  as g(S) -> infinity.

Verdict: FALSE.

Fully kernel-checked concrete attacks below (pure `rfl`/`decide`, core Lean only,
no Mathlib, no axioms, no `sorry`):

* `<17,23,29>`:  g = 215, n = 104, surplus = 94,  surplus/g = 94/215   > 2/5
* `<9,13,101>`:  g = 95,  n = 48,  surplus = 46,  surplus/g = 46/95   > 2/5
* `<15,33,55>`:  g = 227, n = 114, surplus = 112, surplus/g = 112/227 > 2/5
* `<35,55,77>`:  g = 603, n = 302, surplus = 300, surplus/g = 300/603 > 2/5

Each "cover" theorem checks that a run of `multiplicity` consecutive integers above
the stated g are nongaps; together with closure of the semigroup under addition
(add the generator repeatedly) this certifies that the stated g is exactly the
Frobenius number. The family `<pq, pr, qr>` (p,q,r distinct primes) is a complete
intersection, hence symmetric, so n = (g+1)/2, surplus = (g-3)/2 and
surplus/g = (g-3)/(2g) -> 1/2 along g -> infinity (verified numerically up to
g = 2194011 in reproduce.py) — the ratio stays near its universal ceiling 1/2
instead of tending to 0.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

-- Exhaustive bounded search for a representation `n = x*a + y*b + z*c` with
-- `x, y, z >= 0`. Any representation has `y <= n/b` and `z <= n/c`, so searching
-- `y in [0, n/b]`, `z in [0, n/c]` and testing `(n - y*b - z*c)` for divisibility
-- by `a` is sound and complete.
def rep (a b c n : Nat) : Bool :=
  (List.range (n / b + 1)).any fun y =>
    (List.range (n / c + 1)).any fun z =>
      let s := y * b + z * c
      s ≤ n && (n - s) % a == 0

-- Number of nongaps of `<a,b,c>` among `0, 1, ..., upto - 1`.
def countNongaps (a b c upto : Nat) : Nat :=
  (List.range upto).filter (fun k => rep a b c k) |>.length

-- Wilf surplus with embedding dimension e = 3.
def surplus (n g : Nat) : Nat := 3 * n - g - 3

-- ==================== instance `<17,23,29>`, g = 215 ====================

-- 215 is a gap.
theorem gap_17_23_29 : rep 17 23 29 215 = false := rfl

-- The 17 consecutive integers 216..232 are all nongaps; closure under +17 then
-- makes every n >= 216 a nongap, so g(`<17,23,29>`) = 215.
theorem cover_17_23_29 : (List.range 17).all (fun k => rep 17 23 29 (216 + k)) = true := rfl

theorem count_17_23_29 : countNongaps 17 23 29 216 = 104 := rfl

theorem surplus_17_23_29 : surplus 104 215 = 94 := rfl

-- surplus/g = 94/215 ≈ 0.4372 > 2/5: bounded away from 0.
theorem ratio_17_23_29 : (2 * 215 : Nat) < 5 * 94 := by decide

-- ==================== instance `<9,13,101>`, g = 95 ====================

theorem gap_9_13_101 : rep 9 13 101 95 = false := rfl

theorem cover_9_13_101 : (List.range 9).all (fun k => rep 9 13 101 (96 + k)) = true := rfl

theorem count_9_13_101 : countNongaps 9 13 101 96 = 48 := rfl

theorem surplus_9_13_101 : surplus 48 95 = 46 := rfl

theorem ratio_9_13_101 : (2 * 95 : Nat) < 5 * 46 := by decide

-- ==================== instance `<15,33,55>`, g = 227 (symmetric CI family) ====================

theorem gap_15_33_55 : rep 15 33 55 227 = false := rfl

theorem cover_15_33_55 : (List.range 15).all (fun k => rep 15 33 55 (228 + k)) = true := rfl

-- n = 114 = (g+1)/2 exactly: this semigroup is symmetric.
theorem count_15_33_55 : countNongaps 15 33 55 228 = 114 := rfl

theorem surplus_15_33_55 : surplus 114 227 = 112 := rfl

theorem ratio_15_33_55 : (2 * 227 : Nat) < 5 * 112 := by decide

-- ==================== instance `<35,55,77>`, g = 603 (symmetric CI family) ====================

theorem gap_35_55_77 : rep 35 55 77 603 = false := rfl

theorem cover_35_55_77 : (List.range 35).all (fun k => rep 35 55 77 (604 + k)) = true := rfl

theorem count_35_55_77 : countNongaps 35 55 77 604 = 302 := rfl

theorem surplus_35_55_77 : surplus 302 603 = 300 := rfl

theorem ratio_35_55_77 : (2 * 603 : Nat) < 5 * 300 := by decide

-- ==================== combined disproof statement ====================

-- For four embedding-dimension-3 semigroups the Wilf surplus ratio is exactly
-- the stated positive value and exceeds 2/5, so it cannot tend to 0 along this
-- family (which continues to infinity: `<pq,pr,qr>` has g = 2pqr - pq - pr - qr).
theorem main :
    rep 17 23 29 215 = false ∧
    (List.range 17).all (fun k => rep 17 23 29 (216 + k)) = true ∧
    countNongaps 17 23 29 216 = 104 ∧
    surplus 104 215 = 94 ∧
    (2 * 215 : Nat) < 5 * 94 ∧
    rep 9 13 101 95 = false ∧
    (List.range 9).all (fun k => rep 9 13 101 (96 + k)) = true ∧
    countNongaps 9 13 101 96 = 48 ∧
    surplus 48 95 = 46 ∧
    (2 * 95 : Nat) < 5 * 46 ∧
    rep 15 33 55 227 = false ∧
    (List.range 15).all (fun k => rep 15 33 55 (228 + k)) = true ∧
    countNongaps 15 33 55 228 = 114 ∧
    surplus 114 227 = 112 ∧
    (2 * 227 : Nat) < 5 * 112 ∧
    rep 35 55 77 603 = false ∧
    (List.range 35).all (fun k => rep 35 55 77 (604 + k)) = true ∧
    countNongaps 35 55 77 604 = 302 ∧
    surplus 302 603 = 300 ∧
    (2 * 603 : Nat) < 5 * 300 := by
  exact ⟨gap_17_23_29, cover_17_23_29, count_17_23_29, surplus_17_23_29, ratio_17_23_29,
         gap_9_13_101, cover_9_13_101, count_9_13_101, surplus_9_13_101, ratio_9_13_101,
         gap_15_33_55, cover_15_33_55, count_15_33_55, surplus_15_33_55, ratio_15_33_55,
         gap_35_55_77, cover_35_55_77, count_35_55_77, surplus_35_55_77, ratio_35_55_77⟩
