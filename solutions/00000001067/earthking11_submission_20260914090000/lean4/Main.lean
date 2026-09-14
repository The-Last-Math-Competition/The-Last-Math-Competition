/-
  Disproof of conjecture `00000001067`.

  Conjecture (as filed):
    Definition: A B_h set (unique h-fold sums).
    Conjecture: The maximal B_2 set in F_p has size ceil(sqrt p) + O(1),
    and the O(1) term equals 0 for p = 3 mod 4 (an exact B_2 result).

  The conjecture is FALSE.  The standard reading of "B_2 set with unique
  2-fold sums" is the STRONG Sidon set: all unordered sums a + b with a <= b
  (repetition allowed) are distinct.  For such a set of size k in F_p the
  k(k-1) ordered differences a - b (a != b) are pairwise distinct and nonzero,
  hence k(k-1) <= p - 1.  For p = 19 (= 3 mod 4) this forbids k = 5 because
  5*4 = 20 > 18 = p - 1, while ceil(sqrt 19) = 5.  Indeed no 5-element strong
  Sidon subset of F_19 exists (exhaustive boolean check), whereas {0,1,3,7} is
  a 4-element strong Sidon set.  So the maximal size is 4 <> ceil(sqrt 19) = 5
  for a prime p = 3 mod 4, and the "O(1) term = 0" clause is refuted.

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Tlmc1067

/-- The field `F_19` under the canonical presentation `Fin 19`. -/
abbrev F := Fin 19

/-- Addition in `F_19`. -/
def add (x y : F) : F := ⟨(x.val + y.val) % 19, Nat.mod_lt _ (by decide)⟩

/-- Translation `sub a x = x - a` in `F_19`. -/
def sub (a x : F) : F := ⟨(x.val + 19 - a.val) % 19, Nat.mod_lt _ (by decide)⟩

/-- The shift `neg2 a = -2a` in `F_19`, used to compare translated sum multisets. -/
def neg2 (a : F) : F := ⟨(19 - (2 * a.val) % 19) % 19, Nat.mod_lt _ (by decide)⟩

/-- The 15 unordered sums `x + y`, `x <= y`, of a 5-tuple (with repetition). -/
def sums (a b c d e : F) : List F :=
  [add a a, add a b, add a c, add a d, add a e,
   add b b, add b c, add b d, add b e,
   add c c, add c d, add c e,
   add d d, add d e, add e e]

/-- The 10 unordered sums `x + y`, `x <= y`, of a 4-tuple (with repetition). -/
def sums4 (a b c d : F) : List F :=
  [add a a, add a b, add a c, add a d,
   add b b, add b c, add b d, add c c, add c d, add d d]

/-- `sidon5 a b c d e = true` iff the 5-tuple has pairwise distinct 2-fold sums
(i.e. it is a strong Sidon configuration; in increasing order it is a strong
Sidon set of size 5). -/
def sidon5 (a b c d e : F) : Bool := (sums a b c d e).Nodup

/-- `sidon4 a b c d = true` iff the 4-tuple has pairwise distinct 2-fold sums. -/
def sidon4 (a b c d : F) : Bool := (sums4 a b c d).Nodup

/-! ## Translation invariance of the Sidon property -/

/-- `x |-> x + c` is injective on `F_19` (raw, decidable form). -/
theorem add_inj_raw : ∀ c x y : F, add x c = add y c → x = y := by decide

theorem add_inj (c : F) : Function.Injective (fun x : F => add x c) :=
  fun x y h => add_inj_raw c x y h

/-- Each sum of two translated points is the original sum shifted by `neg2 a`. -/
theorem step : ∀ a x y : F, add (sub a x) (sub a y) = add (add x y) (neg2 a) := by decide

theorem sub_self : ∀ a : F, sub a a = (0 : F) := by decide

/-- `sub a` sends positive elements to positive elements, order-preservingly. -/
theorem sub_pos : ∀ a b : F, a < b → (0 : F) < sub a b := by decide
theorem sub_lt : ∀ a b c : F, a < b → b < c → sub a b < sub a c := by decide

/-- Translation invariance: the sum multiset of a translated tuple is the image
of the original sum multiset under `z |-> z + neg2 a`, so distinctness of sums
is preserved.  This is the WLOG reduction "send the smallest element to 0". -/
theorem sidon_translate (a b c d e : F) (h : (sums a b c d e).Nodup) :
    (sums (sub a a) (sub a b) (sub a c) (sub a d) (sub a e)).Nodup := by
  have hmap : sums (sub a a) (sub a b) (sub a c) (sub a d) (sub a e)
      = (sums a b c d e).map (fun z => add z (neg2 a)) := by
    simp [sums, step]
  rw [hmap]
  exact List.Pairwise.map (fun z : F => add z (neg2 a))
    (fun x y hxy => fun heq => hxy (add_inj (neg2 a) heq)) h

/-! ## The p = 19 witness -/

/-- No strong Sidon 5-tuple in `F_19` whose first element is `0`.  This is the
decidable core; the general statement follows by translation invariance. -/
theorem no_sidon5_zero :
    ∀ b c d e : F, 0 < b → b < c → c < d → d < e → sidon5 0 b c d e = false := by
  decide

/-- **Main combinatorial theorem.**  There is no strong Sidon set of size 5 in
`F_19`: for every strictly increasing 5-tuple `a < b < c < d < e` the 15
unordered sums are not pairwise distinct.  Every 5-element subset can be listed
in increasing order, so this says exactly that the maximum size of a strong
Sidon set in `F_19` is at most 4. -/
theorem no_sidon5 :
    ∀ a b c d e : F, a < b → b < c → c < d → d < e → sidon5 a b c d e = false := by
  intro a b c d e h1 h2 h3 h4
  cases hb : sidon5 a b c d e with
  | false => rfl
  | true =>
    have hnd : (sums a b c d e).Nodup := by simpa [sidon5, hb] using hb
    have htr := sidon_translate a b c d e hnd
    have htrue : sidon5 0 (sub a b) (sub a c) (sub a d) (sub a e) = true := by
      simpa [sidon5, sub_self] using htr
    have hac : a < c := by rw [Fin.lt_def] at h1 h2 ⊢; omega
    have had : a < d := by rw [Fin.lt_def] at h1 h2 h3 ⊢; omega
    have hcontra := no_sidon5_zero (sub a b) (sub a c) (sub a d) (sub a e)
      (sub_pos a b h1) (sub_lt a b c h1 h2) (sub_lt a c d hac h3)
      (sub_lt a d e had h4)
    rw [htrue] at hcontra
    exact Bool.noConfusion hcontra

/-- The explicit strong Sidon set `{0,1,3,7}` in `F_19`: its 10 pairwise sums
`0,1,2,3,4,6,7,8,10,14` are pairwise distinct. -/
theorem sidon4_witness : sidon4 0 1 3 7 = true := by decide

/-- **Counting obstruction.**  A strong Sidon set of size `k` in `F_p` has
`k(k-1)` distinct nonzero differences, so `k(k-1) <= p-1`.  For `p = 19` and
`k = 5` this reads `5*4 > 19-1`. -/
theorem count_obstruction : 5 * 4 > 19 - 1 := by decide

/-- `ceil(sqrt 19) = 5`, expressed without real square roots:
`4^2 < 19` and `19 <= 5^2` pin `sqrt 19` in `(4,5]`. -/
theorem ceil_sqrt19 : 4 ^ 2 < 19 ∧ 19 ≤ 5 ^ 2 := by decide

/-- **Refutation of conjecture `00000001067`, packaged.**  There is a strong
Sidon 4-set, there is no strong Sidon 5-set, and `ceil(sqrt 19) = 5`:
for the prime `p = 19 = 3 mod 4` the maximal strong Sidon size is `4`, not
`ceil(sqrt 19) = 5`.  Hence the filed exact clause "the O(1) term equals 0 for
p = 3 mod 4" is false. -/
theorem conjecture_00000001067_false :
    (∃ a b c d : F, sidon4 a b c d = true) ∧
    (∀ a b c d e : F, a < b → b < c → c < d → d < e →
      sidon5 a b c d e = false) ∧
    (4 ^ 2 < 19 ∧ 19 ≤ 5 ^ 2) :=
  ⟨⟨0, 1, 3, 7, sidon4_witness⟩, no_sidon5, ceil_sqrt19⟩

end Tlmc1067
