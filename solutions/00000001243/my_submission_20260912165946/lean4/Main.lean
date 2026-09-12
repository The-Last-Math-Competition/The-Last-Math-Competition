/-
  Disproof of conjecture 00000001243:

      "The central column of Wolfram's rule 30 is square-free over all
       prefixes of length 2^k."

  The refutation does not use any dynamics of rule 30.  The central column is
  a binary sequence, and NO binary word of length >= 4 is square-free.  Hence
  the conjectured property is satisfied by no binary sequence at all, and the
  conjecture cannot serve its stated purpose of "ruling out any short-period
  structure".

  Lean 4, core only -- no Mathlib dependency.
-/

namespace Tlmc1243

/-! ## Squares in binary words -/

/-- `w` contains a square: a nonempty factor `u` occurring twice consecutively. -/
def HasSquare (w : List Bool) : Prop :=
  ∃ s p : Nat, 0 < p ∧ s + 2 * p ≤ w.length ∧
    (w.drop s).take p = (w.drop (s + p)).take p

/-- **The four-case lemma.** Every binary word of length at least 4 has a square.

If the first four letters are `a b c d`, then either `a = b`, or `a ≠ b` and
`b = c`, or `a ≠ b`, `b ≠ c`, `c = d`, or all three adjacent pairs differ --
in which case `c = a` and `d = b` because the alphabet has two letters, so
`a b c d = (a b)²`. -/
theorem binary_word_has_square (w : List Bool) (h : 4 ≤ w.length) : HasSquare w := by
  match w with
  | [] => exact absurd h (by simp)
  | [_] => exact absurd h (by simp)
  | [_, _] => exact absurd h (by simp)
  | [_, _, _] => exact absurd h (by simp)
  | a :: b :: c :: d :: t =>
    by_cases hab : a = b
    · exact ⟨0, 1, by decide, by simp, by simp [hab]⟩
    · by_cases hbc : b = c
      · exact ⟨1, 1, by decide, by simp, by simp [hbc]⟩
      · by_cases hcd : c = d
        · exact ⟨2, 1, by decide, by simp, by simp [hcd]⟩
        · have hca : c = a := by cases a <;> cases b <;> cases c <;> simp_all
          have hdb : d = b := by cases b <;> cases c <;> cases d <;> simp_all
          exact ⟨0, 2, by decide, by simp, by simp [hca, hdb]⟩

/-- Corollary: no binary sequence is square-free over prefixes of length `2^k`
for `k ≥ 2`. -/
theorem no_square_free_binary_prefix (f : Nat → Bool) (k : Nat) (hk : 2 ≤ k) :
    HasSquare ((List.range (2 ^ k)).map f) := by
  apply binary_word_has_square
  rw [List.length_map, List.length_range]
  calc 4 = 2 ^ 2 := by decide
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk

/-! ## The central column of rule 30 -/

/-- One step of elementary cellular automaton rule 30 on a finite row:
`new(i) = left(i) XOR (centre(i) OR right(i))`, with `false` outside. -/
def rule30Step (r : List Bool) : List Bool :=
  (List.range r.length).map fun i =>
    let l := if i = 0 then false else r.getD (i - 1) false
    let c := r.getD i false
    let rr := r.getD (i + 1) false
    l ^^ (c || rr)

/-- Iterate `rule30Step`, recording the cell at `centre` at each step. -/
def rule30Aux (centre : Nat) : Nat → List Bool → List Bool
  | 0, _ => []
  | k + 1, r => r.getD centre false :: rule30Aux centre k (rule30Step r)

/-- The central column of rule 30 from a single `1` at position 0, `n` terms.
The row is wide enough that the light cone never reaches the boundary. -/
def centralColumn (n : Nat) : List Bool :=
  let width := 2 * n + 1
  rule30Aux n n ((List.range width).map fun i => i == n)

/-- The first two terms of the central column are both `true`, so `11` is a
square of period 1 at position 0. -/
theorem central_column_starts_11 : (centralColumn 32).take 2 = [true, true] := by
  decide

/-- **The counterexample.** The central column is not square-free. -/
theorem central_column_has_square : HasSquare (centralColumn 32) :=
  ⟨0, 1, by decide, by decide, by decide⟩

/-! ## The conjecture is false -/

/-- The property asserted by conjecture `00000001243`: the sequence is
square-free over every prefix of length `2 ^ k`. -/
def SquareFreeOverPow2Prefixes (f : Nat → Bool) : Prop :=
  ∀ k : Nat, ¬ HasSquare ((List.range (2 ^ k)).map f)

/-- **Conjecture `00000001243` is false.** Not merely for the central column of
rule 30: no binary sequence whatsoever has the asserted property. -/
theorem conjecture_00000001243_false (f : Nat → Bool) :
    ¬ SquareFreeOverPow2Prefixes f := by
  intro hf
  exact hf 2 (no_square_free_binary_prefix f 2 (by decide))

/-- The refutation instantiated at the central column. -/
theorem rule30_central_column_refutes_conjecture :
    ¬ SquareFreeOverPow2Prefixes (fun t => (centralColumn (t + 1)).getD t false) :=
  conjecture_00000001243_false _

end Tlmc1243
