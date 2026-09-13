/-
  Refutation of conjecture 00000001202.

  The conjecture states that the Sprague-Grundy (SG) sequence of the
  octal game 0.07 is eventually periodic with period 12 and pre-period 4,
  i.e. that `g (n + 12) = g n` for all `n ≥ 4`.

  Under the standard reading of `0.07` (octal digits `d₁ = 0`, `d₂ = 7`)
  a move removes exactly two tokens and may split the remaining tokens
  into 0, 1 or 2 heaps, so for `n ≥ 2`

      g(n) = mex { g(a) XOR g(b) : a + b = n - 2 }.

  This is Dawson's Kayles.  The conjecture is false already for `n = 4`:
  here `g 4 = 2` while `g 16 = 5`, so `g 4 ≠ g 16 = g (4 + 12)`.

  This file formalises, in core Lean 4 (`import Std`, no Mathlib, no
  `sorry`, no `axiom`, no `native_decide`), the computable SG recurrence
  and the single refuting instance `n = 4`.  The full eventual period
  (34, with pre-period 53) and the second reading of the prose
  (`0.77` = Kayles, eventual period 12 but pre-period 71) are computed in
  `reproduce.py`; see `lean4/README.md` for the precise scope.
-/
import Std

-- The kernel must reduce `g 16`, whose computation nests `List.range`
-- folds; the default recursion depth (1000) is too small.
set_option maxRecDepth 1000000

namespace Tlmc1202

/-- `mex s` is the smallest natural number that does not occur in the
list `s`.  Implemented with explicit fuel so that it is structurally
recursive (and therefore reduces in the kernel). -/
def mex (s : List Nat) : Nat :=
  let rec go (fuel k : Nat) : Nat :=
    match fuel with
    | 0     => k
    | f + 1 => if s.contains k then go f (k + 1) else k
  go (s.length + 1) 0

/-- `look l i` is the `i`-th entry of `l`, defaulting to `0` when `i` is
out of range.  A hand-rolled lookup (rather than `List.getD`) keeps the
definition free of `propext`, so the axiom audit of the theorems below is
completely clean. -/
def look : List Nat → Nat → Nat
  | [],      _     => 0
  | x :: _,  0     => x
  | _ :: xs, i + 1 => look xs i

/-- One step of the SG recurrence for the octal game `0.07`.

  `prev` is the list of previously computed values
  `[g 0, g 1, …, g (n-1)]`.  A move at a heap of size `n` removes exactly
  two tokens and splits the remaining `n - 2` tokens into two heaps of
  sizes `a` and `b` (either of which may be empty), so the reachable
  nim-values are `g a XOR g b` over `a + b = n - 2`. -/
def sgOf (prev : List Nat) (n : Nat) : Nat :=
  mex ((List.range (n - 1)).map
        (fun a => look prev a ^^^ look prev (n - 2 - a)))

/-- The list `[g 0, g 1, …, g (n-1)]` of the first `n` SG values, defined
by structural recursion on `n` so that concrete instances reduce in the
kernel. -/
def gList : Nat → List Nat
  | 0     => []
  | n + 1 => let prev := gList n; prev ++ [sgOf prev n]

/-- The Sprague-Grundy value `g n` of a heap of `n` tokens in the octal
game `0.07` (Dawson's Kayles). -/
def g (n : Nat) : Nat := look (gList (n + 1)) n

/-- Computed value at `n = 4`. -/
theorem g4 : g 4 = 2 := by decide

/-- Computed value at `n = 16`. -/
theorem g16 : g 16 = 5 := by decide

/-- The claimed period-12 identity fails at `n = 4`: `g 4 = 2` but
`g 16 = 5`.  This is the concrete refuting instance. -/
theorem period12_fails_at_4 : g 4 ≠ g 16 := by decide

/-- The conjecture `00000001202` is false: the asserted identity
`g (n + 12) = g n` for all `n ≥ 4` fails at `n = 4`, where `g 4 = 2` and
`g 16 = 5`. -/
theorem conjecture_00000001202_false :
    g 4 ≠ g 16 ∧ g 4 = 2 ∧ g 16 = 5 :=
  ⟨period12_fails_at_4, g4, g16⟩

end Tlmc1202
