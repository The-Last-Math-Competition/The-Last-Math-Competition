import Std

namespace Tlmc3836

inductive Sign where
  | plus
  | minus
deriving DecidableEq, Repr

open Sign

/-- One stack update for deletion of adjacent `+ -` pairs. -/
def push : List Sign → Sign → List Sign
  | plus :: rest, minus => rest
  | stack, s => s :: stack

/-- Reduced signature, in reading order. -/
def signature (word : List Sign) : List Sign :=
  (word.foldl push []).reverse

def plusCount (word : List Sign) : Nat :=
  (signature word).count plus

def rotate : List Sign → List Sign
  | [] => []
  | x :: xs => xs ++ [x]

def witness : List Sign := [plus, minus]

theorem witness_output : signature witness = [] := by decide

theorem rotated_output : signature (rotate witness) = [minus, plus] := by decide

theorem plus_counts_differ :
    plusCount witness = 0 ∧ plusCount (rotate witness) = 1 := by
  decide

def RotationInvariant : Prop :=
  ∀ word : List Sign, plusCount word = plusCount (rotate word)

theorem rotation_invariance_false : ¬ RotationInvariant := by
  intro h
  have hw := h witness
  have hzero : plusCount witness = 0 := by decide
  have hone : plusCount (rotate witness) = 1 := by decide
  omega

end Tlmc3836
