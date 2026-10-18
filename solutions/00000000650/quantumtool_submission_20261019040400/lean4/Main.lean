import Std

/-!
A finite arithmetic formalization of the counterexample to conjecture 00000000650.
The mathematical report identifies T(2,3) as the trefoil and proves its standard
invariants bridge number 2 and Seifert genus 1. The formulas below are the
standard torus-knot formulas, and Lean checks the resulting arithmetic failure.
-/

def torusBridgeNumber (p q : Nat) : Nat := min p q

def torusSeifertGenus (p q : Nat) : Nat := ((p - 1) * (q - 1)) / 2

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The first displayed bound in conjecture 00000000650. -/
def ceilBridgeBound (bridge genus : Nat) : Prop :=
  2 + ceilDiv genus (bridge - 1) ≤ bridge

/-- The proposed floor version in conjecture 00000000650. -/
def floorBridgeBound (bridge genus : Nat) : Prop :=
  2 + genus / ((bridge - 1) / 1) ≤ bridge

theorem torus_23_bridgeNumber : torusBridgeNumber 2 3 = 2 := by decide

theorem torus_23_genus : torusSeifertGenus 2 3 = 1 := by decide

theorem trefoil_refutes_both_bounds :
    ¬ ceilBridgeBound (torusBridgeNumber 2 3) (torusSeifertGenus 2 3) ∧
    ¬ floorBridgeBound (torusBridgeNumber 2 3) (torusSeifertGenus 2 3) := by
  simp [ceilBridgeBound, ceilDiv, floorBridgeBound, torusBridgeNumber, torusSeifertGenus]

#print axioms trefoil_refutes_both_bounds
