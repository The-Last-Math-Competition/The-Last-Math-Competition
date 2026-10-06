import Std

namespace Tlmc7669

inductive Move where
  | A
  | B
deriving DecidableEq, Repr

def histories3 : List (List Move) :=
  [[.A,.A,.A], [.A,.A,.B], [.A,.B,.A], [.A,.B,.B],
   [.B,.A,.A], [.B,.A,.B], [.B,.B,.A], [.B,.B,.B]]

/-- Endpoint exponent pair `(number of A moves, number of B moves)`. -/
def endpoint (w : List Move) : Nat × Nat :=
  w.foldl (fun p m => match m with
    | .A => (p.1 + 1, p.2)
    | .B => (p.1, p.2 + 1)) (0, 0)

def endpoints3 : List (Nat × Nat) := (histories3.map endpoint).eraseDups

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem history_count : histories3.length = 8 := by decide

theorem endpoint_list : endpoints3 = [(3,0), (2,1), (1,2), (0,3)] := by decide

theorem endpoint_count : endpoints3.length = 4 := by decide

theorem conjectured_count : fib (3 + 2) = 5 := by decide

theorem tree_reading_refutes : histories3.length ≠ fib (3 + 2) := by decide

theorem quotient_reading_refutes : endpoints3.length ≠ fib (3 + 2) := by decide

end Tlmc7669
