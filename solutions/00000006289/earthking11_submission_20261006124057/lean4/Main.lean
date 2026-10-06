import Std

namespace Tlmc6289

/-- Multiplication on `C₂`, represented by `Bool`; `false` is the identity. -/
def mul : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

/-- The trivial one-dimensional representation, as a scalar matrix. -/
def rho (_ : Bool) : Int := 1

def character (g : Bool) : Int := rho g

theorem rho_multiplicative (a b : Bool) :
    rho (mul a b) = rho a * rho b := by
  cases a <;> cases b <;> decide

theorem nonidentity_trace_nonzero : character true = 1 := by decide

def support : List Bool :=
  [false, true].filter (fun g => character g != 0)

theorem support_is_whole_group : support = [false, true] := by decide

def IdentityOnlySupport : Prop :=
  ∀ g, character g ≠ 0 → g = false

theorem identity_only_support_false : ¬ IdentityOnlySupport := by
  intro h
  have hfalse := h true (by decide)
  cases hfalse

end Tlmc6289
