import Std

namespace Tlmc5344

def comp (f g : Bool → Bool) : Bool → Bool := fun x => f (g x)

def f : Bool → Bool := fun _ => false
def g : Bool → Bool := fun x => !x

theorem fg_at_false : comp f g false = false := by decide
theorem gf_at_false : comp g f false = true := by decide

theorem composites_differ : comp f g ≠ comp g f := by
  intro h
  have hv := congrFun h false
  simp [comp, f, g] at hv

def StrictlyCommutative : Prop :=
  ∀ a b : Bool → Bool, comp a b = comp b a

/-- Function composition is horizontal composition in the locally discrete
strict bicategory associated to `Set`; this witness refutes commutativity. -/
theorem horizontal_composition_not_strictly_commutative :
    ¬ StrictlyCommutative := by
  intro h
  exact composites_differ (h f g)

end Tlmc5344
