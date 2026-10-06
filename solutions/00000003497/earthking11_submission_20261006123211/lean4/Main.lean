import Std

namespace Tlmc3497

/-- A positive scale determines a Hermitian metric on a one-dimensional fibre. -/
abbrev Metric := {n : Nat // 0 < n}

/-- On a point there is exactly one connection. -/
abbrev Connection := Unit

/-- Every metric on a bundle over a point has the unique connection. -/
def chernConnection (_ : Metric) : Connection := ()

def hOne : Metric := ⟨1, by decide⟩
def hTwo : Metric := ⟨2, by decide⟩

theorem metrics_distinct : hOne ≠ hTwo := by
  intro h
  have hv : hOne.val = hTwo.val := congrArg Subtype.val h
  simp [hOne, hTwo] at hv

theorem same_chern_connection : chernConnection hOne = chernConnection hTwo := by
  rfl

/-- The conjectured injectivity already fails on the trivial line over a point. -/
theorem chern_not_injective : ¬ Function.Injective chernConnection := by
  intro hinj
  exact metrics_distinct (hinj same_chern_connection)

theorem chern_not_bijective :
    ¬ (Function.Injective chernConnection ∧ Function.Surjective chernConnection) := by
  intro hbij
  exact chern_not_injective hbij.1

end Tlmc3497
