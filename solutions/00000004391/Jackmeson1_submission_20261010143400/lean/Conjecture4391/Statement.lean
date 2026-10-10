import Mathlib

/-! Formal statement for Conjecture4391: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C4391
open MeasureTheory Set

/-- A graphon: a symmetric measurable function `[0,1]^2 -> [0,1]` (stored on all of `R^2`,
only the values on `[0,1]^2` are used). -/
structure Graphon where
  W : ℝ → ℝ → ℝ
  meas : Measurable (Function.uncurry W)
  symm : ∀ x y, W x y = W y x
  nonneg : ∀ x y, 0 ≤ W x y
  le_one : ∀ x y, W x y ≤ 1

/-- "fixed edge density": the edge density of a graphon is `∫∫ W` over `[0,1]^2`. -/
noncomputable def density (G : Graphon) : ℝ := ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, G.W x y

/-- "its integral operator": `(T_W f)(x) = ∫_0^1 W(x,y) f(y) dy`. -/
noncomputable def op (G : Graphon) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0:ℝ)..1, G.W x y * f y

/-- "eigenvalue of its integral operator": `lam` is an eigenvalue of `T_W` on `L²[0,1]` if some
`f ∈ L²[0,1]`, not a.e. zero, satisfies `T_W f = lam f` almost everywhere on `[0,1]`
(real scalars; `T_W` is self-adjoint so its spectrum is real). -/
def IsEigenvalue (G : Graphon) (lam : ℝ) : Prop :=
  ∃ f : ℝ → ℝ, MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)) ∧
    ¬ (f =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] 0) ∧
    ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) 1)), op G f x = lam * f x

/-- "the spectral radius is the largest eigenvalue". -/
noncomputable def spectralRadius (G : Graphon) : ℝ := sSup {lam | IsEigenvalue G lam}

/-- Variant reading: spectral radius as the largest absolute value of an eigenvalue. -/
noncomputable def spectralRadiusAbs (G : Graphon) : ℝ := sSup {r | ∃ lam, IsEigenvalue G lam ∧ r = |lam|}

/-- "the half-graph graphon": `W(x,y) = 1` if `x + y ≤ 1`, else `0` (edge density `1/2`). -/
noncomputable def halfGraph : Graphon where
  W x y := if x + y ≤ 1 then 1 else 0
  meas := Measurable.ite (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
    measurable_const measurable_const
  symm x y := by simp [add_comm]
  nonneg x y := by split_ifs <;> norm_num
  le_one x y := by split_ifs <;> norm_num

/-- "the half graph, bipartite form": two halves `[0,1/2]` and `(1/2,1]`, with `x` in the first
half joined to `y` in the second half iff `x + 1/2 ≤ y` (edge density `1/4`). -/
noncomputable def halfGraphBip : Graphon where
  W x y := if (x ≤ 1/2 ∧ x + 1/2 ≤ y) ∨ (y ≤ 1/2 ∧ y + 1/2 ≤ x) then 1 else 0
  meas := Measurable.ite (MeasurableSet.union
      (MeasurableSet.inter (measurableSet_le measurable_fst measurable_const)
        (measurableSet_le (measurable_fst.add measurable_const) measurable_snd))
      (MeasurableSet.inter (measurableSet_le measurable_snd measurable_const)
        (measurableSet_le (measurable_snd.add measurable_const) measurable_fst)))
    measurable_const measurable_const
  symm x y := if_congr or_comm rfl rfl
  nonneg x y := by split_ifs <;> norm_num
  le_one x y := by split_ifs <;> norm_num

/-- "Among graphons of fixed edge density, ... the minimum [spectral radius is attained] only by
the half-graph graphon, unique up to zero-measure modification": for graphons `W` of the same
density as `H`, `W` minimizes `ρ` among graphons of that density iff `W = H` a.e. on `[0,1]^2`.
(`ρ` is a reading of "spectral radius".) -/
def MinPart (ρ : Graphon → ℝ) (H : Graphon) : Prop :=
  ∀ W : Graphon, density W = density H →
    ((∀ V : Graphon, density V = density H → ρ W ≤ ρ V) ↔
      ∀ᵐ p ∂(volume.restrict (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1)), W.W p.1 p.2 = H.W p.1 p.2)

/-- The conjecture is a conjunction (maximum part for the twin-clique graphon, and this minimum
part). Its maximum part is not formalized, since the minimum part alone is refuted. Here:
the minimum clause holds under some reading (two spectral-radius readings, two half-graph
conventions, density fixed to that of the half graph). -/
def Conjecture : Prop :=
  MinPart spectralRadius halfGraph ∨ MinPart spectralRadiusAbs halfGraph ∨
  MinPart spectralRadius halfGraphBip ∨ MinPart spectralRadiusAbs halfGraphBip

/-- What this package proves: the minimum clause fails under every one of those four readings. -/
def Claim : Prop := ¬ Conjecture

end C4391
-- STATEMENT END
