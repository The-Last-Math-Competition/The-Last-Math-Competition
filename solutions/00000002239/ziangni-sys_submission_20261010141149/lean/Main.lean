import Mathlib.Tactic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Filter
open scoped Topology Asymptotics

namespace FourSharedValues
noncomputable section

def F (z : ℂ) : ℂ := (Complex.exp z + 2) / (Complex.exp z + 3)
def G (z : ℂ) : ℂ := (1 + 2*Complex.exp z) / (1 + 3*Complex.exp z)
def target : Fin 4 → ℂ := ![2/3, 1, 3/4, 1/2]

theorem targets_distinct : Function.Injective target := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [target] at h ⊢

theorem meromorphic_F (z : ℂ) : MeromorphicAt F z := by
  unfold F
  exact (analyticAt_cexp.add analyticAt_const).meromorphicAt.div'
    (analyticAt_cexp.add analyticAt_const).meromorphicAt

theorem meromorphic_G (z : ℂ) : MeromorphicAt G z := by
  unfold G
  exact (analyticAt_const.add (analyticAt_const.mul analyticAt_cexp)).meromorphicAt.div'
    (analyticAt_const.add (analyticAt_const.mul analyticAt_cexp)).meromorphicAt

lemma fraction_eq (p q a : ℂ) (ha : a ≠ 0) : p/q=a ↔ p=a*q ∧ q≠0 := by
  by_cases hq : q=0
  · simp [hq, ha, Ne.symm ha]
  · rw [div_eq_iff hq]
    simp [hq]

theorem omitted_F_two_thirds (z : ℂ) : F z ≠ 2/3 := by
  intro h
  obtain ⟨he,_⟩ := (fraction_eq _ _ _ (by norm_num)).mp h
  have hz : Complex.exp z = 0 := by linear_combination 3*he
  exact Complex.exp_ne_zero z hz

theorem omitted_G_two_thirds (z : ℂ) : G z ≠ 2/3 := by
  intro h
  obtain ⟨he,_⟩ := (fraction_eq _ _ _ (by norm_num)).mp h
  have hf : (1 : ℂ)=0 := by linear_combination 3*he
  exact one_ne_zero hf

theorem omitted_F_one (z : ℂ) : F z ≠ 1 := by
  intro h
  obtain ⟨he,_⟩ := (fraction_eq _ _ _ (by norm_num)).mp h
  have hf : (1 : ℂ)=0 := by linear_combination -he
  exact one_ne_zero hf

theorem omitted_G_one (z : ℂ) : G z ≠ 1 := by
  intro h
  obtain ⟨he,_⟩ := (fraction_eq _ _ _ (by norm_num)).mp h
  have hz : Complex.exp z = 0 := by linear_combination -he
  exact Complex.exp_ne_zero z hz

theorem preimage_F_three_fourths (z : ℂ) : F z = 3/4 ↔ Complex.exp z=1 := by
  rw [F, fraction_eq _ _ _ (by norm_num)]
  constructor
  · rintro ⟨h,_⟩; linear_combination 4*h
  · intro h; norm_num [h]

theorem preimage_G_three_fourths (z : ℂ) : G z = 3/4 ↔ Complex.exp z=1 := by
  rw [G, fraction_eq _ _ _ (by norm_num)]
  constructor
  · rintro ⟨h,_⟩; linear_combination -4*h
  · intro h; norm_num [h]

theorem preimage_F_half (z : ℂ) : F z = 1/2 ↔ Complex.exp z = -1 := by
  rw [F, fraction_eq _ _ _ (by norm_num)]
  constructor
  · rintro ⟨h,_⟩; linear_combination 2*h
  · intro h; norm_num [h]

theorem preimage_G_half (z : ℂ) : G z = 1/2 ↔ Complex.exp z = -1 := by
  rw [G, fraction_eq _ _ _ (by norm_num)]
  constructor
  · rintro ⟨h,_⟩; linear_combination 2*h
  · intro h; norm_num [h]

/-- Equal finite-value preimages, with equal actual analytic vanishing orders at every preimage.
    At a pole neither function attains any of these nonzero finite target values. -/
def ShareCM (a : ℂ) : Prop := ∀ z : ℂ,
  (F z=a ↔ G z=a) ∧
  (F z=a → ∃ hF : AnalyticAt ℂ (fun w => F w-a) z,
    ∃ hG : AnalyticAt ℂ (fun w => G w-a) z, hF.order=hG.order)

lemma orders_equal_by_unit {f g u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hu : AnalyticAt ℂ u z)
    (hn : u z ≠ 0) (heq : (fun w => u w*g w) =ᶠ[𝓝 z] f) : hf.order=hg.order := by
  calc
    hf.order = (hu.mul hg).order := (hu.mul hg).order_congr heq
    _ = hu.order + hg.order := hu.order_mul hg
    _ = hg.order := by rw [hu.order_eq_zero_iff.mpr hn, zero_add]

lemma matching_orders (a c : ℂ) (z : ℂ)
    (hD : Complex.exp z+3 ≠ 0) (hE : 1+3*Complex.exp z ≠ 0) (hc : c≠0)
    (hid : ∀ u : ℂ, u+3≠0 → 1+3*u≠0 →
      c*((1+3*u)/(u+3))*((1+2*u)/(1+3*u)-a) = (u+2)/(u+3)-a) :
    ∃ hF : AnalyticAt ℂ (fun w => F w-a) z,
      ∃ hG : AnalyticAt ℂ (fun w => G w-a) z, hF.order=hG.order := by
  have hDAn : AnalyticAt ℂ (fun w => Complex.exp w+3) z :=
    analyticAt_cexp.add analyticAt_const
  have hEAn : AnalyticAt ℂ (fun w => 1+3*Complex.exp w) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_cexp)
  have hF : AnalyticAt ℂ (fun w => F w-a) z :=
    ((analyticAt_cexp.add analyticAt_const).div hDAn hD).sub analyticAt_const
  have hG : AnalyticAt ℂ (fun w => G w-a) z :=
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_cexp)).div hEAn hE).sub analyticAt_const
  refine ⟨hF,hG,?_⟩
  apply orders_equal_by_unit hF hG (analyticAt_const.mul (hEAn.div hDAn hD))
  · exact mul_ne_zero hc (div_ne_zero hE hD)
  · filter_upwards [hDAn.continuousAt.eventually_ne hD, hEAn.continuousAt.eventually_ne hE] with w hwD hwE
    exact hid (Complex.exp w) hwD hwE

theorem share_three_fourths : ShareCM (3/4) := by
  intro z
  refine ⟨(preimage_F_three_fourths z).trans (preimage_G_three_fourths z).symm, ?_⟩
  intro h
  have he := (preimage_F_three_fourths z).mp h
  apply matching_orders (3/4) (-1) z (by norm_num [he]) (by norm_num [he]) (by norm_num)
  intro u hd he
  field_simp
  <;> ring

theorem share_half : ShareCM (1/2) := by
  intro z
  refine ⟨(preimage_F_half z).trans (preimage_G_half z).symm, ?_⟩
  intro h
  have he := (preimage_F_half z).mp h
  apply matching_orders (1/2) 1 z (by norm_num [he]) (by norm_num [he]) (by norm_num)
  intro u hd he
  field_simp
  <;> ring

theorem all_four_shared_CM (i : Fin 4) : ShareCM (target i) := by
  fin_cases i
  · intro z
    refine ⟨by simp [target, omitted_F_two_thirds z, omitted_G_two_thirds z], ?_⟩
    intro h; exact (omitted_F_two_thirds z h).elim
  · intro z
    refine ⟨by simp [target, omitted_F_one z, omitted_G_one z], ?_⟩
    intro h; exact (omitted_F_one z h).elim
  · exact share_three_fourths
  · exact share_half

def witness : ℂ := Complex.log 2

theorem witness_exp : Complex.exp witness=2 := by
  exact Complex.exp_log (by norm_num)

theorem values_different : F witness=4/5 ∧ G witness=5/7 := by
  norm_num [F,G,witness_exp]

theorem functions_distinct : F≠G := by
  intro h
  have he := congrFun h witness
  rw [values_different.1, values_different.2] at he
  norm_num at he

/-- For a constant finite meromorphic function, N=0 and m=log^+ |a|. -/
def constantCharacteristic (a : ℂ) : ℝ := Real.log (max 1 ‖a‖)

theorem targets_characteristic_zero (i : Fin 4) : constantCharacteristic (target i)=0 := by
  fin_cases i <;> norm_num [constantCharacteristic,target,norm_div]

theorem targets_small (i : Fin 4) (T : ℝ → ℝ) :
    (fun _ : ℝ => constantCharacteristic (target i)) =o[atTop] T := by
  simp only [targets_characteristic_zero]
  exact Asymptotics.isLittleO_zero T atTop

theorem counterexample :
    (∀ z, MeromorphicAt F z ∧ MeromorphicAt G z) ∧ Function.Injective target ∧
    (∀ i, ShareCM (target i)) ∧ F≠G ∧
    (∀ i (T : ℝ → ℝ), (fun _ : ℝ => constantCharacteristic (target i)) =o[atTop] T) :=
  ⟨fun z => ⟨meromorphic_F z,meromorphic_G z⟩, targets_distinct, all_four_shared_CM,
    functions_distinct, targets_small⟩

#print axioms meromorphic_F
#print axioms meromorphic_G
#print axioms all_four_shared_CM
#print axioms functions_distinct
#print axioms targets_small
#print axioms counterexample
end
end FourSharedValues
