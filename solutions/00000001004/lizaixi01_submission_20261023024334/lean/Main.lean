import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace TLMC1004
open scoped LinearAlgebra.Projectivization
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
variable {K : Type*} [Field K]
abbrev Param (K : Type*) := Fin 4 → K
abbrev V (K : Type*) := Fin 7 → K
abbrev Point (K : Type*) [Field K] := Projectivization K (V K)

def quad (d x y : K) : K := x^2 - d*y^2

lemma quad_zero (d : K) (hd : ¬IsSquare d) (x y : K) (h : quad d x y = 0) :
    x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst y
    have hx : x^2 = 0 := by simpa [quad] using h
    have hx' : x*x=0 := by simpa [pow_two] using hx
    exact ⟨(mul_eq_zero.mp hx').elim id id, rfl⟩
  · exfalso
    apply hd
    refine ⟨x/y, ?_⟩
    dsimp [quad] at h
    field_simp
    linear_combination -h

lemma quad_mix (d a b x y s t : K) (hab : a+b=1) :
    quad d (a*x+b*s) (a*y+b*t) =
      a*quad d x y + b*quad d s t - a*b*quad d (x-s) (y-t) := by
  have hb : b=1-a := by linear_combination hab
  rw [hb]
  dsimp [quad]
  ring

def vec (d : K) (u : Param K) : V K := fun i =>
  match i.val with
  | 0 => 1
  | 1 => u 0
  | 2 => u 1
  | 3 => quad d (u 0) (u 1)
  | 4 => u 2
  | 5 => u 3
  | _ => quad d (u 2) (u 3)

lemma vec_ne_zero (d : K) (u : Param K) : vec d u ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [vec] at this

lemma vec_injective (d : K) : Function.Injective (vec d) := by
  intro u v h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  ext i
  fin_cases i
  · simpa [vec] using h1
  · simpa [vec] using h2
  · simpa [vec] using h4
  · simpa [vec] using h5

def point (d : K) (u : Param K) : Point K :=
  Projectivization.mk K (vec d u) (vec_ne_zero d u)

lemma point_injective (d : K) : Function.Injective (point d) := by
  intro u v h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  have h0 := congrFun ha 0
  have ha1 : (a : K)=1 := by simpa [vec,Pi.smul_apply,Units.smul_def] using h0
  apply vec_injective d
  simpa only [Units.smul_def,ha1,one_smul] using ha.symm

lemma combination (d : K) (hd : ¬IsSquare d) (u v w : Param K) (a b : K)
    (h : a • vec d u + b • vec d v = vec d w) :
    u=v ∨ w=u ∨ w=v := by
  have hab : a+b=1 := by simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 0
  by_cases ha : a=0
  · have hb : b=1 := by simpa [ha] using hab
    have he : vec d v=vec d w := by simpa [ha,hb] using h
    exact Or.inr (Or.inr (vec_injective d he).symm)
  by_cases hb : b=0
  · have ha1 : a=1 := by simpa [hb] using hab
    have he : vec d u=vec d w := by simpa [hb,ha1] using h
    exact Or.inr (Or.inl (vec_injective d he).symm)
  have h1 : a*u 0+b*v 0=w 0 := by simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 1
  have h2 : a*u 1+b*v 1=w 1 := by simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 2
  have h3 : a*quad d (u 0) (u 1)+b*quad d (v 0) (v 1)=quad d (w 0) (w 1) := by
    simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 3
  have h4 : a*u 2+b*v 2=w 2 := by simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 4
  have h5 : a*u 3+b*v 3=w 3 := by simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 5
  have h6 : a*quad d (u 2) (u 3)+b*quad d (v 2) (v 3)=quad d (w 2) (w 3) := by
    simpa [vec,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun h 6
  rw [←h1,←h2,quad_mix d a b _ _ _ _ hab] at h3
  rw [←h4,←h5,quad_mix d a b _ _ _ _ hab] at h6
  have hz1 : a*b*quad d (u 0-v 0) (u 1-v 1)=0 := by linear_combination h3
  have hz2 : a*b*quad d (u 2-v 2) (u 3-v 3)=0 := by linear_combination h6
  have hz1' := (mul_eq_zero.mp hz1).resolve_left (mul_ne_zero ha hb)
  have hz2' := (mul_eq_zero.mp hz2).resolve_left (mul_ne_zero ha hb)
  obtain ⟨hx0,hx1⟩ := quad_zero d hd _ _ hz1'
  obtain ⟨hx2,hx3⟩ := quad_zero d hd _ _ hz2'
  left
  ext i
  fin_cases i
  · exact sub_eq_zero.mp hx0
  · exact sub_eq_zero.mp hx1
  · exact sub_eq_zero.mp hx2
  · exact sub_eq_zero.mp hx3

/-- The standard cap condition: no three distinct points are collinear. -/
def IsCap (S : Finset (Point K)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p≠q → q≠r → r≠p →
    ¬Projectivization.IsCollinear ({p,q,r} : Set (Point K))

lemma no_collinear_three (d : K) (hd : ¬IsSquare d) (u v w : Param K)
    (huv : u≠v) (hvw : v≠w) (hwu : w≠u) :
    ¬Projectivization.IsCollinear ({point d u,point d v,point d w} : Set (Point K)) := by
  rintro ⟨M,hfin,hM,hsub⟩
  have hu : point d u ∈ M.submodule.projectivization := by simpa using hsub (by simp)
  have hv : point d v ∈ M.submodule.projectivization := by simpa using hsub (by simp)
  have hw : point d w ∈ M.submodule.projectivization := by simpa using hsub (by simp)
  have hne : point d u≠point d v := (point_injective d).ne huv
  have hi : LinearIndependent K ![vec d u,vec d v] := by
    apply (Projectivization.independent_mk_iff_LinearIndependent (vec_ne_zero d u) (vec_ne_zero d v)).mp
    exact (Projectivization.independent_pair_iff_ne _ _).mpr hne
  have hle : Submodule.span K {vec d u,vec d v} ≤ M.submodule := by
    apply Submodule.span_le.mpr
    intro z hz
    have hu' := (Submodule.mk_mem_projectivization_iff M.submodule (vec_ne_zero d u)).mp hu
    have hv' := (Submodule.mk_mem_projectivization_iff M.submodule (vec_ne_zero d v)).mp hv
    rcases hz with rfl | hz
    · exact hu'
    · have hz' := Set.mem_singleton_iff.mp hz
      subst z
      exact hv'
  have hspan : Module.finrank K (Submodule.span K {vec d u,vec d v})=2 := by
    rw [← Matrix.range_cons_cons_empty _ _ ![]]
    simpa using finrank_span_eq_card hi
  have htwo : Module.finrank K M.submodule=2 := by
    have hh := Submodule.finrank_mono hle
    rw [hspan] at hh
    omega
  have he := Projectivization.line_unique' (vec_ne_zero d u) (vec_ne_zero d v) hi M.submodule htwo hu hv
  have hw' := (Submodule.mk_mem_projectivization_iff M.submodule (vec_ne_zero d w)).mp hw
  rw [he] at hw'
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hw'
  rcases combination d hd u v w a b hab with h | h | h
  · exact huv h
  · exact hwu h
  · exact hvw h.symm

variable [Fintype K]
noncomputable instance : Fintype (Point K) := Fintype.ofFinite _

noncomputable def cap (d : K) : Finset (Point K) := by
  classical
  exact Finset.univ.image (point d)

lemma cap_card (d : K) : (cap d).card = Fintype.card K ^4 := by
  classical
  rw [cap,Finset.card_image_of_injective _ (point_injective d)]
  simp

lemma cap_isCap (d : K) (hd : ¬IsSquare d) : IsCap (cap d) := by
  classical
  rintro p hp q hq r hr hpq hqr hrp
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hr
  exact no_collinear_three d hd u v w (by intro h; exact hpq (congrArg (point d) h))
    (by intro h; exact hqr (congrArg (point d) h)) (by intro h; exact hrp (congrArg (point d) h))

lemma exists_max_cap : ∃ S : Finset (Point K), IsCap S ∧
    ∀ T : Finset (Point K), IsCap T → T.card ≤ S.card := by
  classical
  let candidates := (Finset.univ : Finset (Point K)).powerset.filter IsCap
  have he : candidates.Nonempty := ⟨∅,by simp [candidates,IsCap]⟩
  obtain ⟨S,hS,hmax⟩ := candidates.exists_max_image Finset.card he
  refine ⟨S,(Finset.mem_filter.mp hS).2,?_⟩
  intro T hT
  exact hmax T (by simp [candidates,hT])

noncomputable def maxCapSet : Finset (Point K) := Classical.choose (exists_max_cap (K:=K))
noncomputable def maxSize : ℕ := (maxCapSet (K:=K)).card

lemma maxCapSet_isCap : IsCap (maxCapSet (K:=K)) := (Classical.choose_spec (exists_max_cap (K:=K))).1
lemma card_le_maxSize (S : Finset (Point K)) (hS : IsCap S) : S.card ≤ maxSize (K:=K) :=
  (Classical.choose_spec (exists_max_cap (K:=K))).2 S hS

lemma q_four_le_maxSize (hodd : ringChar K ≠2) : Fintype.card K ^4 ≤ maxSize (K:=K) := by
  obtain ⟨d,hd⟩ := FiniteField.exists_nonsquare hodd
  rw [←cap_card d]
  exact card_le_maxSize (cap d) (cap_isCap d hd)

/-- Odd prime field sizes form an unbounded subfamily of the original prime powers. -/
abbrev OddPrime := {p : ℕ // p.Prime ∧ 3≤p}
instance : Nonempty OddPrime := ⟨⟨3,by decide⟩⟩

noncomputable def primeMax (p : OddPrime) : ℕ := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  exact maxSize (K:=ZMod p.val)

lemma prime_lower (p : OddPrime) : p.val^4 ≤ primeMax p := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  have hodd : ringChar (ZMod p.val)≠2 := by
    rw [ZMod.ringChar_zmod_n]
    have := p.property.2
    omega
  simpa [primeMax,ZMod.card] using (q_four_le_maxSize (K:=ZMod p.val) hodd)

lemma arbitrarily_large_violation (C : ℝ) (N : ℕ) :
    ∃ p : OddPrime, N≤p.val ∧
      2*(p.val:ℝ)^3+C*(p.val:ℝ)^2 < (primeMax p:ℝ) := by
  obtain ⟨m,hm⟩ := exists_nat_gt C
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (max N (m+4))
  have hN : N≤p := (le_max_left _ _).trans hpbound
  have hm4 : m+4≤p := (le_max_right _ _).trans hpbound
  have h3 : 3≤p := by omega
  let P : OddPrime := ⟨p,hp,h3⟩
  refine ⟨P,hN,?_⟩
  have hp4 : (m:ℝ)+4≤(p:ℝ) := by exact_mod_cast hm4
  have hp3 : (3:ℝ)≤p := by exact_mod_cast h3
  have hpositive : (0:ℝ)<p := by positivity
  have hpoly : 2*(p:ℝ)+C < (p:ℝ)^2 := by
    nlinarith [mul_nonneg (le_of_lt hpositive) (show (0:ℝ)≤p-3 by linarith)]
  have hmul := mul_lt_mul_of_pos_right hpoly (pow_pos hpositive 2)
  have hmax : (p:ℝ)^4 ≤ (primeMax P:ℝ) := by exact_mod_cast prime_lower P
  have hstrict : 2*(p:ℝ)^3+C*(p:ℝ)^2 < (p:ℝ)^4 := by
    nlinarith only [hmul]
  exact hstrict.trans_le hmax

open Filter Asymptotics

/-- The actual maximum, minus the proposed main term, is not even O(q^2). -/
theorem no_quadratic_error :
    ¬ (fun p : OddPrime => (primeMax p:ℝ)-2*(p.val:ℝ)^3) =O[atTop]
      (fun p : OddPrime => (p.val:ℝ)^2) := by
  intro h
  obtain ⟨C,hbound⟩ := h.bound
  obtain ⟨P0,hP0⟩ := Filter.eventually_atTop.mp hbound
  obtain ⟨P,hge,hgt⟩ := arbitrarily_large_violation C P0.val
  have hb := hP0 P hge
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (P.val:ℝ))] at hb
  have hu := (abs_le.mp hb).2
  linarith

/-- Direct negation of the n=6 expansion on the unbounded odd-prime subfamily. -/
theorem no_claimed_expansion :
    ¬ ∃ r : OddPrime → ℝ,
      r =O[atTop] (fun p : OddPrime => (p.val:ℝ)⁻¹) ∧
      ∀ᶠ p in atTop, (primeMax p:ℝ)=2*(p.val:ℝ)^3*(1+r p) := by
  rintro ⟨r,hr,heq⟩
  obtain ⟨C,hbound⟩ := hr.bound
  obtain ⟨P0,hP0⟩ := Filter.eventually_atTop.mp (hbound.and heq)
  obtain ⟨P,hge,hgt⟩ := arbitrarily_large_violation (2*C) P0.val
  obtain ⟨hb,he⟩ := hP0 P hge
  have hp : (0:ℝ)<P.val := by exact_mod_cast (show 0<P.val by have:=P.property.2;omega)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)] at hb
  have hu : r P≤C*(P.val:ℝ)⁻¹ := (le_abs_self _).trans hb
  have hm := mul_le_mul_of_nonneg_left hu (show (0:ℝ)≤2*(P.val:ℝ)^3 by positivity)
  have hc : 2*(P.val:ℝ)^3*(C*(P.val:ℝ)⁻¹)=2*C*(P.val:ℝ)^2 := by
    field_simp
  rw [hc] at hm
  nlinarith

end TLMC1004
