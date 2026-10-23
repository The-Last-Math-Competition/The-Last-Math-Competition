import Mathlib.Data.Stream.Init
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Clopen
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Finite
import Lean.Elab.Tactic.Omega

namespace TLMC1363
noncomputable section
abbrev Cantor := ℕ→Bool
abbrev Word := List Bool

def prepend (u : Word) (s : Cantor) : Cantor := Stream'.appendStream' u s
def cone (u : Word) : Set Cantor := Set.range (prepend u)
def cons (b : Bool) (s : Cantor) : Cantor := Stream'.cons b s
def tail (s : Cantor) : Cantor := fun n => s (n+1)

@[simp] theorem cons_zero (b : Bool) (s : Cantor) : cons b s 0=b := rfl
@[simp] theorem cons_succ (b : Bool) (s : Cantor) (n : ℕ) : cons b s (n+1)=s n := rfl
@[simp] theorem tail_cons (b : Bool) (s : Cantor) : tail (cons b s)=s := rfl
@[simp] theorem cons_tail (s : Cantor) : cons (s 0) (tail s)=s := by
  funext n; cases n <;> rfl

/-- Real transposition of two disjoint cones, with every outside point fixed. -/
def PrefixSwap (u v : Word) (f : Cantor ≃ₜ Cantor) : Prop :=
  Disjoint (cone u) (cone v) ∧
  (∀ s, f (prepend u s)=prepend v s) ∧
  (∀ s, f (prepend v s)=prepend u s) ∧
  (∀ s, s∉cone u → s∉cone v → f s=s)

theorem prefixSwap_involutive {u v : Word} {g : Cantor ≃ₜ Cantor}
    (h : PrefixSwap u v g) : Function.Involutive g := by
  classical
  intro s
  by_cases hu : s∈cone u
  · obtain ⟨t,rfl⟩ := hu
    rw [h.2.1,h.2.2.1]
  · by_cases hv : s∈cone v
    · obtain ⟨t,rfl⟩ := hv
      rw [h.2.2.1,h.2.1]
    · rw [h.2.2.2 s hu hv,h.2.2.2 s hu hv]

/-- Standard Cantor-space transposition-generated model of Thompson's V. -/
def thompsonV : Subgroup (Cantor ≃ₜ Cantor) :=
  Subgroup.closure {f | ∃ u v : Word, PrefixSwap u v f}

/-- The usual finite-generation definition, on actual subgroup closures. -/
def LocallyFinite (Γ : Type*) [Group Γ] : Prop :=
  ∀ s : Finset Γ, (Subgroup.closure (s : Set Γ) : Set Γ).Finite

theorem continuous_cons (b : Bool) {f : Cantor→Cantor} (hf : Continuous f) :
    Continuous (fun s => cons b (f s)) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact (continuous_apply n).comp hf

theorem continuous_tail : Continuous (tail : Cantor→Cantor) :=
  continuous_pi (fun n => continuous_apply (n+1))

theorem continuous_bool_if (i : ℕ) (b : Bool) {f g : Cantor→Cantor}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun s => if s i=b then f s else g s) := by
  have hc : IsClopen {s : Cantor | s i=b} :=
    (isClopen_discrete ({b} : Set Bool)).preimage (continuous_apply i)
  apply Continuous.if _ hf hg
  intro s hs
  rw [hc.frontier_eq] at hs
  exact False.elim hs

def swapA (s : Cantor) : Cantor :=
  if s 0=true then cons false (tail s) else cons true (tail s)
def swapB (s : Cantor) : Cantor :=
  if s 0=true then cons false (cons false (tail s))
  else if s 1=false then cons true (tail (tail s)) else s

@[simp] theorem swapA_cons (b : Bool) (s : Cantor) :
    swapA (cons b s)=cons (!b) s := by cases b <;> simp [swapA]
@[simp] theorem swapB_one (s : Cantor) :
    swapB (cons true s)=cons false (cons false s) := by simp [swapB]
@[simp] theorem swapB_zero_zero (s : Cantor) :
    swapB (cons false (cons false s))=cons true s := by simp [swapB]
@[simp] theorem swapB_zero_one (s : Cantor) :
    swapB (cons false (cons true s))=cons false (cons true s) := by simp [swapB]

theorem swapA_involutive : Function.Involutive swapA := by
  intro s
  have he := cons_tail s
  rw [←he,swapA_cons,swapA_cons]
  simp

theorem swapB_involutive : Function.Involutive swapB := by
  intro s
  cases h0 : s 0 with
  | true =>
    have he : s=cons true (tail s) := by rw [←h0]; exact (cons_tail s).symm
    rw [he,swapB_one,swapB_zero_zero]
  | false =>
    cases h1 : s 1 with
    | false =>
      have he : s=cons false (cons false (tail (tail s))) := by
        funext n; rcases n with _|(_|n) <;> simp [tail,h0,h1]
      rw [he,swapB_zero_zero,swapB_one]
    | true =>
      have he : s=cons false (cons true (tail (tail s))) := by
        funext n; rcases n with _|(_|n) <;> simp [tail,h0,h1]
      rw [he,swapB_zero_one,swapB_zero_one]

theorem continuous_swapA : Continuous swapA :=
  continuous_bool_if 0 true (continuous_cons false continuous_tail)
    (continuous_cons true continuous_tail)
theorem continuous_swapB : Continuous swapB :=
  continuous_bool_if 0 true
    (continuous_cons false (continuous_cons false continuous_tail))
    (continuous_bool_if 1 false (continuous_cons true (continuous_tail.comp continuous_tail))
      continuous_id)

def a : Cantor ≃ₜ Cantor where
  toFun := swapA
  invFun := swapA
  left_inv := swapA_involutive
  right_inv := swapA_involutive
  continuous_toFun := continuous_swapA
  continuous_invFun := continuous_swapA

def b : Cantor ≃ₜ Cantor where
  toFun := swapB
  invFun := swapB
  left_inv := swapB_involutive
  right_inv := swapB_involutive
  continuous_toFun := continuous_swapB
  continuous_invFun := continuous_swapB

theorem a_prefixSwap : PrefixSwap [false] [true] a := by
  refine ⟨?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro s ⟨u,hu⟩ ⟨v,hv⟩
    have h := congrFun (hu.trans hv.symm) 0
    simp [prepend,Stream'.appendStream',Stream'.cons] at h
  · intro s; exact swapA_cons false s
  · intro s; exact swapA_cons true s
  · intro s h0 h1
    cases hs : s 0 with
    | false => exact False.elim (h0 ⟨tail s,by simpa [prepend,Stream'.appendStream',cons,hs] using cons_tail s⟩)
    | true => exact False.elim (h1 ⟨tail s,by simpa [prepend,Stream'.appendStream',cons,hs] using cons_tail s⟩)

theorem b_prefixSwap : PrefixSwap [false,false] [true] b := by
  refine ⟨?_,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro s ⟨u,hu⟩ ⟨v,hv⟩
    have h := congrFun (hu.trans hv.symm) 0
    simp [prepend,Stream'.appendStream',Stream'.cons] at h
  · intro s; exact swapB_zero_zero s
  · intro s; exact swapB_one s
  · intro s h00 h1
    cases hs : s 0 with
    | true => exact False.elim (h1 ⟨tail s,by simpa [prepend,Stream'.appendStream',cons,hs] using cons_tail s⟩)
    | false =>
      cases ht : s 1 with
      | false =>
        apply False.elim
        apply h00
        refine ⟨tail (tail s),?_⟩
        funext n; rcases n with _|(_|n) <;> simp [prepend,Stream'.appendStream',Stream'.cons,tail,hs,ht]
      | true => change swapB s=s; simp [swapB,hs,ht]

theorem a_mem : a∈thompsonV := Subgroup.subset_closure ⟨_,_,a_prefixSwap⟩
theorem b_mem : b∈thompsonV := Subgroup.subset_closure ⟨_,_,b_prefixSwap⟩

def f : Cantor ≃ₜ Cantor := b*a
theorem f_mem : f∈thompsonV := thompsonV.mul_mem b_mem a_mem

theorem f_zero (s : Cantor) : f (cons false s)=cons false (cons false s) := by
  change swapB (swapA (cons false s))=_
  rw [swapA_cons,show (!false)=true from rfl,swapB_one]

/-- An actual orbit: n+1 initial zeros, followed by infinitely many ones. -/
def point (n : ℕ) : Cantor := fun i => decide (n + 1 ≤ i)

theorem point_cons (n : ℕ) : point (n+1)=cons false (point n) := by
  funext i; cases i with
  | zero => simp [point]
  | succ i => simp [point,cons_succ]

theorem f_point (n : ℕ) : f (point n)=point (n+1) := by
  cases n with
  | zero =>
    have hp : point 0=cons false (fun _ => true) := by
      funext i; cases i <;> simp [point]
    rw [hp,f_zero,←hp,←point_cons]
  | succ n => rw [point_cons,f_zero,←point_cons,←point_cons]

theorem power_orbit (n : ℕ) : (f^n) (point 0)=point n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change f ((f^n) (point 0))=_
    rw [ih,f_point]

theorem positive_power_ne_one (n : ℕ) (hn : 0<n) : f^n≠1 := by
  intro h
  have hh := congrArg (fun g : Cantor≃ₜCantor => g (point 0) 1) h
  rw [power_orbit] at hh
  have he : n=0 := by simpa [point] using hh
  omega

theorem f_infinite_order : ¬IsOfFinOrder f := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n,hn,he⟩
  exact positive_power_ne_one n hn he

def witness : thompsonV := ⟨f,f_mem⟩
def cyclicWitness : Subgroup thompsonV := Subgroup.closure ({witness} : Set thompsonV)

theorem cyclicWitness_single_generator :
    ∃ s : Finset thompsonV, s.card=1 ∧ Subgroup.closure (s : Set thompsonV)=cyclicWitness := by
  classical
  exact ⟨{witness},Finset.card_singleton _,by simp [cyclicWitness]⟩

theorem cyclicWitness_infinite : (cyclicWitness : Set thompsonV).Infinite := by
  intro hfin
  have : Finite cyclicWitness := hfin
  let x : cyclicWitness := ⟨witness,Subgroup.subset_closure (by simp)⟩
  obtain ⟨n,hn,he⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
  have h1 : witness^n=1 := congrArg Subtype.val he
  exact positive_power_ne_one n hn (congrArg Subtype.val h1)

theorem locallyFinite_torsion {Γ : Type*} [Group Γ] (h : LocallyFinite Γ) (g : Γ) :
    IsOfFinOrder g := by
  classical
  let H := Subgroup.closure ({g} : Set Γ)
  have hfin : (H : Set Γ).Finite := by simpa [H] using h {g}
  have : Finite H := hfin
  let x : H := ⟨g,Subgroup.subset_closure (by simp)⟩
  have hx := isOfFinOrder_of_finite x
  obtain ⟨n,hn,he⟩ := hx.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,by
    have hh := congrArg Subtype.val he
    exact hh⟩

theorem thompsonV_not_locallyFinite : ¬LocallyFinite thompsonV := by
  intro h
  let g : thompsonV := ⟨f,f_mem⟩
  have hg := locallyFinite_torsion h g
  obtain ⟨n,hn,he⟩ := hg.exists_pow_eq_one
  exact positive_power_ne_one n hn (congrArg Subtype.val he)

/-- No extra action/optimization requirements can restore the missing membership. -/
theorem no_qualified_candidate (P : Subgroup (Cantor≃ₜCantor)→Prop) :
    ¬(LocallyFinite thompsonV ∧ P thompsonV) := by
  intro h; exact thompsonV_not_locallyFinite h.1

end
end TLMC1363
