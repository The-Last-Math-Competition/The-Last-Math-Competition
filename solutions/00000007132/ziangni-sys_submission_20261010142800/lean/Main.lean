import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

noncomputable section
namespace SquareFaces
open Set
abbrev Plane := ℝ × ℝ

def square : Set Plane := {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1}
def horizontal : Set Plane := {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0}
def vertical : Set Plane := {p | p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1}

-- The actual Minkowski sum of its two generating coordinate segments.
theorem zonotope (p : Plane) : p ∈ square ↔
    ∃ h ∈ horizontal, ∃ v ∈ vertical, p = h + v := by
  constructor
  · intro hp
    exact ⟨(p.1,0), ⟨hp.1,hp.2.1,rfl⟩, (0,p.2), ⟨rfl,hp.2.2⟩, by ext <;> simp⟩
  · rintro ⟨h,hh,v,hv,rfl⟩
    rcases hh with ⟨a,b,c⟩
    rcases hv with ⟨d,e,f⟩
    simpa [square,c,d] using And.intro a (And.intro b (And.intro e f))

-- Standard exposed face: maximizers of the genuine linear functional ax+by.
def exposed (a b : ℝ) : Set Plane :=
  {p ∈ square | ∀ q ∈ square, a*q.1 + b*q.2 ≤ a*p.1 + b*p.2}

def faces (i : Fin 5) : Set Plane :=
  if i.val = 0 then {p ∈ square | p.1 = 1}
  else if i.val = 1 then {p ∈ square | p.1 = -1}
  else if i.val = 2 then {p ∈ square | p.2 = 1}
  else if i.val = 3 then {p ∈ square | p.2 = -1}
  else {(1,1)}

theorem face_witnesses (i : Fin 5) : ∃ a b : ℝ, faces i = exposed a b := by
  fin_cases i
  · refine ⟨1,0,?_⟩
    ext p
    simp only [faces, ↓reduceIte, exposed, mem_setOf_eq, one_mul, zero_mul, add_zero]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp,fun q hq => by rw [h]; exact hq.2.1⟩
    · rintro ⟨hp,h⟩
      have he := h (1,0) (by norm_num [square])
      exact ⟨hp,by dsimp at he; linarith [hp.2.1]⟩
  · refine ⟨-1,0,?_⟩
    ext p
    simp only [faces, ↓reduceIte, exposed, mem_setOf_eq, neg_one_mul, zero_mul, add_zero]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp,fun q hq => by rw [h]; linarith [hq.1]⟩
    · rintro ⟨hp,h⟩
      have he := h (-1,0) (by norm_num [square])
      exact ⟨hp,by dsimp at he; linarith [hp.1]⟩
  · refine ⟨0,1,?_⟩
    ext p
    simp only [faces, ↓reduceIte, exposed, mem_setOf_eq, one_mul, zero_mul, zero_add]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp,fun q hq => by rw [h]; exact hq.2.2.2⟩
    · rintro ⟨hp,h⟩
      have he := h (0,1) (by norm_num [square])
      exact ⟨hp,by dsimp at he; linarith [hp.2.2.2]⟩
  · refine ⟨0,-1,?_⟩
    ext p
    simp only [faces, ↓reduceIte, exposed, mem_setOf_eq, neg_one_mul, zero_mul, zero_add]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp,fun q hq => by rw [h]; linarith [hq.2.2.1]⟩
    · rintro ⟨hp,h⟩
      have he := h (0,-1) (by norm_num [square])
      exact ⟨hp,by dsimp at he; linarith [hp.2.2.1]⟩
  · refine ⟨1,1,?_⟩
    ext p
    simp only [faces, ↓reduceIte, exposed, mem_setOf_eq, mem_singleton_iff, one_mul]
    constructor
    · rintro rfl
      refine ⟨by norm_num [square],fun q hq => ?_⟩
      dsimp; linarith [hq.2.1,hq.2.2.2]
    · rintro ⟨hp,h⟩
      have he := h (1,1) (by norm_num [square])
      dsimp at he
      apply Prod.ext <;> dsimp <;> linarith [hp.2.1,hp.2.2.2]

theorem five_distinct : Function.Injective faces := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals first
    | have e := (Set.ext_iff.mp h) ((1,0):Plane); norm_num [faces,square,Fin.ext_iff] at e <;> contradiction
    | have e := (Set.ext_iff.mp h) ((-1,0):Plane); norm_num [faces,square,Fin.ext_iff] at e <;> contradiction
    | have e := (Set.ext_iff.mp h) ((0,1):Plane); norm_num [faces,square,Fin.ext_iff] at e <;> contradiction
    | have e := (Set.ext_iff.mp h) ((0,-1):Plane); norm_num [faces,square,Fin.ext_iff] at e <;> contradiction

theorem proper_nonempty (i : Fin 5) : (faces i).Nonempty ∧ faces i ⊂ square := by
  have hsub : faces i ⊆ square := by
    obtain ⟨a,b,h⟩ := face_witnesses i
    rw [h]
    exact fun p hp => hp.1
  have hn : ((0,0):Plane) ∉ faces i := by
    fin_cases i <;> norm_num [faces,square,Fin.ext_iff]
  have hne : faces i ≠ square := by
    intro h
    apply hn
    rw [h]
    norm_num [square]
  refine ⟨?_,ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩⟩
  fin_cases i
  · exact ⟨(1,0),by norm_num [faces,square,Fin.ext_iff]⟩
  · exact ⟨(-1,0),by norm_num [faces,square,Fin.ext_iff]⟩
  · exact ⟨(0,1),by norm_num [faces,square,Fin.ext_iff]⟩
  · exact ⟨(0,-1),by norm_num [faces,square,Fin.ext_iff]⟩
  · exact ⟨(1,1),by norm_num [faces,square,Fin.ext_iff]⟩

abbrev Chamber := Bool × Bool
def ray (b : Bool) : Set ℝ := if b then Ioi 0 else Iio 0
def region (s : Chamber) : Set Plane := ray s.1 ×ˢ ray s.2

theorem region_connected (s : Chamber) : IsConnected (region s) := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> simp only [region,ray, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact isConnected_Iio.prod isConnected_Iio
    | exact isConnected_Iio.prod isConnected_Ioi
    | exact isConnected_Ioi.prod isConnected_Iio
    | exact isConnected_Ioi.prod isConnected_Ioi

def complement : Set Plane := {p | p.1 ≠ 0 ∧ p.2 ≠ 0}

-- A connected subset of the hyperplane complement cannot cross an axis.
theorem coordinate_sign (S : Set Plane) (hS : IsPreconnected S)
    (hsub : S ⊆ complement) (f : Plane → ℝ) (hf : Continuous f)
    (hn : ∀ p ∈ S, f p ≠ 0) (a b : Plane) (ha : a ∈ S) (hb : b ∈ S)
    (hpos : 0 < f a) : 0 < f b := by
  by_contra h
  have hneg : f b < 0 := lt_of_le_of_ne (le_of_not_gt h) (hn b hb)
  have hz := hS.intermediate_value hb ha hf.continuousOn (show (0:ℝ) ∈ Icc (f b) (f a) from ⟨hneg.le,hpos.le⟩)
  obtain ⟨p,hp,hf0⟩ := hz
  exact hn p hp hf0

theorem four_regions : Fintype.card Chamber = 4 := by decide

theorem counterexample : Function.Injective faces ∧
    (∀ i, (faces i).Nonempty ∧ faces i ⊂ square ∧ ∃ a b, faces i = exposed a b) ∧
    Fintype.card Chamber = 4 ∧ ∀ s : Chamber, IsConnected (region s) := by
  refine ⟨five_distinct,?_,four_regions,region_connected⟩
  intro i
  exact ⟨(proper_nonempty i).1,(proper_nonempty i).2,face_witnesses i⟩

#print axioms zonotope
#print axioms face_witnesses
#print axioms five_distinct
#print axioms region_connected
#print axioms coordinate_sign
#print axioms counterexample
end SquareFaces
