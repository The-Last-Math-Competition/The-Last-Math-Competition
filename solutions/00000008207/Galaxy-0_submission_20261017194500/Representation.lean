import Monoid
open Lean.Grind
namespace TLMC8207
abbrev Vec (K : Type) (n : Nat) := Fin n → K
def vzero {K : Type} [Field K] {n : Nat} : Vec K n := fun _ => 0
def vadd {K : Type} [Field K] {n : Nat} (v w : Vec K n) : Vec K n := fun i => v i + w i
def vscale {K : Type} [Field K] {n : Nat} (a : K) (v : Vec K n) : Vec K n := fun i => a * v i
def vsub {K : Type} [Field K] {n : Nat} (v w : Vec K n) : Vec K n := fun i => v i - w i
/-- A unital representation by actual linear operators on the coordinate vector space K^n. -/
structure Rep (K : Type) [Field K] (n : Nat) where
  act : M → Vec K n → Vec K n
  map_add : ∀ a v w, act a (vadd v w) = vadd (act a v) (act a w)
  map_scale : ∀ a c v, act a (vscale c v) = vscale c (act a v)
  map_unit : ∀ v, act unit v = v
  map_meet : ∀ a b v, act (meet a b) v = act a (act b v)

structure Subspace {K : Type} [Field K] {n : Nat} (S : Vec K n → Prop) : Prop where
  zero : S vzero
  add : ∀ v w, S v → S w → S (vadd v w)
  scale : ∀ c v, S v → S (vscale c v)
def Invariant {K : Type} [Field K] {n : Nat} (r : Rep K n) (S : Vec K n → Prop) : Prop :=
  ∀ a v, S v → S (r.act a v)
def Irreducible {K : Type} [Field K] {n : Nat} (r : Rep K n) : Prop :=
  0 < n ∧ ∀ S, Subspace S → Invariant r S →
    (∀ v, S v → v = vzero) ∨ (∀ v, S v)

section Representations
variable {K : Type} [Field K] {n : Nat}
theorem rep_zero (r : Rep K n) (a : M) : r.act a vzero = vzero := by
  have hv : vscale (0:K) (vzero : Vec K n) = vzero := by funext i; simp [vscale,vzero]; grind
  have h := r.map_scale a 0 vzero
  rw [hv] at h
  rw [h]
  funext i; simp [vscale,vzero]; grind

theorem rep_sub (r : Rep K n) (a : M) (v w : Vec K n) :
    r.act a (vsub v w) = vsub (r.act a v) (r.act a w) := by
  have hh (u z : Vec K n) : vsub u z = vadd u (vscale (-1:K) z) := by
    funext i; simp only [vsub,vadd,vscale]; grind
  rw [hh,r.map_add,r.map_scale,← hh]

theorem rep_idempotent (r : Rep K n) (a : M) (v : Vec K n) :
    r.act a (r.act a v) = r.act a v := by rw [← r.map_meet,meet_self]
theorem rep_commute (r : Rep K n) (a b : M) (v : Vec K n) :
    r.act a (r.act b v) = r.act b (r.act a v) := by
  rw [← r.map_meet,← r.map_meet,meet_comm]

theorem kernel_subspace (r : Rep K n) (a : M) :
    Subspace (fun v => r.act a v = vzero) := by
  constructor
  · exact rep_zero r a
  · intro v w hv hw
    rw [r.map_add,hv,hw]
    funext i; simp [vadd,vzero]; grind
  · intro c v hv
    rw [r.map_scale,hv]
    funext i; simp [vscale,vzero]; grind

theorem kernel_invariant (r : Rep K n) (a : M) :
    Invariant r (fun v => r.act a v = vzero) := by
  intro b v hv
  rw [rep_commute,hv,rep_zero]

/-- Central idempotents are either the zero operator or the identity on an irreducible representation. -/
theorem zero_or_identity (r : Rep K n) (hirr : Irreducible r) (a : M) :
    (∀ v, r.act a v = vzero) ∨ (∀ v, r.act a v = v) := by
  rcases hirr.2 (fun v => r.act a v = vzero) (kernel_subspace r a)
    (kernel_invariant r a) with h | h
  · right
    intro v
    have hk : r.act a (vsub (r.act a v) v) = vzero := by
      rw [rep_sub,rep_idempotent]
      funext i; simp [vsub,vzero]; grind
    have hz := h _ hk
    funext i
    have hc := congrFun hz i
    simp only [vsub,vzero] at hc
    grind
  · exact Or.inl h

def basis (i : Fin n) : Vec K n := fun j => if j = i then 1 else 0

theorem irreducible_dimension_one (r : Rep K n) (hirr : Irreducible r) : n = 1 := by
  have hn := hirr.1
  by_cases h : n = 1
  · exact h
  have hn2 : 2 ≤ n := by omega
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by intro e; have := congrArg Fin.val e; simp [i,j] at this
  let S : Vec K n → Prop := fun v => v i = 0
  have hS : Subspace S := by
    constructor
    · rfl
    · intro v w hv hw; change v i + w i = 0; grind
    · intro c v hv; change c * v i = 0; change v i = 0 at hv; grind
  have hiS : Invariant r S := by
    intro a v hv
    rcases zero_or_identity r hirr a with ha | ha
    · rw [ha]; rfl
    · rw [ha]; exact hv
  rcases hirr.2 S hS hiS with hzero | hall
  · have hv : S (basis j : Vec K n) := by
      change (if i = j then (1:K) else 0) = 0
      simp [hij]
    have hz := congrFun (hzero _ hv) j
    simp [basis,vzero] at hz
    grind
  · have hz := hall (basis i)
    change (if i = i then (1:K) else 0) = 0 at hz
    simp at hz
    grind

/-- The representation associated to a multiplicative scalar character. -/
def scalarRep (f : Character K) : Rep K 1 where
  act a v := vscale (f.val a) v
  map_add := by intro a v w; funext i; simp only [vscale,vadd]; grind
  map_scale := by intro a c v; funext i; simp only [vscale]; grind
  map_unit := by intro v; funext i; simp only [vscale,f.property.1]; grind
  map_meet := by intro a b v; funext i; simp only [vscale,f.property.2]; grind

def standardRep (t : M) : Rep K 1 := scalarRep (thresholdCharacter t)

theorem scalarRep_irreducible (f : Character K) : Irreducible (scalarRep f) := by
  constructor
  · decide
  · intro S hS _
    by_cases hzero : ∀ v, S v → v = vzero
    · exact Or.inl hzero
    · right
      have he : ∃ v, S v ∧ v ≠ vzero := by
        apply Classical.byContradiction; intro h
        apply hzero
        intro v hv
        apply Classical.byContradiction; intro hv0
        exact h ⟨v,hv,hv0⟩
      obtain ⟨v,hv,hv0⟩ := he
      have hval : v 0 ≠ 0 := by
        intro heq
        apply hv0; funext i
        have hi : i = 0 := by apply Fin.ext; omega
        subst i; exact heq
      intro w
      have hw : w = vscale (w 0 / v 0) v := by
        funext i
        have hi : i = 0 := by apply Fin.ext; omega
        subst i
        simp only [vscale]
        grind
      rw [hw]
      exact hS.scale _ _ hv

theorem one_coordinate (v : Vec K 1) : v = vscale (v 0) (basis 0) := by
  funext i
  have hi : i = 0 := by apply Fin.ext; omega
  subst i
  simp only [vscale,basis]
  grind

def repCharacter (r : Rep K 1) : Character K := by
  refine ⟨fun a => r.act a (basis 0) 0, ?_, ?_⟩
  · change r.act unit (basis 0) 0 = 1
    rw [r.map_unit]; rfl
  · intro a b
    change r.act (meet a b) (basis 0) 0 = r.act a (basis 0) 0 * r.act b (basis 0) 0
    rw [r.map_meet]
    have hb := one_coordinate (r.act b (basis 0))
    rw [hb,r.map_scale]
    simp only [vscale,basis]
    grind

theorem rep_one_scalar (r : Rep K 1) (a : M) (v : Vec K 1) :
    r.act a v = vscale ((repCharacter r).val a) v := by
  have hv := one_coordinate v
  have hb := one_coordinate (r.act a (basis 0))
  rw [hv,r.map_scale,hb]
  funext i
  simp only [vscale,repCharacter]
  grind

theorem Rep.ext {r s : Rep K n} (h : ∀ a v, r.act a v = s.act a v) : r = s := by
  cases r; cases s
  simp_all only
  congr
  funext a v
  exact h a v

theorem all_irreducibles_classified (r : Rep K n) (hirr : Irreducible r) :
    ∃ h : n = 1, ∃ t : M, h ▸ r = standardRep t := by
  have hn := irreducible_dimension_one r hirr
  subst n
  obtain ⟨t,ht⟩ := character_classification (repCharacter r)
  refine ⟨rfl,t,?_⟩
  apply Rep.ext
  intro a v
  rw [rep_one_scalar,ht]
  rfl
end Representations
end TLMC8207
