import Representation
open Lean.Grind
namespace TLMC8207
/-- An actual two-sided linear isomorphism; both linearity laws are included. -/
structure LinearIso {K : Type} [Field K] (n m : Nat) where
  forward : Vec K n → Vec K m
  backward : Vec K m → Vec K n
  forward_add : ∀ v w, forward (vadd v w) = vadd (forward v) (forward w)
  forward_scale : ∀ c v, forward (vscale c v) = vscale c (forward v)
  backward_add : ∀ v w, backward (vadd v w) = vadd (backward v) (backward w)
  backward_scale : ∀ c v, backward (vscale c v) = vscale c (backward v)
  left_inv : ∀ v, backward (forward v) = v
  right_inv : ∀ v, forward (backward v) = v

structure RepIso {K : Type} [Field K] {n m : Nat} (r : Rep K n) (s : Rep K m)
    extends LinearIso (K := K) n m where
  intertwine : ∀ a v, forward (r.act a v) = s.act a (forward v)

section Equivalence
variable {K : Type} [Field K] {n m l : Nat}
def linearId (n : Nat) : LinearIso (K := K) n n where
  forward := id
  backward := id
  forward_add := by intros; rfl
  forward_scale := by intros; rfl
  backward_add := by intros; rfl
  backward_scale := by intros; rfl
  left_inv := by intros; rfl
  right_inv := by intros; rfl

def repIsoRefl (r : Rep K n) : RepIso r r where
  toLinearIso := linearId n
  intertwine := by intros; rfl

def repIsoSymm {r : Rep K n} {s : Rep K m} (e : RepIso r s) : RepIso s r where
  forward := e.backward
  backward := e.forward
  forward_add := e.backward_add
  forward_scale := e.backward_scale
  backward_add := e.forward_add
  backward_scale := e.forward_scale
  left_inv := e.right_inv
  right_inv := e.left_inv
  intertwine := by
    intro a v
    have h := congrArg e.backward (e.intertwine a (e.backward v))
    simpa only [e.left_inv,e.right_inv] using h.symm

def repIsoTrans {r : Rep K n} {s : Rep K m} {t : Rep K l}
    (e : RepIso r s) (f : RepIso s t) : RepIso r t where
  forward := fun v => f.forward (e.forward v)
  backward := fun v => e.backward (f.backward v)
  forward_add := by intros; rw [e.forward_add,f.forward_add]
  forward_scale := by intros; rw [e.forward_scale,f.forward_scale]
  backward_add := by intros; rw [f.backward_add,e.backward_add]
  backward_scale := by intros; rw [f.backward_scale,e.backward_scale]
  left_inv := by intro v; rw [f.left_inv,e.left_inv]
  right_inv := by intro v; rw [e.right_inv,f.right_inv]
  intertwine := by intro a v; rw [e.intertwine,f.intertwine]

theorem linear_forward_zero (e : LinearIso (K := K) n m) : e.forward vzero = vzero := by
  have h := e.forward_scale 0 (vzero : Vec K n)
  have hz : vscale (0:K) (vzero : Vec K n) = vzero := by
    funext i; simp only [vscale,vzero]; grind
  rw [hz] at h
  rw [h]; funext i; simp only [vscale,vzero]; grind

theorem linear_backward_zero (e : LinearIso (K := K) n m) : e.backward vzero = vzero := by
  have h := e.backward_scale 0 (vzero : Vec K m)
  have hz : vscale (0:K) (vzero : Vec K m) = vzero := by
    funext i; simp only [vscale,vzero]; grind
  rw [hz] at h
  rw [h]; funext i; simp only [vscale,vzero]; grind

theorem standard_inequivalent {s t : M}
    (e : RepIso (standardRep (K := K) s) (standardRep t)) : s = t := by
  have hnz : e.forward (basis 0) 0 ≠ 0 := by
    intro h
    have hz : e.forward (basis 0) = vzero := by
      funext i
      have hi : i = 0 := by apply Fin.ext; omega
      subst i; exact h
    have hh := congrArg e.backward hz
    rw [e.left_inv,linear_backward_zero e.toLinearIso] at hh
    have hh0 := congrFun hh 0
    change (1:K) = 0 at hh0
    grind
  apply threshold_injective (K := K)
  intro a
  have h := e.intertwine a (basis 0)
  change e.forward (vscale (threshold s a) (basis 0)) =
    vscale (threshold t a) (e.forward (basis 0)) at h
  rw [e.forward_scale] at h
  have hh := congrFun h 0
  simp only [vscale] at hh
  grind
end Equivalence

/-- Membership in the actual restriction fiber over the trivial 1-dimensional
representation of the unit group: a linear isomorphism intertwines each unit's
restricted action with the identity. -/
def RestrictsToTrivial {K : Type} [Field K] {n : Nat} (r : Rep K n) : Prop :=
  ∃ e : LinearIso (K := K) n 1, ∀ a, IsUnit a → ∀ v, e.forward (r.act a v) = e.forward v

theorem standard_restricts {K : Type} [Field K] (t : M) :
    RestrictsToTrivial (standardRep (K := K) t) := by
  refine ⟨linearId 1,?_⟩
  intro a ha v
  rw [(units_exact a).mp ha,(standardRep t).map_unit]

structure FiberRep (K : Type) [Field K] where
  dim : Nat
  rep : Rep K dim
  irreducible : Irreducible rep
  restriction : RestrictsToTrivial rep

namespace FiberRep
variable {K : Type} [Field K]
def standard (t : M) : FiberRep K where
  dim := 1
  rep := standardRep t
  irreducible := scalarRep_irreducible _
  restriction := standard_restricts t

theorem classification (r : FiberRep K) : ∃ t, r = standard t := by
  rcases r with ⟨n,r,hirr,hrestrict⟩
  obtain ⟨hn,t,ht⟩ := all_irreducibles_classified r hirr
  subst n
  change r = standardRep t at ht
  subst r
  exact ⟨t,rfl⟩

def equivalent (r s : FiberRep K) : Prop := Nonempty (RepIso r.rep s.rep)
instance representationSetoid : Setoid (FiberRep K) where
  r := equivalent
  iseqv := {
    refl := fun r => ⟨repIsoRefl r.rep⟩
    symm := fun ⟨e⟩ => ⟨repIsoSymm e⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨repIsoTrans e f⟩ }
end FiberRep

/-- The fiber consists of isomorphism classes, not labeled characters. -/
def RestrictionFiber (K : Type) [Field K] := Quotient (FiberRep.representationSetoid (K := K))
def fiberPoint {K : Type} [Field K] (t : M) : RestrictionFiber K :=
  Quotient.mk _ (FiberRep.standard t)

/-- Exact finite cardinality via a bijective enumeration. This does not assume
or bake in any classification of the elements being counted. -/
def HasCard (X : Type) (n : Nat) : Prop :=
  ∃ f : Fin n → X, (∀ i j, f i = f j → i = j) ∧ (∀ x, ∃ i, f i = x)

theorem nodup_length_le_of_subset {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hx : xs.Nodup) (hsub : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hx' := List.nodup_cons.mp hx
    have hmem : x ∈ ys := hsub (by simp)
    have hsub' : xs ⊆ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by intro h; subst y; exact hx'.1 hy
      exact (List.mem_erase_of_ne hne).mpr (hsub (by simp [hy]))
    have hlen := ih (ys.erase x) hx'.2 hsub'
    have hl := List.length_erase_of_mem hmem
    have hpos : 0 < ys.length := List.length_pos_of_mem hmem
    simp only [List.length_cons]
    omega

theorem finite_injection_bound {n m : Nat} (f : Fin n → Fin m)
    (hf : ∀ i j, f i = f j → i = j) : n ≤ m := by
  have hnodup : (List.ofFn f).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij he
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn] at he
    have h := congrArg Fin.val (hf ⟨i,hi⟩ ⟨j,hj⟩ he)
    simp only at h
    omega
  have hlen := nodup_length_le_of_subset (List.ofFn f) (List.finRange m) hnodup
    (fun {a} _ => List.mem_finRange a)
  simpa only [List.length_ofFn,List.length_finRange] using hlen

theorem card_unique {X : Type} {n m : Nat} (hn : HasCard X n) (hm : HasCard X m) : n = m := by
  obtain ⟨f,hfi,hfs⟩ := hn
  obtain ⟨g,hgi,hgs⟩ := hm
  have bound {a b : Nat} (u : Fin a → X) (v : Fin b → X)
      (hui : ∀ i j, u i = u j → i = j) (hvs : ∀ x, ∃ j, v j = x) : a ≤ b := by
    let p : Fin a → Fin b := fun i => Classical.choose (hvs (u i))
    have hp : ∀ i, v (p i) = u i := fun i => Classical.choose_spec (hvs (u i))
    apply finite_injection_bound p
    intro i j h
    apply hui i j
    rw [← hp i,← hp j,h]
  have hnm := bound f g hfi hgs
  have hmn := bound g f hgi hfs
  omega

section FiberCardinality
variable {K : Type} [Field K]
theorem fiberPoint_injective (s t : M) (h : fiberPoint (K := K) s = fiberPoint t) : s = t := by
  have he := Quotient.exact h
  obtain ⟨e⟩ := he
  exact standard_inequivalent e

theorem fiberPoint_surjective (q : RestrictionFiber K) : ∃ t, fiberPoint t = q := by
  refine Quotient.inductionOn q ?_
  intro r
  obtain ⟨t,ht⟩ := FiberRep.classification r
  subst r
  exact ⟨t,rfl⟩

theorem restriction_fiber_six : HasCard (RestrictionFiber K) 6 := by
  exact ⟨fiberPoint,fiberPoint_injective,fiberPoint_surjective⟩

theorem all_irreducibles_restrict (n : Nat) (r : Rep K n) (hirr : Irreducible r) :
    RestrictsToTrivial r := by
  obtain ⟨hn,t,ht⟩ := all_irreducibles_classified r hirr
  subst n
  change r = standardRep t at ht
  subst r
  exact standard_restricts t

end FiberCardinality

theorem six_not_power_two (k : Nat) : 6 ≠ 2^k := by
  by_cases h : k ≤ 2
  · have he : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases he with e | e | e <;> subst k <;> decide
  · have hk : 3 ≤ k := by omega
    have hh := Nat.pow_le_pow_right (n:=2) (by decide) hk
    change 8 ≤ 2^k at hh
    omega

/-- The claimed power-of-two law fails for the actual restriction fiber. -/
theorem conjecture8207_false {K : Type} [Field K] :
    ¬ ∃ k : Nat, HasCard (RestrictionFiber K) (2^k) := by
  rintro ⟨k,hk⟩
  exact six_not_power_two k (card_unique restriction_fiber_six hk)

/-- Alternative convention: representations send the monoid zero to zero. -/
def ZeroFiberRep (K : Type) [Field K] :=
  { r : FiberRep K // ∀ v, r.rep.act 0 v = vzero }

section Contracted
variable {K : Type} [Field K]
def positiveThreshold (t : Fin 5) : M := ⟨t.val+1,by omega⟩

theorem standard_zero_iff (t : M) :
    (∀ v, (standardRep (K := K) t).act 0 v = vzero) ↔ t.val ≠ 0 := by
  constructor
  · intro h ht
    have hh := congrFun (h (basis 0)) 0
    change (if t.val ≤ 0 then (1:K) else 0) * 1 = 0 at hh
    rw [ht] at hh
    simp at hh
    grind
  · intro ht v
    funext i
    change (if t.val ≤ 0 then (1:K) else 0) * v i = 0
    have hnot : ¬t.val ≤ 0 := by omega
    rw [if_neg hnot]
    grind

def zeroStandard (t : Fin 5) : ZeroFiberRep K :=
  ⟨FiberRep.standard (positiveThreshold t),
    (standard_zero_iff _).mpr (by simp [positiveThreshold])⟩

instance zeroRepresentationSetoid : Setoid (ZeroFiberRep K) where
  r := fun r s => FiberRep.equivalent r.val s.val
  iseqv := {
    refl := fun r => ⟨repIsoRefl r.val.rep⟩
    symm := fun ⟨e⟩ => ⟨repIsoSymm e⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨repIsoTrans e f⟩ }

def ZeroRestrictionFiber (K : Type) [Field K] := Quotient (zeroRepresentationSetoid (K := K))
def zeroFiberPoint (t : Fin 5) : ZeroRestrictionFiber K := Quotient.mk _ (zeroStandard t)

theorem zero_rep_classification (r : ZeroFiberRep K) : ∃ t : Fin 5, r = zeroStandard t := by
  obtain ⟨t,ht⟩ := FiberRep.classification r.val
  have hz : ∀ v, (standardRep (K := K) t).act 0 v = vzero := by
    have hh := r.property
    rw [ht] at hh
    exact hh
  have hpos := (standard_zero_iff t).mp hz
  let s : Fin 5 := ⟨t.val-1,by omega⟩
  have hst : positiveThreshold s = t := by
    apply Fin.ext
    simp only [positiveThreshold,s]
    omega
  refine ⟨s,?_⟩
  apply Subtype.ext
  change r.val = FiberRep.standard (positiveThreshold s)
  rw [hst,ht]

theorem zeroFiberPoint_injective (s t : Fin 5)
    (h : zeroFiberPoint (K := K) s = zeroFiberPoint t) : s = t := by
  obtain ⟨e⟩ := Quotient.exact h
  have hh := standard_inequivalent e
  have hv := congrArg Fin.val hh
  apply Fin.ext
  change s.val+1 = t.val+1 at hv
  omega

theorem zeroFiberPoint_surjective (q : ZeroRestrictionFiber K) : ∃ t, zeroFiberPoint t = q := by
  refine Quotient.inductionOn q ?_
  intro r
  obtain ⟨t,ht⟩ := zero_rep_classification r
  subst r
  exact ⟨t,rfl⟩

theorem zero_restriction_fiber_five : HasCard (ZeroRestrictionFiber K) 5 :=
  ⟨zeroFiberPoint,zeroFiberPoint_injective,zeroFiberPoint_surjective⟩
end Contracted

theorem five_not_power_two (k : Nat) : 5 ≠ 2^k := by
  by_cases h : k ≤ 2
  · have he : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases he with e | e | e <;> subst k <;> decide
  · have hk : 3 ≤ k := by omega
    have hh := Nat.pow_le_pow_right (n:=2) (by decide) hk
    change 8 ≤ 2^k at hh
    omega

theorem contracted_conjecture8207_false {K : Type} [Field K] :
    ¬ ∃ k : Nat, HasCard (ZeroRestrictionFiber K) (2^k) := by
  rintro ⟨k,hk⟩
  exact five_not_power_two k (card_unique zero_restriction_fiber_five hk)
end TLMC8207
