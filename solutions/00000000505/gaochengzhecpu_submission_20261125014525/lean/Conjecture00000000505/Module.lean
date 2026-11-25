import Conjecture00000000505.Ring

namespace Conjecture00000000505

/-- Left `R`-module structure over a commutative ring `R`. -/
class CAlgModule (R : Type u) [CAlgRing R] (M : Type v) where
  zero : M
  add : M → M → M
  neg : M → M
  smul : R → M → M
  add_assoc : ∀ x y z : M, add (add x y) z = add x (add y z)
  add_comm : ∀ x y : M, add x y = add y x
  zero_add : ∀ x : M, add zero x = x
  add_left_neg : ∀ x : M, add (neg x) x = zero
  one_smul : ∀ x : M, smul 1 x = x
  mul_smul : ∀ r s : R, ∀ x : M, smul (r * s) x = smul r (smul s x)
  smul_add : ∀ r : R, ∀ x y : M, smul r (add x y) = add (smul r x) (smul r y)
  add_smul : ∀ r s : R, ∀ x : M, smul (r + s) x = add (smul r x) (smul s x)

section ModuleLemmas
variable {R : Type u} [CAlgRing R] {M : Type v} [CAlgModule R M]

theorem m_add_left_cancel {x y z : M}
    (h : CAlgModule.add (R := R) x y = CAlgModule.add (R := R) x z) : y = z := by
  have h1 := congrArg (fun w => CAlgModule.add (R := R) (CAlgModule.neg (R := R) x) w) h
  dsimp only at h1
  rw [← CAlgModule.add_assoc (R := R), ← CAlgModule.add_assoc (R := R),
      CAlgModule.add_left_neg (R := R), CAlgModule.zero_add (R := R),
      CAlgModule.zero_add (R := R)] at h1
  exact h1

theorem m_add_zero (x : M) : CAlgModule.add (R := R) x (CAlgModule.zero (R := R)) = x := by
  rw [CAlgModule.add_comm (R := R), CAlgModule.zero_add (R := R)]

theorem m_add_right_neg (x : M) :
    CAlgModule.add (R := R) x (CAlgModule.neg (R := R) x) = CAlgModule.zero (R := R) := by
  rw [CAlgModule.add_comm (R := R), CAlgModule.add_left_neg (R := R)]

theorem m_zero_smul (x : M) :
    CAlgModule.smul (0 : R) x = CAlgModule.zero (R := R) := by
  apply m_add_left_cancel (R := R) (x := CAlgModule.smul (0 : R) x)
  rw [← CAlgModule.add_smul (R := R), r_add_zero, m_add_zero (R := R)]

theorem m_smul_zero (r : R) :
    CAlgModule.smul r (CAlgModule.zero (R := R) : M) = CAlgModule.zero (R := R) := by
  apply m_add_left_cancel (R := R) (x := CAlgModule.smul r (CAlgModule.zero (R := R)))
  rw [← CAlgModule.smul_add (R := R), m_add_zero (R := R), m_add_zero (R := R)]

theorem m_neg_smul (r : R) (x : M) :
    CAlgModule.smul (-r) x = CAlgModule.neg (R := R) (CAlgModule.smul r x) := by
  apply m_add_left_cancel (R := R) (x := CAlgModule.smul r x)
  rw [← CAlgModule.add_smul (R := R), r_add_right_neg, m_zero_smul (R := R),
      m_add_right_neg (R := R)]

end ModuleLemmas

/-- `R`-linear map between `R`-modules. -/
structure LinearMap (R : Type u) [CAlgRing R] (M : Type v) (N : Type w)
    [CAlgModule R M] [CAlgModule R N] where
  toFun : M → N
  map_add : ∀ x y : M, toFun (CAlgModule.add (R := R) x y) =
    CAlgModule.add (R := R) (toFun x) (toFun y)
  map_smul : ∀ r : R, ∀ x : M, toFun (CAlgModule.smul r x) =
    CAlgModule.smul r (toFun x)

theorem LinearMap.map_zero {R : Type u} [CAlgRing R] {M : Type v} {N : Type w}
    [CAlgModule R M] [CAlgModule R N] (f : LinearMap R M N) :
    f.toFun (CAlgModule.zero (R := R)) = CAlgModule.zero (R := R) := by
  have h := f.map_smul (0 : R) (CAlgModule.zero (R := R))
  rw [m_zero_smul (R := R), m_zero_smul (R := R)] at h
  exact h

def LinearMap.IsSurjective {R : Type u} [CAlgRing R] {M : Type v} {N : Type w}
    [CAlgModule R M] [CAlgModule R N] (f : LinearMap R M N) : Prop :=
  ∀ y : N, ∃ x : M, f.toFun x = y

/-- Kernel submodule `ker(f) ⊆ M` of an `R`-linear map `f : M → N`. -/
def KerMod {R : Type u} [CAlgRing R] {M : Type v} {N : Type w}
    [CAlgModule R M] [CAlgModule R N] (f : LinearMap R M N) : Type v :=
  { x : M // f.toFun x = CAlgModule.zero (R := R) }

instance {R : Type u} [CAlgRing R] {M : Type v} {N : Type w}
    [CAlgModule R M] [CAlgModule R N] (f : LinearMap R M N) :
    CAlgModule R (KerMod f) where
  zero := ⟨CAlgModule.zero (R := R), f.map_zero⟩
  add x y := ⟨CAlgModule.add (R := R) x.val y.val, by
    rw [f.map_add, x.property, y.property, m_add_zero (R := R)]⟩
  neg x := ⟨CAlgModule.neg (R := R) x.val, by
    have h : CAlgModule.neg (R := R) x.val = CAlgModule.smul (-1 : R) x.val := by
      rw [m_neg_smul (R := R), CAlgModule.one_smul (R := R)]
    rw [h, f.map_smul, x.property, m_smul_zero (R := R)]⟩
  smul r x := ⟨CAlgModule.smul r x.val, by
    rw [f.map_smul, x.property, m_smul_zero (R := R)]⟩
  add_assoc x y z := Subtype.ext (CAlgModule.add_assoc (R := R) x.val y.val z.val)
  add_comm x y := Subtype.ext (CAlgModule.add_comm (R := R) x.val y.val)
  zero_add x := Subtype.ext (CAlgModule.zero_add (R := R) x.val)
  add_left_neg x := Subtype.ext (CAlgModule.add_left_neg (R := R) x.val)
  one_smul x := Subtype.ext (CAlgModule.one_smul (R := R) x.val)
  mul_smul r s x := Subtype.ext (CAlgModule.mul_smul (R := R) r s x.val)
  smul_add r x y := Subtype.ext (CAlgModule.smul_add (R := R) r x.val y.val)
  add_smul r s x := Subtype.ext (CAlgModule.add_smul (R := R) r s x.val)

/-- Finite-rank free `R`-module `R^k`. -/
def FreeMod (R : Type u) (k : Nat) : Type u := Fin k → R

instance (R : Type u) [CAlgRing R] (k : Nat) : CAlgModule R (FreeMod R k) where
  zero := fun _ => 0
  add v w := fun i => v i + w i
  neg v := fun i => -(v i)
  smul r v := fun i => r * v i
  add_assoc x y z := funext (fun i => r_add_assoc (x i) (y i) (z i))
  add_comm x y := funext (fun i => r_add_comm (x i) (y i))
  zero_add x := funext (fun i => r_zero_add (x i))
  add_left_neg x := funext (fun i => r_add_left_neg (x i))
  one_smul x := funext (fun i => r_one_mul (x i))
  mul_smul r s x := funext (fun i => r_mul_assoc r s (x i))
  smul_add r x y := funext (fun i => r_left_distrib r (x i) (y i))
  add_smul r s x := funext (fun i => r_right_distrib r s (x i))

/-- A finitely generated `R`-module `M` is projective iff it is a direct summand of `R^k`. -/
def IsProjective (R : Type u) [CAlgRing R] (M : Type u) [CAlgModule R M] : Prop :=
  ∃ (k : Nat) (inc : LinearMap R M (FreeMod R k)) (proj : LinearMap R (FreeMod R k) M),
    ∀ x : M, proj.toFun (inc.toFun x) = x

theorem FreeMod.isProjective (R : Type u) [CAlgRing R] (k : Nat) :
    IsProjective R (FreeMod R k) :=
  ⟨k, ⟨id, fun _ _ => rfl, fun _ _ => rfl⟩, ⟨id, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

/-- Every projective module over an integral domain is torsion-free. -/
theorem IsProjective.torsion_free {R : Type u} [CAlgRing R] (hd : IsDomain R)
    {M : Type u} [CAlgModule R M] (hp : IsProjective R M)
    {r : R} {x : M} (hr : r ≠ 0)
    (hsmul : CAlgModule.smul r x = CAlgModule.zero (R := R)) :
    x = CAlgModule.zero (R := R) := by
  rcases hp with ⟨k, inc, proj, hret⟩
  have hinc0 : inc.toFun x = (fun _ : Fin k => (0 : R)) := by
    funext i
    have hi : r * (inc.toFun x i) = 0 := by
      have hmap := congrFun (inc.map_smul r x) i
      rw [hsmul, inc.map_zero] at hmap
      exact hmap.symm
    cases hd.mul_eq_zero hi with
    | inl h1 => exact False.elim (hr h1)
    | inr h2 => exact h2
  rw [← hret x, hinc0]
  exact proj.map_zero

/-- Inductive existence of a finite projective resolution of `M` over `R` of length `d`:
- length `0`: `M` is projective (`0 → P_0 ≅ M → 0`);
- length `d + 1`: there exists a short exact sequence `0 → ker(ε) → P_0 → M → 0` with `P_0`
  projective and `ker(ε)` admitting a projective resolution of length `d`. -/
def HasProjResolution (R : Type u) [CAlgRing R] :
    (M : Type u) → [CAlgModule R M] → Nat → Prop
  | M, _, 0 => IsProjective R M
  | M, _, d + 1 =>
    ∃ (P0 : Type u) (_ : CAlgModule R P0) (_ : IsProjective R P0)
      (eps : LinearMap R P0 M),
      eps.IsSurjective ∧ HasProjResolution R (KerMod eps) d

/-- Projective dimension `pd_R(M) = d`: `M` admits a projective resolution of length `d`
and no projective resolution of strictly smaller length. -/
def IsProjDim (R : Type u) [CAlgRing R] (M : Type u) [CAlgModule R M] (d : Nat) : Prop :=
  HasProjResolution R M d ∧ ∀ e : Nat, e < d → ¬ HasProjResolution R M e

/-- Ideal `I ⊆ R` viewed as an `R`-submodule of `R`. -/
def IdealMod (R : Type u) [CAlgRing R] (I : Ideal R) : Type u :=
  { x : R // x ∈ I }

instance (R : Type u) [CAlgRing R] (I : Ideal R) : CAlgModule R (IdealMod R I) where
  zero := ⟨0, I.zero_mem⟩
  add x y := ⟨x.val + y.val, I.add_mem x.property y.property⟩
  neg x := ⟨-x.val, I.neg_mem x.property⟩
  smul r x := ⟨r * x.val, I.mul_mem_left r x.property⟩
  add_assoc x y z := Subtype.ext (r_add_assoc x.val y.val z.val)
  add_comm x y := Subtype.ext (r_add_comm x.val y.val)
  zero_add x := Subtype.ext (r_zero_add x.val)
  add_left_neg x := Subtype.ext (r_add_left_neg x.val)
  one_smul x := Subtype.ext (r_one_mul x.val)
  mul_smul r s x := Subtype.ext (r_mul_assoc r s x.val)
  smul_add r x y := Subtype.ext (r_left_distrib r x.val y.val)
  add_smul r s x := Subtype.ext (r_right_distrib r s x.val)

/-- Quotient `R / I` constructed via `Quot` modulo `a - b ∈ I`, viewed as an `R`-module. -/
def IdealRel {R : Type u} [CAlgRing R] (I : Ideal R) (a b : R) : Prop :=
  a - b ∈ I

theorem IdealRel.refl {R : Type u} [CAlgRing R] (I : Ideal R) (a : R) : IdealRel I a a := by
  change a - a ∈ I
  rw [r_sub_self]
  exact I.zero_mem

theorem IdealRel.symm {R : Type u} [CAlgRing R] (I : Ideal R) {a b : R}
    (h : IdealRel I a b) : IdealRel I b a := by
  change b - a ∈ I
  have hneg : -(a - b) ∈ I := I.neg_mem h
  have heq : -(a - b) = b - a := by
    change -(a + (-b)) = b + (-a)
    rw [r_neg_add, r_neg_neg, r_add_comm]
  rw [← heq]
  exact hneg

theorem IdealRel.trans {R : Type u} [CAlgRing R] (I : Ideal R) {a b c : R}
    (h1 : IdealRel I a b) (h2 : IdealRel I b c) : IdealRel I a c := by
  change a - c ∈ I
  have hsum : (a - b) + (b - c) ∈ I := I.add_mem h1 h2
  have heq : (a - b) + (b - c) = a - c := by
    change (a + (-b)) + (b + (-c)) = a + (-c)
    calc
      (a + (-b)) + (b + (-c))
        = a + ((-b) + (b + (-c))) := by rw [r_add_assoc]
      _ = a + (((-b) + b) + (-c)) := by rw [← r_add_assoc (-b)]
      _ = a + ((0 : R) + (-c)) := by rw [r_add_left_neg]
      _ = a + (-c) := by rw [r_zero_add]
  rw [← heq]
  exact hsum

def QuotientMod (R : Type u) [CAlgRing R] (I : Ideal R) : Type u :=
  Quot (IdealRel I)

def QuotientMod.mk {R : Type u} [CAlgRing R] (I : Ideal R) (a : R) : QuotientMod R I :=
  Quot.mk (IdealRel I) a

theorem QuotientMod.eq_iff {R : Type u} [CAlgRing R] (I : Ideal R) (a b : R) :
    QuotientMod.mk I a = QuotientMod.mk I b ↔ a - b ∈ I := by
  constructor
  · intro h
    let motive : QuotientMod R I → Prop := fun q =>
      Quot.lift (fun x => IdealRel I a x)
        (fun x y hxy => propext ⟨fun hax => IdealRel.trans I hax hxy,
          fun hay => IdealRel.trans I hay (IdealRel.symm I hxy)⟩) q
    have ha : motive (QuotientMod.mk I a) := IdealRel.refl I a
    rw [h] at ha
    exact ha
  · intro h
    exact Quot.sound h

instance (R : Type u) [CAlgRing R] (I : Ideal R) : CAlgModule R (QuotientMod R I) where
  zero := QuotientMod.mk I 0
  add := fun q1 q2 => Quot.lift
    (fun a => Quot.lift (fun b => QuotientMod.mk I (a + b))
      (fun b1 b2 hb => Quot.sound (by
        change (a + b1) - (a + b2) ∈ I
        have heq : (a + b1) - (a + b2) = b1 - b2 := by
          change (a + b1) + (-(a + b2)) = b1 + (-b2)
          rw [r_neg_add]
          calc
            (a + b1) + ((-a) + (-b2))
              = b1 + (a + ((-a) + (-b2))) := by rw [r_add_comm a b1, r_add_assoc]
            _ = b1 + ((a + (-a)) + (-b2)) := by rw [← r_add_assoc a]
            _ = b1 + ((0 : R) + (-b2)) := by rw [r_add_right_neg]
            _ = b1 + (-b2) := by rw [r_zero_add]
        rw [heq]
        exact hb)) q2)
    (fun a1 a2 ha => Quot.inductionOn q2 (fun b => Quot.sound (by
      change (a1 + b) - (a2 + b) ∈ I
      have heq : (a1 + b) - (a2 + b) = a1 - a2 := by
        change (a1 + b) + (-(a2 + b)) = a1 + (-a2)
        rw [r_neg_add]
        calc
          (a1 + b) + ((-a2) + (-b))
            = a1 + (b + ((-b) + (-a2))) := by rw [r_add_comm (-a2) (-b), r_add_assoc]
          _ = a1 + ((b + (-b)) + (-a2)) := by rw [← r_add_assoc b]
          _ = a1 + ((0 : R) + (-a2)) := by rw [r_add_right_neg]
          _ = a1 + (-a2) := by rw [r_zero_add]
      rw [heq]
      exact ha))) q1
  neg := Quot.lift (fun a => QuotientMod.mk I (-a))
    (fun a b hab => Quot.sound (by
      change (-a) - (-b) ∈ I
      have heq : (-a) - (-b) = -(a - b) := by
        change (-a) + (-(-b)) = -(a + (-b))
        rw [r_neg_add]
      rw [heq]
      exact I.neg_mem hab))
  smul r := Quot.lift (fun a => QuotientMod.mk I (r * a))
    (fun a b hab => Quot.sound (by
      change r * a - r * b ∈ I
      rw [← r_mul_sub]
      exact I.mul_mem_left r hab))
  add_assoc := by
    intro x y z
    refine Quot.inductionOn x (fun a => Quot.inductionOn y (fun b => Quot.inductionOn z (fun c => ?_)))
    exact congrArg (QuotientMod.mk I) (r_add_assoc a b c)
  add_comm := by
    intro x y
    refine Quot.inductionOn x (fun a => Quot.inductionOn y (fun b => ?_))
    exact congrArg (QuotientMod.mk I) (r_add_comm a b)
  zero_add := by
    intro x
    refine Quot.inductionOn x (fun a => ?_)
    exact congrArg (QuotientMod.mk I) (r_zero_add a)
  add_left_neg := by
    intro x
    refine Quot.inductionOn x (fun a => ?_)
    exact congrArg (QuotientMod.mk I) (r_add_left_neg a)
  one_smul := by
    intro x
    refine Quot.inductionOn x (fun a => ?_)
    exact congrArg (QuotientMod.mk I) (r_one_mul a)
  mul_smul := by
    intro r s x
    refine Quot.inductionOn x (fun a => ?_)
    exact congrArg (QuotientMod.mk I) (r_mul_assoc r s a)
  smul_add := by
    intro r x y
    refine Quot.inductionOn x (fun a => Quot.inductionOn y (fun b => ?_))
    exact congrArg (QuotientMod.mk I) (r_left_distrib r a b)
  add_smul := by
    intro r s x
    refine Quot.inductionOn x (fun a => ?_)
    exact congrArg (QuotientMod.mk I) (r_right_distrib r s a)

end Conjecture00000000505
