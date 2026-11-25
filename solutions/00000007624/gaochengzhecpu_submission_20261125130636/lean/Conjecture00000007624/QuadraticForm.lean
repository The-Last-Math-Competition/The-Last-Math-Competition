/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Diagonal quadratic spaces `(Vec R g, quadForm g)`, polar bilinear forms, isotropic
(null) vectors, and the ordered-domain signature and inertia characterizations.
-/
import Conjecture00000007624.Algebra

namespace Conjecture00000007624

theorem eq_zero_of_neg_eq_zero {A : Type u} [AssocRing A] {a : A} (h : -a = 0) : a = 0 := by
  calc
    a = -(-a) := (neg_neg_eq a).symm
    _ = -(0 : A) := congrArg Neg.neg h
    _ = 0 := neg_zero_eq

/-- Coordinate module `R^n` indexed by a diagonal weight list `g : List R`. -/
def Vec (R : Type u) : List R → Type u
  | [] => PUnit.{u + 1}
  | _ :: gs => R × Vec R gs

section VecOps

variable {R : Type u} [CommRing R]

def vzero : (g : List R) → Vec R g
  | [] => PUnit.unit
  | _ :: gs => (0, vzero gs)

def vadd : {g : List R} → Vec R g → Vec R g → Vec R g
  | [], _, _ => PUnit.unit
  | _ :: _, (x, u), (y, w) => (x + y, vadd u w)

def vneg : {g : List R} → Vec R g → Vec R g
  | [], _ => PUnit.unit
  | _ :: _, (x, u) => (-x, vneg u)

def vsmul : {g : List R} → R → Vec R g → Vec R g
  | [], _, _ => PUnit.unit
  | _ :: _, a, (x, u) => (a * x, vsmul a u)

@[reducible] instance (g : List R) : OfNat (Vec R g) 0 := ⟨vzero g⟩
instance (g : List R) : Add (Vec R g) := ⟨vadd⟩
instance (g : List R) : Neg (Vec R g) := ⟨vneg⟩

theorem vsmul_zero_right : ∀ (g : List R) (a : R), vsmul a (0 : Vec R g) = 0
  | [], _ => rfl
  | _ :: gs, a => Prod.ext (mul_zero_eq a) (vsmul_zero_right gs a)

theorem vsmul_one_left : ∀ {g : List R} (v : Vec R g), vsmul (1 : R) v = v
  | [], PUnit.unit => rfl
  | _ :: _, (x, u) => Prod.ext (one_mul_eq x) (vsmul_one_left u)

theorem vsmul_mul : ∀ {g : List R} (a b : R) (v : Vec R g),
    vsmul (a * b) v = vsmul a (vsmul b v)
  | [], _, _, PUnit.unit => rfl
  | _ :: _, a, b, (x, u) => Prod.ext (AssocRing.mul_assoc a b x) (vsmul_mul a b u)

/-- Diagonal quadratic form `Q_g(v) = ∑_i g_i * v_i^2`. -/
def quadForm : (g : List R) → Vec R g → R
  | [], _ => 0
  | c :: gs, (x, v) => c * (x * x) + quadForm gs v

/-- Associated symmetric bilinear form `B_g(u, w) = ∑_i g_i * u_i * w_i`,
    satisfying `Q_g(u + w) = Q_g(u) + Q_g(w) + 2 * B_g(u, w)`. -/
def polarForm : (g : List R) → Vec R g → Vec R g → R
  | [], _, _ => 0
  | c :: gs, (x, u), (y, w) => c * (x * y) + polarForm gs u w

theorem quadForm_zero : ∀ (g : List R), quadForm g 0 = 0
  | [] => rfl
  | c :: gs => by
    change c * ((0 : R) * 0) + quadForm gs 0 = 0
    rw [mul_zero_eq, mul_zero_eq, quadForm_zero gs, zero_add_eq]

theorem polarForm_comm : ∀ {g : List R} (u w : Vec R g), polarForm g u w = polarForm g w u
  | [], _, _ => rfl
  | c :: _, (x, u), (y, w) => by
    change c * (x * y) + polarForm _ u w = c * (y * x) + polarForm _ w u
    rw [CommRing.mul_comm x y, polarForm_comm u w]

theorem polarization_identity : ∀ {g : List R} (u w : Vec R g),
    quadForm g (u + w) = (quadForm g u + quadForm g w) + (1 + 1) * polarForm g u w
  | [], _, _ => by
    change (0 : R) = (0 + 0) + (1 + 1) * 0
    rw [add_zero_eq, mul_zero_eq, add_zero_eq]
  | c :: gs, (x, u), (y, w) => by
    change c * ((x + y) * (x + y)) + quadForm gs (u + w) =
      ((c * (x * x) + quadForm gs u) + (c * (y * y) + quadForm gs w)) +
      (1 + 1) * (c * (x * y) + polarForm gs u w)
    rw [polarization_identity u w]
    have hsq_xy : (x + y) * (x + y) = (x * x + y * y) + (x * y + x * y) := by
      calc
        (x + y) * (x + y)
          = (x * x + x * y) + (y * x + y * y) := by
            rw [AssocRing.right_distrib x y (x + y), AssocRing.left_distrib x x y,
                AssocRing.left_distrib y x y]
        _ = (x * x + y * y) + (x * y + x * y) := by
            rw [CommRing.mul_comm y x, AssocRing.add_assoc (x * x) (x * y),
                ← AssocRing.add_assoc (x * y) (x * y) (y * y),
                AssocRing.add_comm (x * y + x * y) (y * y),
                ← AssocRing.add_assoc (x * x) (y * y)]
    have hxy : c * ((x + y) * (x + y)) =
        (c * (x * x) + c * (y * y)) + (1 + 1) * (c * (x * y)) := by
      rw [hsq_xy, AssocRing.left_distrib, AssocRing.left_distrib, AssocRing.left_distrib,
          AssocRing.right_distrib (1 : R) 1 (c * (x * y)), one_mul_eq]
    rw [hxy, AssocRing.left_distrib (1 + 1)]
    let A := c * (x * x)
    let B := c * (y * y)
    let C2 := (1 + 1 : R) * (c * (x * y))
    let D := quadForm gs u
    let E := quadForm gs w
    let F2 := (1 + 1 : R) * polarForm gs u w
    change ((A + B) + C2) + ((D + E) + F2) = ((A + D) + (B + E)) + (C2 + F2)
    calc
      ((A + B) + C2) + ((D + E) + F2)
        = (A + B) + (C2 + ((D + E) + F2)) := AssocRing.add_assoc _ _ _
      _ = (A + B) + ((C2 + (D + E)) + F2) := by rw [← AssocRing.add_assoc C2 (D + E) F2]
      _ = (A + B) + (((D + E) + C2) + F2) := by rw [AssocRing.add_comm C2 (D + E)]
      _ = (A + B) + ((D + E) + (C2 + F2)) := by rw [AssocRing.add_assoc (D + E) C2 F2]
      _ = ((A + B) + (D + E)) + (C2 + F2) := by rw [← AssocRing.add_assoc (A + B)]
      _ = (A + (B + (D + E))) + (C2 + F2) := by rw [AssocRing.add_assoc A B (D + E)]
      _ = (A + ((B + D) + E)) + (C2 + F2) := by rw [← AssocRing.add_assoc B D E]
      _ = (A + ((D + B) + E)) + (C2 + F2) := by rw [AssocRing.add_comm B D]
      _ = (A + (D + (B + E))) + (C2 + F2) := by rw [AssocRing.add_assoc D B E]
      _ = ((A + D) + (B + E)) + (C2 + F2) := by rw [← AssocRing.add_assoc A D (B + E)]

/-- A vector `v` is a (nonzero) isotropic / null vector if `v ≠ 0` and `Q_g(v) = 0`. -/
def IsIsotropic (g : List R) (v : Vec R g) : Prop :=
  v ≠ 0 ∧ quadForm g v = 0

/-- The quadratic space `(Vec R g, quadForm g)` admits a nonzero isotropic vector. -/
def HasIsotropic (g : List R) : Prop :=
  ∃ v : Vec R g, IsIsotropic g v

/-- Negated weight list `-g`, corresponding to switching sign convention `Q ↦ -Q`. -/
def negSig (g : List R) : List R := g.map (fun c => -c)

/-- Canonical coordinate identification between `Vec R g` and `Vec R (negSig g)`. -/
def toNegSig : {g : List R} → Vec R g → Vec R (negSig g)
  | [], PUnit.unit => PUnit.unit
  | _ :: _, (x, v) => (x, toNegSig v)

/-- Inverse coordinate identification from `Vec R (negSig g)` to `Vec R g`. -/
def fromNegSig : {g : List R} → Vec R (negSig g) → Vec R g
  | [], PUnit.unit => PUnit.unit
  | _ :: _, (x, u) => (x, fromNegSig u)

theorem toNegSig_fromNegSig : ∀ {g : List R} (u : Vec R (negSig g)),
    toNegSig (fromNegSig u) = u
  | [], PUnit.unit => rfl
  | _ :: _, (_, u) => Prod.ext rfl (toNegSig_fromNegSig u)

theorem toNegSig_zero : ∀ (g : List R), toNegSig (0 : Vec R g) = 0
  | [] => rfl
  | _ :: gs => Prod.ext rfl (toNegSig_zero gs)

theorem toNegSig_injective : ∀ {g : List R} {u w : Vec R g},
    toNegSig u = toNegSig w → u = w
  | [], PUnit.unit, PUnit.unit, _ => rfl
  | _ :: _, (_, _), (_, _), h => by
    injection h with hxy huv
    exact Prod.ext hxy (toNegSig_injective huv)

theorem quadForm_negSig : ∀ {g : List R} (v : Vec R g),
    quadForm (negSig g) (toNegSig v) = -(quadForm g v)
  | [], PUnit.unit => neg_zero_eq.symm
  | c :: gs, (x, v) => by
    change (-c) * (x * x) + quadForm (negSig gs) (toNegSig v) = -(c * (x * x) + quadForm gs v)
    rw [neg_mul_eq, quadForm_negSig v, neg_add_distrib]

theorem hasIsotropic_negSig_iff (g : List R) :
    HasIsotropic (negSig g) ↔ HasIsotropic g := by
  constructor
  · intro ⟨u, hu0, huq⟩
    refine ⟨fromNegSig u, ?_, ?_⟩
    · intro hf0
      apply hu0
      rw [← toNegSig_fromNegSig u, hf0, toNegSig_zero]
    · have hq := quadForm_negSig (fromNegSig u)
      rw [toNegSig_fromNegSig u, huq] at hq
      exact eq_zero_of_neg_eq_zero hq.symm
  · intro ⟨v, hv0, hvq⟩
    refine ⟨toNegSig v, ?_, ?_⟩
    · intro h0
      rw [← toNegSig_zero g] at h0
      exact hv0 (toNegSig_injective h0)
    · rw [quadForm_negSig, hvq, neg_zero_eq]

/-- Nondegenerate Sylvester signature weight list `(p, q)` with `p` ones and `q` minus-ones. -/
def sigList (R : Type u) [CommRing R] (p q : Nat) : List R :=
  List.replicate p 1 ++ List.replicate q (-1)

/-- General Sylvester inertia weight list `(p, q, r)` with `p` ones, `q` minus-ones, and `r` zeros. -/
def inertiaList (R : Type u) [CommRing R] (p q r : Nat) : List R :=
  List.replicate p 1 ++ List.replicate q (-1) ++ List.replicate r 0

end VecOps

section IntegralDomainVec

variable {R : Type u} [IntegralDomain R]

theorem vsmul_eq_zero_of_ne_zero : ∀ {g : List R} {a : R} {v : Vec R g},
    v ≠ 0 → vsmul a v = 0 → a = 0
  | [], _, PUnit.unit, hv, _ => False.elim (hv rfl)
  | _ :: _, a, (x, u), hv, hsm => by
    injection hsm with hax hau
    by_cases hx : x = 0
    · subst hx
      have hu : u ≠ 0 := fun hu0 => hv (Prod.ext rfl hu0)
      exact vsmul_eq_zero_of_ne_zero hu hau
    · cases IntegralDomain.mul_eq_zero a x hax with
      | inl ha => exact ha
      | inr hx0 => exact False.elim (hx hx0)

end IntegralDomainVec

section OrderedSignatureTheorems

variable {R : Type u} [OrderedDomain R]

private theorem pos_def_replicate_one : ∀ (p : Nat) (v : Vec R (List.replicate p 1)),
    OrderedDomain.NonNeg (quadForm (List.replicate p 1) v) ∧
    (quadForm (List.replicate p 1) v = 0 → v = 0)
  | 0, PUnit.unit => ⟨OrderedDomain.nonneg_zero, fun _ => rfl⟩
  | p + 1, (x, v) => by
    have ⟨hnn_v, hzero_v⟩ := pos_def_replicate_one p v
    have hq_eq : quadForm (List.replicate (p + 1) (1 : R)) (x, v) =
        x * x + quadForm (List.replicate p 1) v := by
      change (1 : R) * (x * x) + quadForm (List.replicate p 1) v = _
      rw [one_mul_eq]
    constructor
    · rw [hq_eq]
      exact OrderedDomain.nonneg_add (OrderedDomain.nonneg_sq x) hnn_v
    · intro hq0
      rw [hq_eq] at hq0
      have ⟨hx2, hvq⟩ := eq_zero_of_add_nonneg_eq_zero (OrderedDomain.nonneg_sq x) hnn_v hq0
      exact Prod.ext ((sq_eq_zero_iff x).mp hx2) (hzero_v hvq)

private theorem neg_def_replicate_neg_one : ∀ (q : Nat) (v : Vec R (List.replicate q (-1))),
    OrderedDomain.NonNeg (-(quadForm (List.replicate q (-1)) v)) ∧
    (quadForm (List.replicate q (-1)) v = 0 → v = 0)
  | 0, PUnit.unit => by
    refine ⟨?_, fun _ => rfl⟩
    change OrderedDomain.NonNeg (-(0 : R))
    rw [neg_zero_eq]
    exact OrderedDomain.nonneg_zero
  | q + 1, (x, v) => by
    have ⟨hnn_v, hzero_v⟩ := neg_def_replicate_neg_one q v
    have hneg_eq : -(quadForm (List.replicate (q + 1) (-1 : R)) (x, v)) =
        x * x + (-(quadForm (List.replicate q (-1)) v)) := by
      change -((-1 : R) * (x * x) + quadForm (List.replicate q (-1)) v) = _
      rw [neg_mul_eq, one_mul_eq, neg_add_distrib, neg_neg_eq]
    constructor
    · rw [hneg_eq]
      exact OrderedDomain.nonneg_add (OrderedDomain.nonneg_sq x) hnn_v
    · intro hq0
      have hneg0 : -(quadForm (List.replicate (q + 1) (-1 : R)) (x, v)) = 0 := by
        rw [hq0, neg_zero_eq]
      rw [hneg_eq] at hneg0
      have ⟨hx2, hvq⟩ := eq_zero_of_add_nonneg_eq_zero (OrderedDomain.nonneg_sq x) hnn_v hneg0
      exact Prod.ext ((sq_eq_zero_iff x).mp hx2) (hzero_v (eq_zero_of_neg_eq_zero hvq))

/-- Extend a vector `v : Vec R g1` by zeros onto `Vec R (g1 ++ g2)`. -/
def appendZeroRight : ∀ {g1 : List R} (g2 : List R), Vec R g1 → Vec R (g1 ++ g2)
  | [], g2, _ => vzero g2
  | _ :: _, g2, (x, v) => (x, appendZeroRight g2 v)

theorem appendZeroRight_ne_zero : ∀ {g1 : List R} (g2 : List R) {v : Vec R g1},
    v ≠ 0 → appendZeroRight g2 v ≠ 0
  | [], _, PUnit.unit, hv => False.elim (hv rfl)
  | _ :: _, g2, (x, v), hv => by
    intro h0
    injection h0 with hx0 hv0
    subst hx0
    have hv_ne : v ≠ 0 := fun h => hv (Prod.ext rfl h)
    exact appendZeroRight_ne_zero g2 hv_ne hv0

theorem quadForm_appendZeroRight : ∀ {g1 : List R} (g2 : List R) (v : Vec R g1),
    quadForm (g1 ++ g2) (appendZeroRight g2 v) = quadForm g1 v
  | [], g2, _ => by
    change quadForm g2 0 = 0
    exact quadForm_zero g2
  | c :: _, g2, (x, v) => by
    change c * (x * x) + quadForm (_ ++ g2) (appendZeroRight g2 v) = c * (x * x) + quadForm _ v
    rw [quadForm_appendZeroRight g2 v]

/-- Prepend zeros onto `v : Vec R g2` to obtain `Vec R (g1 ++ g2)`. -/
def prependZeroLeft : ∀ (g1 : List R) {g2 : List R}, Vec R g2 → Vec R (g1 ++ g2)
  | [], _, v => v
  | _ :: gs, _, v => (0, prependZeroLeft gs v)

theorem prependZeroLeft_ne_zero : ∀ (g1 : List R) {g2 : List R} {v : Vec R g2},
    v ≠ 0 → prependZeroLeft g1 v ≠ 0
  | [], _, _, hv => hv
  | _ :: gs, _, _, hv => by
    intro h0
    injection h0 with _ htl
    exact prependZeroLeft_ne_zero gs hv htl

theorem quadForm_prependZeroLeft : ∀ (g1 : List R) {g2 : List R} (v : Vec R g2),
    quadForm (g1 ++ g2) (prependZeroLeft g1 v) = quadForm g2 v
  | [], _, _ => rfl
  | c :: gs, _, v => by
    change c * ((0 : R) * 0) + quadForm (gs ++ _) (prependZeroLeft gs v) = quadForm _ v
    rw [mul_zero_eq, mul_zero_eq, zero_add_eq, quadForm_prependZeroLeft gs v]

/-- Construct an explicit nonzero isotropic vector `e_1 + e_{p+1}` in `sigList R p q`
    whenever `p ≥ 1` and `q ≥ 1`. -/
private def witnessIndefinite : ∀ (p q : Nat), p ≥ 1 → q ≥ 1 → Vec R (sigList R p q)
  | 0, _, hp, _ => False.elim (by omega)
  | _, 0, _, hq => False.elim (by omega)
  | 1, q + 1, _, _ =>
    (1, (1, vzero (List.replicate q (-1))))
  | p + 2, q + 1, _, hq =>
    (0, witnessIndefinite (p + 1) (q + 1) (by omega) hq)

private theorem witnessIndefinite_spec : ∀ (p q : Nat) (hp : p ≥ 1) (hq : q ≥ 1),
    IsIsotropic (sigList R p q) (witnessIndefinite p q hp hq)
  | 0, _, hp, _ => False.elim (by omega)
  | _, 0, _, hq => False.elim (by omega)
  | 1, q + 1, _, _ => by
    constructor
    · intro h0
      injection h0 with h10 _
      exact IntegralDomain.zero_ne_one h10.symm
    · change (1 : R) * (1 * 1) + ((-1 : R) * (1 * 1) + quadForm (List.replicate q (-1)) 0) = 0
      rw [quadForm_zero, add_zero_eq, one_mul_eq, one_mul_eq,
          neg_mul_eq, one_mul_eq, add_neg_cancel]
  | p + 2, q + 1, _, hq => by
    have ⟨hne, hqf⟩ := witnessIndefinite_spec (p + 1) (q + 1) (by omega) hq
    constructor
    · intro h0
      injection h0 with _ htl
      exact hne htl
    · change (1 : R) * ((0 : R) * 0) +
        quadForm (sigList R (p + 1) (q + 1)) (witnessIndefinite (p + 1) (q + 1) (by omega) hq) = 0
      rw [mul_zero_eq, mul_zero_eq, zero_add_eq, hqf]

/-- **Positive Signature Theorem (Sylvester Nondegenerate Canonical Form):**
    Over any ordered integral domain `R` (including `ℤ`, `ℚ`, and `ℝ`),
    the nondegenerate quadratic space of signature `(p, q)` admits a nonzero isotropic
    vector if and only if the signature is indefinite (`p ≥ 1 ∧ q ≥ 1`). -/
theorem hasIsotropic_sigList_iff (p q : Nat) :
    HasIsotropic (sigList R p q) ↔ (p ≥ 1 ∧ q ≥ 1) := by
  constructor
  · match p, q with
    | 0, q =>
      intro ⟨v, hv_ne, hv_q⟩
      exact False.elim (hv_ne ((neg_def_replicate_neg_one q v).2 hv_q))
    | p + 1, 0 =>
      unfold sigList
      rw [List.replicate_zero, List.append_nil]
      intro ⟨v, hv_ne, hv_q⟩
      exact False.elim (hv_ne ((pos_def_replicate_one (p + 1) v).2 hv_q))
    | p + 1, q + 1 =>
      intro _
      exact ⟨by omega, by omega⟩
  · intro ⟨hp, hq⟩
    exact ⟨witnessIndefinite p q hp hq, witnessIndefinite_spec p q hp hq⟩

/-- **General Inertia Theorem (Allowing Radical / Degeneracy `r`):**
    Over any ordered integral domain `R`, the canonical quadratic form of inertia `(p, q, r)`
    admits a nonzero isotropic vector if and only if `(p ≥ 1 ∧ q ≥ 1) ∨ r ≥ 1`. -/
theorem hasIsotropic_inertiaList_iff (p q r : Nat) :
    HasIsotropic (inertiaList R p q r) ↔ ((p ≥ 1 ∧ q ≥ 1) ∨ r ≥ 1) := by
  constructor
  · match r with
    | r' + 1 =>
      intro _
      exact Or.inr (by omega)
    | 0 =>
      unfold inertiaList
      rw [List.replicate_zero, List.append_nil]
      intro h
      exact Or.inl ((hasIsotropic_sigList_iff (R := R) p q).mp h)
  · intro h
    cases h with
    | inl hpq =>
      have ⟨u, hu_ne, hu_q⟩ := (hasIsotropic_sigList_iff (R := R) p q).mpr hpq
      refine ⟨appendZeroRight (List.replicate r 0) u,
        appendZeroRight_ne_zero _ hu_ne, ?_⟩
      unfold inertiaList
      change quadForm (sigList R p q ++ List.replicate r 0) _ = 0
      rw [quadForm_appendZeroRight, hu_q]
    | inr hr =>
      match r with
      | 0 => omega
      | r' + 1 =>
        let radVec : Vec R (List.replicate (r' + 1) (0 : R)) :=
          (1, vzero (List.replicate r' 0))
        have hrad_ne : radVec ≠ 0 := by
          intro h0
          injection h0 with h10 _
          exact IntegralDomain.zero_ne_one h10.symm
        have hrad_q : quadForm (List.replicate (r' + 1) (0 : R)) radVec = 0 := by
          change (0 : R) * (1 * 1) + quadForm (List.replicate r' 0) 0 = 0
          rw [zero_mul_eq, quadForm_zero, zero_add_eq]
        refine ⟨prependZeroLeft (sigList R p q) radVec,
          prependZeroLeft_ne_zero (sigList R p q) hrad_ne, ?_⟩
        unfold inertiaList
        change quadForm (sigList R p q ++ List.replicate (r' + 1) 0) _ = 0
        rw [quadForm_prependZeroLeft, hrad_q]

end OrderedSignatureTheorems

end Conjecture00000007624
