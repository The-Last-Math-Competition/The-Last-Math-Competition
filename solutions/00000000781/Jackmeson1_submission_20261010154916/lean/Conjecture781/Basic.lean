import Mathlib
import Conjecture781.Statement

/-! # Conjecture 00000000781: the closed-subgroup lattice of `1 + pℤ_p` and quotient lattices of `ℤ`

The conjecture (unit group subgroup lattice classification) says that the lattice of closed subgroups
of `1 + pℤ_p` is isomorphic to a quotient lattice of the integers.  The text does not restrict `p`
(no "odd" in either language), so the conjecture is read as holding for every prime `p`; we show
that it fails at `p = 2`: the closed subgroups of `1 + 2ℤ_2` contain a diamond `M₃`, hence the
lattice is not distributive, while every reading of "quotient lattice of the integers" listed in
`QuotientLatticeOfInt` is distributive. -/

-- (formal statement: see Statement.lean)

namespace C781

/-! ### Distributivity of every listed quotient -/

lemma distrib_of_surj {S L : Type*} [Lattice S] [Lattice L]
    (hS : ∀ x y z : S, x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z) (f : LatticeHom S L)
    (hf : Function.Surjective f) : ∀ a b c : L, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by
  intro a b c
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  obtain ⟨z, rfl⟩ := hf c
  simpa [map_inf, map_sup] using OrderHomClass.mono f (hS x y z)

lemma dual_distrib {S : Type*} [Lattice S] (hS : ∀ x y z : S, x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z) :
    ∀ x y z : Sᵒᵈ, x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z := by
  letI : DistribLattice S := DistribLattice.ofInfSupLe hS
  intro x y z
  exact le_of_eq (inf_sup_left x y z)

lemma chain_distrib (x y z : ℤ) : x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z :=
  le_of_eq (inf_sup_left x y z)

lemma cyc (H : AddSubgroup ℤ) : ∃ n : ℕ, H = AddSubgroup.zmultiples (n : ℤ) := by
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal (AddSubgroup.toIntSubmodule H))
  refine ⟨g.natAbs, ?_⟩
  have h2 : H = AddSubgroup.zmultiples g := by
    ext x
    have h3 : x ∈ AddSubgroup.toIntSubmodule H ↔ x ∈ Submodule.span ℤ {g} := by rw [hg]
    rw [AddSubgroup.mem_zmultiples_iff]
    simp only [Submodule.mem_span_singleton] at h3
    exact h3
  rw [h2]
  simp

theorem gcd_lcm_key (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) (Nat.lcm a c) = Nat.lcm a (Nat.gcd b c) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have hb' := hb.ne'; have hc' := hc.ne'; have ha' := ha.ne'
  apply Nat.eq_of_factorization_eq
  · exact Nat.gcd_ne_zero_left (Nat.lcm_ne_zero ha' hb')
  · exact Nat.lcm_ne_zero ha' (Nat.gcd_ne_zero_left hb')
  intro p
  rw [Nat.factorization_gcd (Nat.lcm_ne_zero ha' hb') (Nat.lcm_ne_zero ha' hc'),
    Nat.factorization_lcm ha' (Nat.gcd_ne_zero_left hb'), Nat.factorization_gcd hb' hc',
    Nat.factorization_lcm ha' hb', Nat.factorization_lcm ha' hc']
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

lemma subZ_distrib (x y z : AddSubgroup ℤ) : x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z := by
  obtain ⟨a, rfl⟩ := cyc x
  obtain ⟨b, rfl⟩ := cyc y
  obtain ⟨c, rfl⟩ := cyc z
  rw [Int.zmultiples_sup, Int.zmultiples_inf, Int.zmultiples_inf, Int.zmultiples_inf,
    Int.zmultiples_sup]
  refine le_of_eq ?_
  simp only [Int.gcd_natCast_natCast, Int.lcm_natCast_natCast, gcd_lcm_key]

lemma subZMod_distrib (n : ℕ) (x y z : AddSubgroup (ZMod n)) :
    x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z := by
  have hs : Function.Surjective (Int.castAddHom (ZMod n)) := ZMod.intCast_surjective
  have hr : (Int.castAddHom (ZMod n)).range = ⊤ := AddMonoidHom.range_eq_top.mpr hs
  have hsup : ∀ u v : AddSubgroup (ZMod n), (u ⊔ v).comap (Int.castAddHom (ZMod n)) =
      u.comap (Int.castAddHom (ZMod n)) ⊔ v.comap (Int.castAddHom (ZMod n)) := fun u v =>
    (AddSubgroup.comap_sup_eq_of_le_range (Int.castAddHom (ZMod n)) (H := u) (K := v)
      (le_of_le_of_eq le_top hr.symm) (le_of_le_of_eq le_top hr.symm)).symm
  rw [← AddSubgroup.comap_le_comap_of_surjective hs]
  have := subZ_distrib (x.comap (Int.castAddHom (ZMod n))) (y.comap (Int.castAddHom (ZMod n)))
    (z.comap (Int.castAddHom (ZMod n)))
  rwa [← AddSubgroup.comap_inf, ← AddSubgroup.comap_inf, ← hsup, ← hsup, ← AddSubgroup.comap_inf]
    at this

lemma quotient_distrib (L : Type) [Lattice L] (h : QuotientLatticeOfInt L) :
    ∀ a b c : L, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by
  rcases h with ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨n, ⟨g⟩⟩
  · exact distrib_of_surj chain_distrib f hf
  · exact distrib_of_surj subZ_distrib f hf
  · exact distrib_of_surj (dual_distrib subZ_distrib) f hf
  · intro a b c
    obtain ⟨x, rfl⟩ := g.surjective a
    obtain ⟨y, rfl⟩ := g.surjective b
    obtain ⟨z, rfl⟩ := g.surjective c
    simpa [g.map_inf, g.map_sup] using g.monotone (subZMod_distrib n x y z)

/-! ### The diamond in the closed subgroups of `1 + 2ℤ_2` -/

/-- Reduction modulo `8`. -/
noncomputable def pi8 : ℤ_[2] →+* ZMod (2 ^ 3) := PadicInt.toZModPow 3

lemma pi8_cont : Continuous pi8 := by
  rw [continuous_def]
  intro s _
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(1 / 8 : ℝ), by norm_num, fun y hy => ?_⟩
  have h : pi8 (y - x) = 0 := by
    have : y - x ∈ RingHom.ker pi8 := by
      rw [pi8, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have : ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) = 1 / 8 := by norm_num
      rw [this]; exact hy.le
    exact this
  rw [map_sub, sub_eq_zero] at h
  show pi8 y ∈ s
  rw [h]; exact hx

/-- The residue mod `8` of an element of `1 + 2ℤ_2`. -/
noncomputable def res (u : ↥(U1 2)) : ZMod (2 ^ 3) := pi8 ((u : ℤ_[2]ˣ) : ℤ_[2])

lemma res_cont : Continuous res :=
  pi8_cont.comp (Units.continuous_val.comp continuous_subtype_val)

lemma res_mul (u v : ↥(U1 2)) : res (u * v) = res u * res v := by simp [res]

lemma res_one : res (1 : ↥(U1 2)) = 1 := by simp [res]

lemma res_inv (u : ↥(U1 2)) : res u * res u⁻¹ = 1 := by rw [← res_mul]; simp [res_one]

lemma res_odd (u : ↥(U1 2)) : ∃ s : ZMod (2 ^ 3), res u = 1 + 2 * s := by
  obtain ⟨w, hw⟩ := u.2
  refine ⟨pi8 w, ?_⟩
  have : ((u : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 * w := by
    have : ((u : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 * w := by simpa using hw
    linear_combination this
  have h2 : pi8 2 = 2 := map_ofNat pi8 2
  simp [res, this, map_add, map_mul, h2]

lemma odd_cases : ∀ s : ZMod (2 ^ 3), (1 + 2 * s = 1 ∨ 1 + 2 * s = 3 ∨ 1 + 2 * s = 5 ∨ 1 + 2 * s = 7) := by
  decide

/-- The closed subgroup `{u | u ≡ 1 or u ≡ a mod 8}` for `a² = 1` in `ℤ/8`. -/
noncomputable def Hres (a : ZMod (2 ^ 3)) (ha : a * a = 1) : ClosedSubgroup ↥(U1 2) where
  toSubgroup :=
  { carrier := {u | res u = 1 ∨ res u = a}
    mul_mem' := by
      intro u v hu hv
      simp only [Set.mem_setOf_eq, res_mul] at *
      rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv, ha]
    one_mem' := by simp [res_one]
    inv_mem' := by
      intro u hu
      have h := res_inv u
      simp only [Set.mem_setOf_eq] at *
      rcases hu with hu | hu
      · rw [hu] at h; left; simpa using h
      · rw [hu] at h; right
        calc res u⁻¹ = a * (a * res u⁻¹) := by rw [← mul_assoc, ha, one_mul]
          _ = a := by rw [h, mul_one] }
  isClosed' := by
    have : ({u : ↥(U1 2) | res u = 1 ∨ res u = a} : Set ↥(U1 2)) = res ⁻¹' {1, a} := by
      ext u; simp
    show IsClosed {u : ↥(U1 2) | res u = 1 ∨ res u = a}
    rw [this]
    haveI : DiscreteTopology (ZMod (2 ^ 3)) := ⟨rfl⟩
    exact (Set.toFinite _).isClosed.preimage res_cont

lemma mem_Hres (a : ZMod (2 ^ 3)) (ha : a * a = 1) (u : ↥(U1 2)) :
    u ∈ Hres a ha ↔ res u = 1 ∨ res u = a := Iff.rfl

lemma h7 : (7 : ZMod (2 ^ 3)) * 7 = 1 := by decide
lemma h3 : (3 : ZMod (2 ^ 3)) * 3 = 1 := by decide
lemma h5 : (5 : ZMod (2 ^ 3)) * 5 = 1 := by decide

/-- The whole group as a closed subgroup. -/
noncomputable def Top : ClosedSubgroup ↥(U1 2) :=
  ⟨⊤, by show IsClosed (Set.univ : Set ↥(U1 2)); exact isClosed_univ⟩

/-- The element `-1` of `1 + 2ℤ_2`. -/
noncomputable def m1 : ↥(U1 2) :=
  ⟨-1, by
    show ((2 : ℕ) : ℤ_[2]) ∣ (((-1 : ℤ_[2]ˣ)) : ℤ_[2]) - 1
    exact ⟨-1, by simp; ring⟩⟩

lemma res_m1 : res m1 = 7 := by
  simp [res, m1, pi8]
  decide +revert

lemma m1_mul : m1 * m1 = 1 := by
  apply Subtype.ext; apply Units.ext; simp [m1]

lemma top_of (a : ZMod (2 ^ 3)) (ha : a * a = 1) (ha' : a = 3 ∨ a = 5)
    (X : ClosedSubgroup ↥(U1 2)) (hX7 : Hres 7 h7 ≤ X) (hXa : Hres a ha ≤ X) (u : ↥(U1 2)) :
    u ∈ X := by
  have hm : m1 ∈ X := hX7 ((mem_Hres _ _ _).2 (Or.inr res_m1))
  obtain ⟨s, hs⟩ := res_odd u
  have hcase := odd_cases s
  rw [← hs] at hcase
  by_cases hu : res u = 1 ∨ res u = 7
  · exact hX7 ((mem_Hres _ _ _).2 hu)
  by_cases hua : res u = a
  · exact hXa ((mem_Hres _ _ _).2 (Or.inr hua))
  have hmu : m1 * u ∈ X := by
    apply hXa
    rw [mem_Hres]; right
    rw [res_mul, res_m1]
    have key : ∀ a b : ZMod (2 ^ 3), (a = 3 ∨ a = 5) → (b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7) →
        ¬ (b = 1 ∨ b = 7) → b ≠ a → 7 * b = a := by decide
    exact key a _ ha' hcase hu hua
  have : u = m1⁻¹ * (m1 * u) := by simp
  rw [this]
  exact X.mul_mem (X.inv_mem hm) hmu

lemma isLUB_pair (a : ZMod (2 ^ 3)) (ha : a * a = 1) (ha' : a = 3 ∨ a = 5) :
    IsLUB {Hres 7 h7, Hres a ha} Top := by
  constructor
  · intro X hX u _
    exact trivial
  · intro X hX u _
    exact top_of a ha ha' X (hX (by simp)) (hX (by simp)) u

lemma isGLB_pair (a : ZMod (2 ^ 3)) (ha : a * a = 1) (ha' : a = 3 ∨ a = 5) :
    IsGLB {Hres 7 h7, Hres a ha} (Hres 1 (by decide)) := by
  constructor
  · intro X hX u hu
    have hu' : res u = 1 := by simpa [mem_Hres] using hu
    rcases hX with rfl | rfl <;> exact (mem_Hres _ _ _).2 (Or.inl hu')
  · intro X hX u hu
    have h1 := (mem_Hres _ _ _).1 (hX (by simp : Hres 7 h7 ∈ _) hu)
    have h2 := (mem_Hres _ _ _).1 (hX (by simp : Hres a ha ∈ _) hu)
    have key : ∀ a r : ZMod (2 ^ 3), (a = 3 ∨ a = 5) → (r = 1 ∨ r = 7) → (r = 1 ∨ r = a) → r = 1 := by
      decide
    exact (mem_Hres _ _ _).2 (Or.inl (key a _ ha' h1 h2))

theorem main : Claim := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, hq, ⟨e⟩⟩ := h 2
  have hL := quotient_distrib L hq
  letI : DistribLattice L := DistribLattice.ofInfSupLe hL
  have hup : ∀ (a : ZMod (2 ^ 3)) (ha : a * a = 1), (a = 3 ∨ a = 5) →
      e (Hres 7 h7) ⊔ e (Hres a ha) = e Top := by
    intro a ha ha'
    have := (OrderIso.isLUB_image' e).2 (isLUB_pair a ha ha')
    rw [Set.image_pair] at this
    exact (_root_.isLUB_pair (a := e (Hres 7 h7)) (b := e (Hres a ha))).unique this
  have hlo : ∀ (a : ZMod (2 ^ 3)) (ha : a * a = 1), (a = 3 ∨ a = 5) →
      e (Hres 7 h7) ⊓ e (Hres a ha) = e (Hres 1 (by decide)) := by
    intro a ha ha'
    have := (OrderIso.isGLB_image' e).2 (isGLB_pair a ha ha')
    rw [Set.image_pair] at this
    exact (_root_.isGLB_pair (a := e (Hres 7 h7)) (b := e (Hres a ha))).unique this
  have heq : e (Hres 3 h3) = e (Hres 5 h5) :=
    eq_of_inf_eq_sup_eq (a := e (Hres 7 h7))
      (by rw [inf_comm, hlo 3 h3 (Or.inl rfl), inf_comm, hlo 5 h5 (Or.inr rfl)])
      (by rw [sup_comm, hup 3 h3 (Or.inl rfl), sup_comm, hup 5 h5 (Or.inr rfl)])
  have hne := e.injective heq
  -- an element of `1 + 2ℤ_2` with residue 3
  have hunit : IsUnit (3 : ℤ_[2]) := by
    have h2 : (-2 : ℤ_[2]) ∈ nonunits ℤ_[2] := by
      intro hu
      exact PadicInt.p_nonunit (p := 2) (by simpa using hu.neg)
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2
    convert this using 1; norm_num
  let u : ↥(U1 2) := ⟨hunit.unit, ⟨1, by simp; norm_num⟩⟩
  have hu3 : res u = 3 := by
    have : pi8 3 = 3 := map_ofNat pi8 3
    simpa [res, u] using this
  have hmem : u ∈ Hres 3 h3 := (mem_Hres _ _ _).2 (Or.inr hu3)
  rw [hne] at hmem
  have := (mem_Hres _ _ _).1 hmem
  rw [hu3] at this
  revert this; decide

end C781
