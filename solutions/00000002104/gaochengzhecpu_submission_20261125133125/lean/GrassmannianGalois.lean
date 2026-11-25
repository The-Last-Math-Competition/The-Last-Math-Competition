import Std

namespace GrassmannianGalois

abbrev Exponent := Fin 8
abbrev OddIndex := Fin 4

/-- Integral coordinates in the basis 1, ζ, ζ², ζ³ of ℤ[ζ]. -/
structure Cyclotomic where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving DecidableEq, Repr

def Cyclotomic.add (a b : Cyclotomic) : Cyclotomic :=
  ⟨a.c0+b.c0, a.c1+b.c1, a.c2+b.c2, a.c3+b.c3⟩

def Cyclotomic.sub (a b : Cyclotomic) : Cyclotomic :=
  ⟨a.c0-b.c0, a.c1-b.c1, a.c2-b.c2, a.c3-b.c3⟩

def Cyclotomic.scale (n : Int) (a : Cyclotomic) : Cyclotomic :=
  ⟨n*a.c0, n*a.c1, n*a.c2, n*a.c3⟩

def Cyclotomic.mul (a b : Cyclotomic) : Cyclotomic :=
  ⟨a.c0*b.c0-a.c1*b.c3-a.c2*b.c2-a.c3*b.c1,
   a.c0*b.c1+a.c1*b.c0-a.c2*b.c3-a.c3*b.c2,
   a.c0*b.c2+a.c1*b.c1+a.c2*b.c0-a.c3*b.c3,
   a.c0*b.c3+a.c1*b.c2+a.c2*b.c1+a.c3*b.c0⟩

def basisVector (i : Fin 4) : Cyclotomic :=
  ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0,
   if i = 2 then 1 else 0, if i = 3 then 1 else 0⟩

def zetaPower (i : Exponent) : Cyclotomic :=
  (basisVector (Fin.ofNat' 4 i.val)).scale (if i.val < 4 then 1 else -1)

theorem zeta_power_multiplication : ∀ i j : Exponent,
    (zetaPower i).mul (zetaPower j) = zetaPower (i+j) := by decide

theorem distinct_zeta_powers : ∀ i j : Exponent,
    zetaPower i = zetaPower j → i = j := by decide

/-- The normalized eigenvalue divided by α, with the factor 8 from c₁. -/
def spectrumCoefficient (i j k : Exponent) : Cyclotomic :=
  (((zetaPower i).add (zetaPower j)).add (zetaPower k)).scale 8

def subsets : List (Exponent × Exponent × Exponent) :=
  (List.finRange 8).flatMap fun i =>
    (List.finRange 8).flatMap fun j =>
      ((List.finRange 8).filter (fun k => i < j && j < k)).map fun k => (i,j,k)

private theorem mem_fin_range (i : Fin n) : i ∈ List.finRange n := by
  rw [List.finRange, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem subsets_exact (i j k : Exponent) :
    (i,j,k) ∈ subsets ↔ i < j ∧ j < k := by
  simp only [subsets, List.mem_flatMap, List.mem_filter, List.mem_map,
    mem_fin_range, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, c, h, he⟩
    cases he
    exact h
  · intro h
    exact ⟨i, j, k, h, rfl⟩

theorem spectrum_size : subsets.length = 56 := by decide

def eigenvalueCoefficients : List Cyclotomic :=
  subsets.map fun (i,j,k) => spectrumCoefficient i j k

theorem extraction_identities :
    (spectrumCoefficient 1 2 3).sub (spectrumCoefficient 0 2 3) =
      ((zetaPower 1).sub (zetaPower 0)).scale 8 ∧
    (spectrumCoefficient 0 2 3).sub (spectrumCoefficient 2 3 4) =
      (zetaPower 0).scale 16 := by decide

theorem extraction_uses_spectral_roots :
    spectrumCoefficient 1 2 3 ∈ eigenvalueCoefficients ∧
    spectrumCoefficient 0 2 3 ∈ eigenvalueCoefficients ∧
    spectrumCoefficient 2 3 4 ∈ eigenvalueCoefficients := by
  unfold eigenvalueCoefficients
  exact ⟨List.mem_map.mpr ⟨(1,2,3), (subsets_exact 1 2 3).mpr (by decide), rfl⟩,
    List.mem_map.mpr ⟨(0,2,3), (subsets_exact 0 2 3).mpr (by decide), rfl⟩,
    List.mem_map.mpr ⟨(2,3,4), (subsets_exact 2 3 4).mpr (by decide), rfl⟩⟩

def oddExponent (u : OddIndex) : Exponent := ⟨2*u.val+1, by omega⟩

def oddIndex (i : Exponent) : OddIndex := ⟨i.val/2, by omega⟩

def unitMul (u v : OddIndex) : OddIndex := oddIndex (oddExponent u * oddExponent v)

theorem odd_units_exact (i : Exponent) :
    (∃ u : OddIndex, oddExponent u = i) ↔ i.val % 2 = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (by decide : ∀ v : OddIndex, (oddExponent v).val % 2 = 1) u
  · intro h
    exact ⟨oddIndex i,
      (by decide : ∀ j : Exponent, j.val % 2 = 1 → oddExponent (oddIndex j) = j) i h⟩

theorem unit_mul_exponents : ∀ u v : OddIndex,
    oddExponent (unitMul u v) = oddExponent u * oddExponent v := by decide

theorem cyclotomic_group_laws :
    (∀ u : OddIndex, unitMul 0 u = u ∧ unitMul u 0 = u ∧ unitMul u u = 0) ∧
    (∀ u v : OddIndex, unitMul u v = unitMul v u) ∧
    (∀ u v w : OddIndex, unitMul (unitMul u v) w = unitMul u (unitMul v w)) := by decide

/-- Apply ζ ↦ ζ^u to the four coefficients. -/
def substitute (u : OddIndex) (a : Cyclotomic) : Cyclotomic :=
  (((zetaPower 0).scale a.c0).add ((zetaPower (oddExponent u)).scale a.c1)).add
    (((zetaPower (oddExponent u * 2)).scale a.c2).add
      ((zetaPower (oddExponent u * 3)).scale a.c3))

theorem cyclotomic_action_on_powers : ∀ (u : OddIndex) (i : Exponent),
    substitute u (zetaPower i) = zetaPower (oddExponent u * i) := by decide

/-- Under α ↦ ζ^r α and ζ ↦ ζ^u the index i becomes r + ui modulo 8. -/
def affineAction (r : Exponent) (u : OddIndex) (i : Exponent) : Exponent :=
  r + oddExponent u * i

theorem action_on_root_coefficients : ∀ (r : Exponent) (u : OddIndex) (i : Exponent),
    (zetaPower r).mul (substitute u (zetaPower i)) = zetaPower (affineAction r u i) := by
  intro r u i
  rw [cyclotomic_action_on_powers, zeta_power_multiplication]
  rfl

private theorem add_assoc_mod8 : ∀ a b c : Exponent,
    a + (b + c) = a + b + c := by decide

private theorem mul_add_mod8 : ∀ a b c : Exponent,
    a * (b + c) = a * b + a * c := by decide

theorem affine_composition (r s : Exponent) (u v : OddIndex) (i : Exponent) :
    affineAction r u (affineAction s v i) =
      affineAction (r + oddExponent u * s) (unitMul u v) i := by
  simp only [affineAction, unit_mul_exponents, mul_add_mod8, add_assoc_mod8, Fin.mul_assoc]

theorem affine_action_inverses : ∀ (r : Exponent) (u : OddIndex) (i : Exponent),
    let inverseShift := oddExponent u * (0-r)
    affineAction inverseShift u (affineAction r u i) = i ∧
    affineAction r u (affineAction inverseShift u i) = i := by decide

theorem affine_distinct_labels_at_zero_and_one :
    ∀ (r s : Exponent) (u v : OddIndex),
      affineAction r u 0 = affineAction s v 0 →
      affineAction r u 1 = affineAction s v 1 → r = s ∧ u = v := by decide

def genericLabels : List (Exponent × OddIndex) :=
  (List.finRange 8).flatMap fun r => (List.finRange 4).map fun u => (r,u)

theorem generic_labels_exact (r : Exponent) (u : OddIndex) :
    (r,u) ∈ genericLabels := by simp [genericLabels, mem_fin_range]

theorem galois_orders_exclude_S5 :
    (List.finRange 4).length = 4 ∧
    genericLabels.Nodup ∧ genericLabels.length = 32 ∧
    (4 : Nat) ≠ 1*2*3*4*5 ∧ (32 : Nat) ≠ 1*2*3*4*5 := by decide

#print axioms zeta_power_multiplication
#print axioms subsets_exact
#print axioms extraction_identities
#print axioms extraction_uses_spectral_roots
#print axioms cyclotomic_group_laws
#print axioms affine_composition
#print axioms affine_action_inverses
#print axioms galois_orders_exclude_S5

end GrassmannianGalois
