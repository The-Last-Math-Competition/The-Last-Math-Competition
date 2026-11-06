import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Complex.Basic

namespace TLMC1581

noncomputable section
open scoped BigOperators

/-- The standard zero-local-trace Fricke--Painleve character surface. -/
abbrev CayleyPoint (K : Type*) [CommRing K] :=
  {p : K × K × K // p.1^2 + p.2.1^2 + p.2.2^2 + p.1*p.2.1*p.2.2 = 4}

def pointCount (K : Type*) [CommRing K] [Finite K] := Nat.card (CayleyPoint K)

abbrev RootPair (K : Type*) [CommRing K] :=
  {p : K × K // p.2^2 = p.1^2 - 4}

abbrev RootTriple (K : Type*) [CommRing K] :=
  {p : (K × K) × K // p.2^2 = (p.1.1^2-4)*(p.1.2^2-4)}

def pairFiberEquiv {K L : Type*} (P : K → L → Prop) :
    {p : K × L // P p.1 p.2} ≃ Σ x : K, {y : L // P x y} where
  toFun p := ⟨p.1.1, ⟨p.1.2,p.2⟩⟩
  invFun p := ⟨(p.1,p.2.1),p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {K : Type*} [Field K]

theorem rootpair_nonzero (h2 : (2:K) ≠ 0) (p : RootPair K) :
    p.1.1-p.1.2 ≠ 0 := by
  intro h
  have he : p.1.1=p.1.2 := sub_eq_zero.mp h
  have hp := p.2
  have h4 : (4:K)=0 := by rw [he] at hp; linear_combination hp
  have hn : (4:K) ≠ 0 := by convert mul_ne_zero h2 h2 using 1; norm_num
  exact hn h4

/-- A genuine hyperbola-to-nonzero-field-elements equivalence. -/
def hyperbolaEquiv (h2 : (2:K) ≠ 0) : RootPair K ≃ {u : K // u ≠ 0} where
  toFun p := ⟨p.1.1-p.1.2,rootpair_nonzero h2 p⟩
  invFun u := ⟨((u.1+4/u.1)/2,(4/u.1-u.1)/2),by
    field_simp [h2,u.2]
    ring⟩
  left_inv p := by
    apply Subtype.ext
    have hu := rootpair_nonzero h2 p
    apply Prod.ext
    · dsimp
      field_simp [hu,h2]
      linear_combination p.2
    · dsimp
      field_simp [hu,h2]
      linear_combination p.2
  right_inv u := by
    apply Subtype.ext
    dsimp
    field_simp [h2,u.2]
    ring

/-- Actual cubic fibers are transformed by w=2z+xy, matching the +xyz convention. -/
def cayleyRootEquiv (h2 : (2:K) ≠ 0) : CayleyPoint K ≃ RootTriple K where
  toFun p := ⟨((p.1.1,p.1.2.1),2*p.1.2.2+p.1.1*p.1.2.1),by
    dsimp
    linear_combination 4*p.2⟩
  invFun p := ⟨(p.1.1.1,p.1.1.2,(p.1.2-p.1.1.1*p.1.1.2)/2),by
    dsimp
    field_simp
    linear_combination p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · dsimp
        field_simp
        ring
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      field_simp
      ring

variable [Fintype K] [DecidableEq K]

theorem root_card (hF : ringChar K ≠ 2) (a : K) :
    (Nat.card {z : K // z^2=a} : ℤ) = quadraticChar K a + 1 := by
  classical
  have h := quadraticChar_card_sqrts hF a
  simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card] at h
  let e : (↑({x : K | x^2=a} : Set K)) ≃ {z : K // z^2=a} :=
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun x => ⟨x.1,x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e] at h
  exact h

theorem rootpair_card (h2 : (2:K) ≠ 0) :
    Nat.card (RootPair K) + 1 = Fintype.card K := by
  classical
  rw [Nat.card_congr (hyperbolaEquiv h2)]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hq := Fintype.card_pos (α := K)
  omega

theorem character_sum (hF : ringChar K ≠ 2) :
    ∑ x : K, quadraticChar K (x^2-4) = -1 := by
  classical
  have h2 : (2:K) ≠ 0 := Ring.two_ne_zero hF
  have hcard := rootpair_card h2
  have hs : (Nat.card (RootPair K) : ℤ) =
      ∑ x : K, (quadraticChar K (x^2-4)+1) := by
    rw [Nat.card_congr (pairFiberEquiv (fun x y : K => y^2=x^2-4))]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    simpa only [Nat.card_eq_fintype_card] using root_card hF (x^2-4)
  have hcast : (Nat.card (RootPair K) : ℤ)+1 = Fintype.card K := by exact_mod_cast hcard
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hs
  omega

theorem roottriple_card (hF : ringChar K ≠ 2) :
    (Nat.card (RootTriple K) : ℤ) =
      ∑ x : K, ∑ y : K, (quadraticChar K ((x^2-4)*(y^2-4))+1) := by
  classical
  rw [Nat.card_congr (pairFiberEquiv (fun p : K × K => fun w : K =>
    w^2=(p.1^2-4)*(p.2^2-4)))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simpa only [Nat.card_eq_fintype_card] using root_card hF ((x^2-4)*(y^2-4))

theorem point_count_odd (hF : ringChar K ≠ 2) :
    pointCount K = Fintype.card K ^ 2 + 1 := by
  classical
  have h2 : (2:K) ≠ 0 := Ring.two_ne_zero hF
  have he := Nat.card_congr (cayleyRootEquiv h2)
  have hc := roottriple_card hF
  have hs := character_sum hF
  have hcalc : (Nat.card (RootTriple K) : ℤ) = (Fintype.card K : ℤ)^2+1 := by
    rw [hc]
    simp_rw [map_mul]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hs]
    ring
  have hnat : Nat.card (RootTriple K) = Fintype.card K^2+1 := by exact_mod_cast hcalc
  exact he.trans hnat

theorem point_count_two : pointCount (ZMod 2) = 5 := by
  change Nat.card (CayleyPoint (ZMod 2)) = 5
  rw [Nat.card_eq_fintype_card]
  decide

theorem point_count_prime (p : ℕ) [Fact p.Prime] :
    pointCount (ZMod p) = p^2+1 := by
  by_cases h : p=2
  · subst p
    exact point_count_two
  · have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using h
    simpa using point_count_odd (K := ZMod p) hF

/-- The standard four-punctured-sphere presentation, not a label for a cubic. -/
def sphereRelator : FreeGroup (Fin 4) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 3
abbrev SphereGroup := PresentedGroup ({sphereRelator} : Set (FreeGroup (Fin 4)))
def loop (i : Fin 4) : SphereGroup := PresentedGroup.of i
abbrev SL2Q := Matrix.SpecialLinearGroup (Fin 2) ℚ

def skew (t : ℚ) (ht : t≠0) : SL2Q :=
  ⟨!![0,t;-1/t,0],by simp only [Matrix.det_fin_two]; dsimp; field_simp; ring⟩

theorem skew_pair (t : ℚ) (ht : t≠0) :
    skew t ht * skew (-t) (neg_ne_zero.mpr ht) = 1 := by
  apply Subtype.ext
  change !![0,t;-1/t,0] * !![0,-t;-1/(-t),0] = (1 : Matrix (Fin 2) (Fin 2) ℚ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,ht]

def b (n : ℕ) : ℚ := n+2
theorem b_gt_one (n : ℕ) : 1 < b n := by
  dsimp [b]
  have hn : 0 ≤ (n:ℚ) := Nat.cast_nonneg n
  linarith
theorem b_ne_zero (n : ℕ) : b n≠0 := ne_of_gt (lt_trans (by norm_num) (b_gt_one n))
def z (n : ℕ) : ℚ := b n + 1/b n

def generators (n : ℕ) : Fin 4 → SL2Q :=
  ![skew (-1) (by norm_num),skew 1 (by norm_num),
    skew (b n) (b_ne_zero n),skew (-b n) (neg_ne_zero.mpr (b_ne_zero n))]

theorem representation_relation (n : ℕ) :
    ∀ r ∈ ({sphereRelator} : Set (FreeGroup (Fin 4))),
      FreeGroup.lift (generators n) r=1 := by
  rintro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  have h1 := skew_pair (-1) (by norm_num : (-1:ℚ)≠0)
  have h2 := skew_pair (b n) (b_ne_zero n)
  simp only [neg_neg] at h1
  simp [sphereRelator,generators,h1,mul_assoc,h2]

def representation (n : ℕ) : SphereGroup →* SL2Q :=
  PresentedGroup.toGroup (representation_relation n)

theorem representation_loop (n : ℕ) (i : Fin 4) :
    representation n (loop i) = generators n i := by
  simp [representation,loop]

/-- The genuine character function evaluates matrix traces on every group element. -/
def character (ρ : SphereGroup →* SL2Q) (g : SphereGroup) : ℚ :=
  Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) ℚ)

def traceCoordinates (ρ : SphereGroup →* SL2Q) : ℚ × ℚ × ℚ :=
  (character ρ (loop 0*loop 1),character ρ (loop 1*loop 2),
    character ρ (loop 2*loop 0))

theorem local_traces_zero (n : ℕ) (i : Fin 4) :
    character (representation n) (loop i)=0 := by
  rw [character,representation_loop]
  fin_cases i <;> simp [generators,skew,Matrix.trace,Fin.sum_univ_succ]

theorem actual_trace_coordinates (n : ℕ) :
    traceCoordinates (representation n) = (2,-z n,z n) := by
  simp only [traceCoordinates,character,map_mul,representation_loop]
  change (Matrix.trace ((generators n 0 : Matrix (Fin 2) (Fin 2) ℚ)*
      (generators n 1 : Matrix (Fin 2) (Fin 2) ℚ)),
    Matrix.trace ((generators n 1 : Matrix (Fin 2) (Fin 2) ℚ)*
      (generators n 2 : Matrix (Fin 2) (Fin 2) ℚ)),
    Matrix.trace ((generators n 2 : Matrix (Fin 2) (Fin 2) ℚ)*
      (generators n 0 : Matrix (Fin 2) (Fin 2) ℚ))) = _
  simp [generators,skew,Matrix.trace,Fin.sum_univ_succ,z]
  ring_nf
  trivial

def rationalPoint (n : ℕ) : CayleyPoint ℚ :=
  ⟨traceCoordinates (representation n),by rw [actual_trace_coordinates]; ring⟩

theorem z_gt_two (n : ℕ) : 2 < z n := by
  have hb := b_gt_one n
  have hb0 : 0 < b n := lt_trans (by norm_num) hb
  have h : 0 < (b n-1)^2 := sq_pos_of_pos (by linarith)
  have he : z n-2 = (b n-1)^2/b n := by dsimp [z]; field_simp; ring
  have := div_pos h hb0
  linarith

theorem z_strictMono : StrictMono z := by
  intro n m hnm
  have hx := b_gt_one n
  have hy := b_gt_one m
  have hxy : b n < b m := by
    have hh : (n:ℚ) < (m:ℚ) := by exact_mod_cast hnm
    dsimp [b]
    linarith
  have hx0 : 0 < b n := lt_trans (by norm_num) hx
  have hy0 : 0 < b m := lt_trans (by norm_num) hy
  have he : z m-z n = (b m-b n)*(b n*b m-1)/(b n*b m) := by
    dsimp [z]
    field_simp
    ring
  have hp : 0 < b n*b m-1 := by nlinarith
  have := div_pos (mul_pos (sub_pos.mpr hxy) hp) (mul_pos hx0 hy0)
  linarith

theorem rationalPoint_injective : Function.Injective rationalPoint := by
  intro n m h
  have hh := congrArg (fun p : CayleyPoint ℚ => p.1.2.2) h
  simp only [rationalPoint,actual_trace_coordinates] at hh
  exact z_strictMono.injective hh

theorem character_family_injective :
    Function.Injective (fun n => character (representation n)) := by
  intro n m h
  have hh := congrFun h (loop 2*loop 0)
  have hn := congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) (actual_trace_coordinates n)
  have hm := congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) (actual_trace_coordinates m)
  change character (representation n) (loop 2*loop 0)=z n at hn
  change character (representation m) (loop 2*loop 0)=z m at hm
  exact z_strictMono.injective (hn.symm.trans (hh.trans hm))

def cubic : MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.X 0^2 + MvPolynomial.X 1^2 + MvPolynomial.X 2^2 +
    MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 2-MvPolynomial.C 4
def pointCoordinates (p : CayleyPoint ℚ) : Fin 3 → ℚ := ![p.1.1,p.1.2.1,p.1.2.2]

theorem eval_cubic (p : CayleyPoint ℚ) :
    MvPolynomial.eval (pointCoordinates p) cubic=0 := by
  simp [cubic,pointCoordinates,p.2]

theorem eval_pderiv (p : CayleyPoint ℚ) :
    MvPolynomial.eval (pointCoordinates p) (MvPolynomial.pderiv 0 cubic) =
      2*p.1.1+p.1.2.1*p.1.2.2 := by
  simp [cubic,pointCoordinates]
  ring

def SmoothRationalPoint :=
  {p : CayleyPoint ℚ // ∃ i : Fin 3,
    MvPolynomial.eval (pointCoordinates p) (MvPolynomial.pderiv i cubic)≠0}

theorem family_pderiv_ne_zero (n : ℕ) :
    MvPolynomial.eval (pointCoordinates (rationalPoint n))
      (MvPolynomial.pderiv 0 cubic) ≠ 0 := by
  rw [eval_pderiv]
  simp only [rationalPoint,actual_trace_coordinates]
  have hz := z_gt_two n
  nlinarith

def smoothPoint (n : ℕ) : SmoothRationalPoint :=
  ⟨rationalPoint n,0,family_pderiv_ne_zero n⟩

theorem smoothPoint_injective : Function.Injective smoothPoint := by
  intro n m h
  exact rationalPoint_injective (congrArg Subtype.val h)

theorem rational_points_infinite : Infinite (CayleyPoint ℚ) :=
  Infinite.of_injective rationalPoint rationalPoint_injective

theorem smooth_rational_points_infinite : Infinite SmoothRationalPoint :=
  Infinite.of_injective smoothPoint smoothPoint_injective

theorem rational_cardinal_not_finite (N : ℕ) :
    Cardinal.mk (CayleyPoint ℚ) ≠ N := by
  have := rational_points_infinite
  exact ne_of_gt (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n:=N))
    (Cardinal.aleph0_le_mk (CayleyPoint ℚ)))

theorem smooth_cardinal_not_finite (N : ℕ) :
    Cardinal.mk SmoothRationalPoint ≠ N := by
  have := smooth_rational_points_infinite
  exact ne_of_gt (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n:=N))
    (Cardinal.aleph0_le_mk SmoothRationalPoint))

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ
def complexRepresentation (n : ℕ) : SphereGroup →* SL2C :=
  (Matrix.SpecialLinearGroup.map (Rat.castHom ℂ)).comp (representation n)

theorem complex_trace_cast (n : ℕ) (g : SphereGroup) :
    Matrix.trace (complexRepresentation n g : Matrix (Fin 2) (Fin 2) ℂ) =
      (character (representation n) g : ℂ) := by
  change Matrix.trace ((Rat.castHom ℂ).mapMatrix
    (representation n g : Matrix (Fin 2) (Fin 2) ℚ)) = _
  simp [character,Matrix.trace,Fin.sum_univ_succ]

theorem sl2_trace_conjugation (U A : SL2C) :
    Matrix.trace ((U*A*U⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  change Matrix.trace ((U : Matrix (Fin 2) (Fin 2) ℂ)*
    (A : Matrix (Fin 2) (Fin 2) ℂ)*((U⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace (((U⁻¹*U : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)*
    (A : Matrix (Fin 2) (Fin 2) ℂ)) = _
  simp

/-- Distinct family members are not simultaneously SL2(C)-conjugate. -/
theorem family_not_conjugate {n m : ℕ} (hnm : n≠m) :
    ¬ ∃ U : SL2C, ∀ g : SphereGroup,
      complexRepresentation m g = U*complexRepresentation n g*U⁻¹ := by
  rintro ⟨U,hU⟩
  apply hnm
  apply character_family_injective
  funext g
  have h := congrArg (fun A : SL2C =>
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ)) (hU g)
  rw [sl2_trace_conjugation,complex_trace_cast,complex_trace_cast] at h
  exact_mod_cast h.symm

theorem literal_Q_formula_impossible (p : ℕ) (a : ℤ) :
    Cardinal.mk (CayleyPoint ℚ) ≠ (((p:ℤ)^2+a*p+1).toNat : Cardinal) ∧
    Cardinal.mk SmoothRationalPoint ≠ (((p:ℤ)^2+a*p+1).toNat : Cardinal) :=
  ⟨rational_cardinal_not_finite _,smooth_cardinal_not_finite _⟩

/-- Both source readings are addressed separately; the Fp formula is true with a=0. -/
theorem dual_domain_conclusion (p : ℕ) [Fact p.Prime] :
    pointCount (ZMod p) = p^2+1 ∧
    ∀ a : ℤ, Cardinal.mk (CayleyPoint ℚ) ≠
      (((p:ℤ)^2+a*p+1).toNat : Cardinal) :=
  ⟨point_count_prime p,fun a => (literal_Q_formula_impossible p a).1⟩

end
end TLMC1581
