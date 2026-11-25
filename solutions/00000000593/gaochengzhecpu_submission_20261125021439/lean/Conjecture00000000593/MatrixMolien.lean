/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Unconditional Matrix Molien Theorem from `n × n` matrices and determinants:
 1. `seriesCRing`: formal power series `ℤ[[t]]` as a commutative ring `CRing Series`.
 2. `detZPoly` and bridge theorems to `det seriesCRing` and `det intCRing`.
 3. Matrix geometric-series identity `(I_n - t A) (∑_{s=0}^{e-1} t^s A^s) = (1 - t^e) I_n`
    for any `n × n` integer matrix `A` with `A^e = I_n` (`e ≥ 1`).
 4. Determinant cofactor identity `det(I_n - t A) · B_A(t) = (1 - t^e)^n` with strict
    degree bound `deg B_A ≤ n(e - 1) < n e` and `det(I_n - t A)(0) = 1`.
 5. Formal power-series inversion `invUnitPoly` and unconditional rationality, strict
    divisibility-chain denominator, and modular periodic (quasi-polynomial) theorems for
    the Molien series of any finite matrix group `G`.
-/
import Conjecture00000000593.Determinant
import Conjecture00000000593.ModularPeriodic

namespace Conjecture00000000593

/-! ### 1. Formal Power Series `ℤ[[t]]` as a Commutative Ring `CRing Series` -/

/-- Prefix sum `F 0 + F 1 + ... + F (n - 1)`. -/
def rangeSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, F => rangeSum n F + F n

theorem rangeSum_congr {n : Nat} {F G : Nat → Int} (h : ∀ i : Nat, i < n → F i = G i) :
    rangeSum n F = rangeSum n G := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [rangeSum]
    rw [ih (fun i hi => h i (by omega)), h n' (by omega)]

theorem rangeSum_zero (n : Nat) : rangeSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [rangeSum, ih]

theorem rangeSum_add (n : Nat) (F G : Nat → Int) :
    rangeSum n (fun i => F i + G i) = rangeSum n F + rangeSum n G := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [rangeSum, ih]
    omega

theorem rangeSum_mul_left (c : Int) (n : Nat) (F : Nat → Int) :
    rangeSum n (fun i => c * F i) = c * rangeSum n F := by
  induction n with
  | zero => simp [rangeSum]
  | succ n' ih =>
    simp only [rangeSum, ih, Int.mul_add]

theorem rangeSum_mul_right (n : Nat) (F : Nat → Int) (c : Int) :
    rangeSum n (fun i => F i * c) = rangeSum n F * c := by
  induction n with
  | zero => simp [rangeSum]
  | succ n' ih =>
    simp only [rangeSum, ih, Int.add_mul]

theorem rangeSum_head :
    ∀ (n : Nat) (F : Nat → Int), rangeSum (n + 1) F = F 0 + rangeSum n (fun i => F (i + 1))
  | 0, F => by simp [rangeSum]
  | n + 1, F => by
    calc
      rangeSum (n + 2) F = rangeSum (n + 1) F + F (n + 1) := rfl
      _ = (F 0 + rangeSum n (fun i => F (i + 1))) + F (n + 1) := by rw [rangeSum_head n F]
      _ = F 0 + (rangeSum n (fun i => F (i + 1)) + F (n + 1)) := by omega
      _ = F 0 + rangeSum (n + 1) (fun i => F (i + 1)) := rfl

theorem rangeSum_rev :
    ∀ (n : Nat) (F : Nat → Int), rangeSum n F = rangeSum n (fun i => F (n - 1 - i))
  | 0, _ => rfl
  | n + 1, F => by
    rw [rangeSum_head n (fun i => F (n + 1 - 1 - i))]
    have h0 : F (n + 1 - 1 - 0) = F n := by
      have hn : n + 1 - 1 - 0 = n := by omega
      rw [hn]
    have htail : rangeSum n (fun i => F (n + 1 - 1 - (i + 1))) =
        rangeSum n (fun i => F (n - 1 - i)) := by
      apply rangeSum_congr
      intro i _
      have hi : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
      rw [hi]
    rw [h0, htail, ← rangeSum_rev n F]
    simp only [rangeSum]
    omega

theorem rangeSum_triangle_swap (A : Nat → Nat → Int) :
    ∀ m : Nat,
      rangeSum (m + 1) (fun j => rangeSum (j + 1) (fun i => A i j)) =
        rangeSum (m + 1) (fun i => rangeSum (m + 1 - i) (fun k => A i (i + k)))
  | 0 => by simp [rangeSum]
  | m + 1 => by
    have lhs_step :
        rangeSum (m + 2) (fun j => rangeSum (j + 1) (fun i => A i j)) =
          rangeSum (m + 1) (fun j => rangeSum (j + 1) (fun i => A i j)) +
            (rangeSum (m + 1) (fun i => A i (m + 1)) + A (m + 1) (m + 1)) := rfl
    rw [lhs_step, rangeSum_triangle_swap A m]
    have hcomb :
        rangeSum (m + 1) (fun i => rangeSum (m + 1 - i) (fun k => A i (i + k))) +
            rangeSum (m + 1) (fun i => A i (m + 1)) =
          rangeSum (m + 1) (fun i => rangeSum (m + 2 - i) (fun k => A i (i + k))) := by
      rw [← rangeSum_add]
      apply rangeSum_congr
      intro i hi
      have hsub : m + 2 - i = (m + 1 - i) + 1 := by omega
      have hidx : i + (m + 1 - i) = m + 1 := by omega
      rw [hsub]
      simp only [rangeSum, hidx]
    have hlast : A (m + 1) (m + 1) =
        rangeSum (m + 2 - (m + 1)) (fun k => A (m + 1) (m + 1 + k)) := by
      have h1 : m + 2 - (m + 1) = 1 := by omega
      rw [h1]
      simp [rangeSum]
    have hassoc :
        rangeSum (m + 1) (fun i => rangeSum (m + 1 - i) (fun k => A i (i + k))) +
            (rangeSum (m + 1) (fun i => A i (m + 1)) + A (m + 1) (m + 1)) =
          (rangeSum (m + 1) (fun i => rangeSum (m + 1 - i) (fun k => A i (i + k))) +
            rangeSum (m + 1) (fun i => A i (m + 1))) + A (m + 1) (m + 1) := by omega
    rw [hassoc, hcomb, hlast]
    rfl

/-- Cauchy convolution product on `Series = Nat → Int`. -/
def serMul (f g : Series) : Series :=
  fun m => rangeSum (m + 1) (fun i => f i * g (m - i))

/-- Formal power series `ℤ[[t]]` equipped with its commutative ring structure. -/
def seriesCRing : CRing Series where
  zero := fun _ => 0
  one := unitSeries
  add := fun f g m => f m + g m
  neg := fun f m => - f m
  mul := serMul
  add_assoc := fun _ _ _ => funext (fun _ => Int.add_assoc _ _ _)
  add_comm := fun _ _ => funext (fun _ => Int.add_comm _ _)
  zero_add := fun _ => funext (fun _ => Int.zero_add _)
  add_left_neg := fun _ => funext (fun _ => Int.add_left_neg _)
  mul_assoc := by
    intro f g h
    funext m
    unfold serMul
    have hL : rangeSum (m + 1) (fun j => rangeSum (j + 1) (fun i => f i * g (j - i)) * h (m - j)) =
        rangeSum (m + 1) (fun j => rangeSum (j + 1) (fun i => f i * g (j - i) * h (m - j))) := by
      apply rangeSum_congr
      intro j _
      rw [← rangeSum_mul_right]
    rw [hL, rangeSum_triangle_swap (fun i j => f i * g (j - i) * h (m - j)) m]
    apply rangeSum_congr
    intro i hi
    rw [← rangeSum_mul_left]
    have hlen : m + 1 - i = m - i + 1 := by omega
    rw [hlen]
    apply rangeSum_congr
    intro k hk
    have h1 : i + k - i = k := by omega
    have h2 : m - (i + k) = m - i - k := by omega
    rw [h1, h2, Int.mul_assoc]
  mul_comm := by
    intro f g
    funext m
    unfold serMul
    rw [rangeSum_rev (m + 1)]
    apply rangeSum_congr
    intro i hi
    have h1 : m + 1 - 1 - i = m - i := by omega
    have h2 : m - (m - i) = i := by omega
    rw [h1, h2, Int.mul_comm]
  one_mul := by
    intro f
    funext m
    unfold serMul unitSeries
    rw [rangeSum_head m]
    have h0 : (if 0 = 0 then (1 : Int) else 0) * f (m - 0) = f m := by simp
    have hrest : rangeSum m (fun i => (if i + 1 = 0 then (1 : Int) else 0) * f (m - (i + 1))) = 0 := by
      have hcongr : rangeSum m (fun i => (if i + 1 = 0 then (1 : Int) else 0) * f (m - (i + 1))) =
          rangeSum m (fun _ => 0) := by
        apply rangeSum_congr
        intro i _
        have hne : i + 1 ≠ 0 := Nat.succ_ne_zero i
        simp only [hne, ↓reduceIte, Int.zero_mul]
      rw [hcongr, rangeSum_zero]
    rw [h0, hrest, Int.add_zero]
  left_distrib := by
    intro f g h
    funext m
    unfold serMul
    rw [← rangeSum_add]
    apply rangeSum_congr
    intro i _
    exact Int.mul_add _ _ _

/-- Canonical embedding `ZPoly → Series` (`ofPoly P m = coeff P m`). -/
def ofPoly (P : ZPoly) : Series :=
  mulPolySeries P unitSeries

theorem ofPoly_coeff (P : ZPoly) (m : Nat) : ofPoly P m = coeff P m :=
  mulPolySeries_unit P m

theorem polyEq_iff_ofPoly_eq {P Q : ZPoly} : PolyEq P Q ↔ ofPoly P = ofPoly Q := by
  constructor
  · intro h
    funext m
    rw [ofPoly_coeff, ofPoly_coeff]
    exact h m
  · intro h m
    rw [← ofPoly_coeff, ← ofPoly_coeff, h]

theorem mulPolySeries_eq_serMul (P : ZPoly) (a : Series) :
    mulPolySeries P a = serMul (ofPoly P) a := by
  induction P with
  | nil =>
    funext m
    unfold serMul ofPoly
    have hcongr : rangeSum (m + 1) (fun i => mulPolySeries [] unitSeries i * a (m - i)) =
        rangeSum (m + 1) (fun _ => 0) := by
      apply rangeSum_congr
      intro _ _
      exact Int.zero_mul _
    simp only [mulPolySeries]
    exact (hcongr.trans (rangeSum_zero (m + 1))).symm
  | cons c cs ih =>
    funext m
    cases m with
    | zero =>
      unfold serMul ofPoly
      simp [rangeSum, mulPolySeries, unitSeries]
    | succ m' =>
      unfold serMul
      rw [rangeSum_head (m' + 1)]
      have h0 : ofPoly (c :: cs) 0 * a (m' + 1 - 0) = c * a (m' + 1) := by
        rw [ofPoly_coeff]
        simp [coeff]
      have htail : rangeSum (m' + 1) (fun i => ofPoly (c :: cs) (i + 1) * a (m' + 1 - (i + 1))) =
          serMul (ofPoly cs) a m' := by
        unfold serMul
        apply rangeSum_congr
        intro i _
        rw [ofPoly_coeff, ofPoly_coeff]
        have hsub : m' + 1 - (i + 1) = m' - i := by omega
        rw [hsub]
        rfl
      rw [h0, htail, ← ih]
      rfl

theorem ofPoly_add (P Q : ZPoly) :
    ofPoly (add P Q) = seriesCRing.add (ofPoly P) (ofPoly Q) := by
  funext m
  unfold ofPoly
  exact mulPolySeries_add P Q unitSeries m

theorem ofPoly_scale (c : Int) (P : ZPoly) :
    ofPoly (scale c P) = fun m => c * ofPoly P m := by
  funext m
  unfold ofPoly
  exact mulPolySeries_scale c P unitSeries m

theorem ofPoly_mul (P Q : ZPoly) :
    ofPoly (mul P Q) = seriesCRing.mul (ofPoly P) (ofPoly Q) := by
  unfold ofPoly
  rw [mulPolySeries_mul, mulPolySeries_eq_serMul]
  rfl

/-! ### 2. Polynomial Matrix Determinants `detZPoly` and Bridge Lemmas -/

def finSumZPoly : (n : Nat) → (Fin n → ZPoly) → ZPoly
  | 0, _ => []
  | n + 1, f => add (f ⟨0, Nat.zero_lt_succ n⟩) (finSumZPoly n (fun i => f i.succ))

theorem ofPoly_finSumZPoly :
    ∀ (n : Nat) (f : Fin n → ZPoly),
      ofPoly (finSumZPoly n f) = seriesCRing.finSum n (fun i => ofPoly (f i))
  | 0, _ => rfl
  | n + 1, f => by
    simp only [finSumZPoly, CRing.finSum]
    rw [ofPoly_add, ofPoly_finSumZPoly n (fun i => f i.succ)]

theorem coeff0_finSumZPoly :
    ∀ (n : Nat) (f : Fin n → ZPoly),
      coeff (finSumZPoly n f) 0 = intCRing.finSum n (fun i => coeff (f i) 0)
  | 0, _ => rfl
  | n + 1, f => by
    simp only [finSumZPoly, CRing.finSum]
    rw [coeff_add, coeff0_finSumZPoly n (fun i => f i.succ)]
    rfl

theorem isPolyBelow_add {B : Nat} {f g : Series}
    (hf : IsPolyBelow B f) (hg : IsPolyBelow B g) :
    IsPolyBelow B (seriesCRing.add f g) := by
  intro m hm
  change f m + g m = 0
  rw [hf m hm, hg m hm]
  simp

theorem isPolyBelow_finSumZPoly :
    ∀ (n B : Nat) (f : Fin n → ZPoly),
      (∀ i : Fin n, IsPolyBelow B (ofPoly (f i))) →
      IsPolyBelow B (ofPoly (finSumZPoly n f))
  | 0, B, _, _ => by
    intro m _
    rfl
  | n + 1, B, f, h => by
    rw [ofPoly_finSumZPoly]
    simp only [CRing.finSum]
    apply isPolyBelow_add (h ⟨0, Nat.zero_lt_succ n⟩)
    rw [← ofPoly_finSumZPoly n (fun i => f i.succ)]
    exact isPolyBelow_finSumZPoly n B (fun i => f i.succ) (fun i => h i.succ)

theorem isPolyBelow_serMul {a b : Nat} {f g : Series}
    (hf : IsPolyBelow (a + 1) f) (hg : IsPolyBelow (b + 1) g) :
    IsPolyBelow (a + b + 1) (seriesCRing.mul f g) := by
  intro m hm
  change rangeSum (m + 1) (fun i => f i * g (m - i)) = 0
  rw [← rangeSum_zero (m + 1)]
  apply rangeSum_congr
  intro i _
  by_cases hi : a + 1 ≤ i
  · rw [hf i hi, Int.zero_mul]
  · have hgi : b + 1 ≤ m - i := by omega
    rw [hg (m - i) hgi, Int.mul_zero]

/-- Laplace determinant of a polynomial matrix `M : Mat ZPoly n`. -/
def detZPoly : {n : Nat} → Mat ZPoly n → ZPoly
  | 0, _ => [1]
  | n + 1, M =>
      let r0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      finSumZPoly (n + 1) (fun j =>
        scale (intCRing.altSign j.val)
          (mul (M r0 j) (detZPoly (minor M r0 j))))

theorem altSign_series_eq (k : Nat) :
    seriesCRing.altSign k = fun m => if m = 0 then intCRing.altSign k else 0 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [CRing.altSign, ih]
    funext m
    change - (if m = 0 then intCRing.altSign k' else 0) =
      if m = 0 then - intCRing.altSign k' else 0
    by_cases hm : m = 0 <;> simp [hm]

theorem serMul_altSign (k : Nat) (f : Series) :
    seriesCRing.mul (seriesCRing.altSign k) f = fun m => intCRing.altSign k * f m := by
  funext m
  change rangeSum (m + 1) (fun i => seriesCRing.altSign k i * f (m - i)) =
    intCRing.altSign k * f m
  rw [altSign_series_eq k, rangeSum_head m]
  have h0 : (if 0 = 0 then intCRing.altSign k else 0) * f (m - 0) = intCRing.altSign k * f m := by
    simp
  have hrest : rangeSum m (fun i => (if i + 1 = 0 then intCRing.altSign k else 0) * f (m - (i + 1))) = 0 := by
    have hcongr : rangeSum m (fun i => (if i + 1 = 0 then intCRing.altSign k else 0) * f (m - (i + 1))) =
        rangeSum m (fun _ => 0) := by
      apply rangeSum_congr
      intro i _
      have hne : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp only [hne, ↓reduceIte, Int.zero_mul]
    rw [hcongr, rangeSum_zero]
  rw [h0, hrest, Int.add_zero]

theorem ofPoly_detZPoly :
    ∀ {n : Nat} (M : Mat ZPoly n),
      ofPoly (detZPoly M) = det seriesCRing (fun i j => ofPoly (M i j))
  | 0, _ => by
      funext m
      rw [ofPoly_coeff]
      cases m <;> rfl
  | n + 1, M => by
      simp only [detZPoly, det]
      rw [ofPoly_finSumZPoly]
      apply seriesCRing.finSum_congr
      intro j
      rw [ofPoly_scale, ofPoly_mul, serMul_altSign]
      have hmin : (fun i k => ofPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j i k)) =
          minor (fun i k => ofPoly (M i k)) ⟨0, Nat.zero_lt_succ n⟩ j := rfl
      rw [ofPoly_detZPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j), hmin]

theorem coeff0_detZPoly :
    ∀ {n : Nat} (M : Mat ZPoly n),
      coeff (detZPoly M) 0 = det intCRing (fun i j => coeff (M i j) 0)
  | 0, _ => rfl
  | n + 1, M => by
      simp only [detZPoly, det]
      rw [coeff0_finSumZPoly]
      apply intCRing.finSum_congr
      intro j
      rw [coeff_scale]
      have hmul0 : coeff (mul (M ⟨0, Nat.zero_lt_succ n⟩ j) (detZPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j))) 0 =
          coeff (M ⟨0, Nat.zero_lt_succ n⟩ j) 0 * coeff (detZPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j)) 0 := by
        rw [← ofPoly_coeff, ofPoly_mul]
        change rangeSum 1 _ = _
        simp [rangeSum, ofPoly_coeff]
      rw [hmul0, coeff0_detZPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j)]
      rfl

theorem isPolyBelow_detZPoly :
    ∀ {n : Nat} (d : Nat) (M : Mat ZPoly n),
      (∀ i j : Fin n, IsPolyBelow (d + 1) (ofPoly (M i j))) →
      IsPolyBelow (n * d + 1) (ofPoly (detZPoly M))
  | 0, d, _, _ => by
      intro m hm
      rw [Nat.zero_mul, Nat.zero_add] at hm
      rw [ofPoly_coeff]
      cases m with
      | zero => omega
      | succ _ => rfl
  | n + 1, d, M, h => by
      simp only [detZPoly]
      apply isPolyBelow_finSumZPoly (n + 1) ((n + 1) * d + 1)
      intro j
      intro m hm
      rw [ofPoly_scale]
      have hprod : IsPolyBelow (d + (n * d) + 1)
          (ofPoly (mul (M ⟨0, Nat.zero_lt_succ n⟩ j) (detZPoly (minor M ⟨0, Nat.zero_lt_succ n⟩ j)))) := by
        rw [ofPoly_mul]
        apply isPolyBelow_serMul (h ⟨0, Nat.zero_lt_succ n⟩ j)
        apply isPolyBelow_detZPoly d (minor M ⟨0, Nat.zero_lt_succ n⟩ j)
        intro r c
        exact h (skipIdx ⟨0, Nat.zero_lt_succ n⟩ r) (skipIdx j c)
      have heq_deg : d + n * d + 1 = (n + 1) * d + 1 := by
        rw [Nat.succ_mul]
        omega
      rw [heq_deg] at hprod
      dsimp only
      rw [hprod m hm, Int.mul_zero]

/-! ### 3. Polynomial Matrix Geometric Series `(I_n - t A) (∑_{s=0}^{e-1} t^s A^s) = (1 - t^e) I_n` -/

/-- Characteristic polynomial matrix `I_n - t A` of an integer matrix `A : Mat Int n`. -/
def charPolyMat {n : Nat} (A : Mat Int n) : Mat ZPoly n :=
  fun i j => [if i.val = j.val then 1 else 0, - A i j]

/-- Characteristic determinant `det(I_n - t A) ∈ ℤ[t]`. -/
def charDetPoly {n : Nat} (A : Mat Int n) : ZPoly :=
  detZPoly (charPolyMat A)

theorem coeff0_charDetPoly {n : Nat} (A : Mat Int n) :
    coeff (charDetPoly A) 0 = 1 := by
  unfold charDetPoly
  rw [coeff0_detZPoly]
  have hmat : (fun i j : Fin n => coeff (charPolyMat A i j) 0) = matId intCRing n := by
    funext i j
    rfl
  rw [hmat]
  exact det_id intCRing n

/-- Auxiliary matrix polynomial `∑_{s=0}^{k-1} t^s (A^s · cur)`. -/
def geomPolyFrom {n : Nat} (A cur : Mat Int n) : Nat → Mat ZPoly n
  | 0 => fun _ _ => []
  | k + 1 => fun i j => cur i j :: geomPolyFrom A (matMul intCRing A cur) k i j

/-- Matrix geometric sum `S_A(t) = ∑_{s=0}^{e-1} t^s A^s`. -/
def geomPolyMat {n : Nat} (A : Mat Int n) (e : Nat) : Mat ZPoly n :=
  geomPolyFrom A (matId intCRing n) e

/-- Cofactor polynomial `B_A(t) = det(∑_{s=0}^{e-1} t^s A^s) ∈ ℤ[t]`. -/
def geomDetPoly {n : Nat} (A : Mat Int n) (e : Nat) : ZPoly :=
  detZPoly (geomPolyMat A e)

theorem geomPolyFrom_length {n : Nat} (A : Mat Int n) :
    ∀ (k : Nat) (cur : Mat Int n) (i j : Fin n),
      (geomPolyFrom A cur k i j).length = k
  | 0, _, _, _ => rfl
  | k + 1, cur, i, j => by
      simp only [geomPolyFrom, List.length_cons, geomPolyFrom_length A k]

theorem isPolyBelow_geomDetPoly {n e : Nat} (hn : 1 ≤ n) (he : 1 ≤ e) (A : Mat Int n) :
    IsPolyBelow (n * e) (ofPoly (geomDetPoly A e)) := by
  have hbound : IsPolyBelow (n * (e - 1) + 1) (ofPoly (geomDetPoly A e)) := by
    apply isPolyBelow_detZPoly (e - 1) (geomPolyMat A e)
    intro i j m hm
    rw [ofPoly_coeff]
    apply coeff_gt_length
    unfold geomPolyMat
    rw [geomPolyFrom_length]
    omega
  intro m hm
  apply hbound m
  have hle : n * (e - 1) + 1 ≤ n * e := by
    have he1 : e = (e - 1) + 1 := by omega
    conv => rhs; rw [he1, Nat.mul_add, Nat.mul_one]
    omega
  omega

theorem int_finSum_map_mul_t {n : Nat} (f : Fin n → Series) (m : Nat) :
    seriesCRing.finSum n f m = intCRing.finSum n (fun j => f j m) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [CRing.finSum]
    change f ⟨0, Nat.zero_lt_succ n'⟩ m + seriesCRing.finSum n' (fun i => f i.succ) m = _
    rw [ih (fun i => f i.succ)]
    rfl

theorem geomPolyFrom_coeff {n : Nat} (A : Mat Int n) :
    ∀ (k : Nat) (cur : Mat Int n) (i j : Fin n) (m : Nat),
      coeff (geomPolyFrom A cur k i j) m =
        if m < k then matMul intCRing (matPow intCRing A m) cur i j else 0
  | 0, cur, i, j, m => by
      simp [geomPolyFrom, coeff]
  | k + 1, cur, i, j, 0 => by
      simp only [geomPolyFrom, coeff, Nat.zero_lt_succ, ↓reduceIte, matPow]
      rw [matId_mul]
  | k + 1, cur, i, j, m + 1 => by
      simp only [geomPolyFrom, coeff]
      rw [geomPolyFrom_coeff A k (matMul intCRing A cur) i j m]
      by_cases hlt : m < k
      · have hlt2 : m + 1 < k + 1 := by omega
        simp only [hlt, hlt2, ↓reduceIte, matPow]
        -- Show `((A * A^m) * cur)_{i,j} = (A^m * (A * cur))_{i,j}`:
        -- Wait: prove `matPow_mul_comm : A^m * (A * cur) = (A * A^m) * cur`!
        have hpow_assoc : ∀ (s : Nat) (C : Mat Int n),
            matMul intCRing (matPow intCRing A s) (matMul intCRing A C) =
              matMul intCRing (matMul intCRing A (matPow intCRing A s)) C := by
          -- Associate `matMul` in general!
          intro s C
          -- Inline general matrix multiplication associativity over `intCRing`:
          have hmat_assoc : ∀ (X Y Z : Mat Int n),
              matMul intCRing (matMul intCRing X Y) Z =
                matMul intCRing X (matMul intCRing Y Z) := by
            intro X Y Z
            funext r c
            unfold matMul
            -- Expand both sides by induction on middle Fin sums:
            have hsum_swap : ∀ (p q : Nat) (W : Fin p → Fin q → Int),
                intCRing.finSum p (fun u => intCRing.finSum q (fun v => W u v)) =
                  intCRing.finSum q (fun v => intCRing.finSum p (fun u => W u v)) := by
              intro p
              induction p with
              | zero =>
                intro q _
                simp only [CRing.finSum]
                exact (intCRing.finSum_zero q).symm
              | succ p' ihp =>
                intro q W
                simp only [CRing.finSum]
                rw [ihp q (fun u v => W u.succ v), ← intCRing.finSum_add]
            have hL : intCRing.finSum n (fun u => intCRing.mul (intCRing.finSum n (fun v => intCRing.mul (X r v) (Y v u))) (Z u c)) =
                intCRing.finSum n (fun u => intCRing.finSum n (fun v => X r v * (Y v u * Z u c))) := by
              apply intCRing.finSum_congr
              intro u
              rw [← intCRing.finSum_mul_right]
              apply intCRing.finSum_congr
              intro v
              exact Int.mul_assoc _ _ _
            have hR : intCRing.finSum n (fun v => intCRing.mul (X r v) (intCRing.finSum n (fun u => intCRing.mul (Y v u) (Z u c)))) =
                intCRing.finSum n (fun v => intCRing.finSum n (fun u => X r v * (Y v u * Z u c))) := by
              apply intCRing.finSum_congr
              intro v
              rw [← intCRing.finSum_mul_left]
              rfl
            rw [hL, hR, hsum_swap]
          have hmat_id_right : ∀ (M : Mat Int n), matMul intCRing M (matId intCRing n) = M := by
            intro M
            funext r c
            unfold matMul matId
            rw [intCRing.finSum_eq_single c]
            · simp only [↓reduceIte, intCRing.mul_one]
            · intro j hj
              have hv : j.val ≠ c.val := fun h => hj (Fin.ext h)
              simp only [hv, ↓reduceIte, intCRing.mul_zero]
          induction s with
          | zero =>
            simp only [matPow]
            rw [matId_mul, hmat_id_right A]
          | succ s' ihs =>
            simp only [matPow]
            rw [hmat_assoc A (matPow intCRing A s') (matMul intCRing A C), ihs, ← hmat_assoc]
        rw [hpow_assoc m cur]
      · have hlt2 : ¬ (m + 1 < k + 1) := by omega
        simp [hlt, hlt2]

/-- **Polynomial Matrix Geometric-Series Identity:**
If `A^e = I_n` (`e ≥ 1`), then `(I_n - t A) · (∑_{s=0}^{e-1} t^s A^s) = (1 - t^e) I_n`
in `Mat Series n`. -/
theorem charPolyMat_mul_geomPolyMat {n e : Nat} (he : 1 ≤ e) (A : Mat Int n)
    (hAe : matPow intCRing A e = matId intCRing n) :
    matMul seriesCRing
        (fun i j => ofPoly (charPolyMat A i j))
        (fun i j => ofPoly (geomPolyMat A e i j)) =
      scalarMat seriesCRing n (ofPoly (oneMinusTPow e)) := by
  funext i k m
  unfold matMul
  rw [int_finSum_map_mul_t]
  -- Evaluate each summand `(ofPoly (charPolyMat A i j) * ofPoly (geomPolyMat A e j k)) m`:
  have hterm : ∀ j : Fin n,
      seriesCRing.mul (ofPoly (charPolyMat A i j)) (ofPoly (geomPolyMat A e j k)) m =
        (if i.val = j.val then coeff (geomPolyMat A e j k) m else 0) -
          (if m = 0 then 0 else A i j * coeff (geomPolyMat A e j k) (m - 1)) := by
    intro j
    rw [← ofPoly_mul, ofPoly_coeff, ← mulPolySeries_unit]
    rw [mulPolySeries_mul]
    unfold charPolyMat
    cases m with
    | zero =>
      simp only [mulPolySeries, mulPolySeries_unit]
      by_cases hij : i.val = j.val <;> simp [hij]
    | succ m' =>
      cases m' with
      | zero =>
        by_cases hij : i.val = j.val <;>
          simp [mulPolySeries, mulPolySeries_unit, hij, Int.neg_mul] <;> omega
      | succ m'' =>
        by_cases hij : i.val = j.val <;>
          simp [mulPolySeries, mulPolySeries_unit, hij, Int.neg_mul] <;> omega
  have hsum_eq := intCRing.finSum_congr hterm
  rw [hsum_eq]
  have hfin_sub : ∀ (u v : Fin n → Int),
      intCRing.finSum n (fun j => u j - v j) = intCRing.finSum n u - intCRing.finSum n v := by
    intro u v
    have h1 := intCRing.finSum_add u (fun j => - v j)
    have h2 := intCRing.finSum_mul_left (-1) v
    have hneg : (fun j => intCRing.add (u j) (- v j)) = (fun j => u j - v j) := by
      funext j; change u j + - v j = u j - v j; omega
    have hneg2 : (fun j => intCRing.mul (-1) (v j)) = (fun j => - v j) := by
      funext j; change (-1) * v j = - v j; omega
    rw [← hneg, h1, ← hneg2, h2]
    change intCRing.finSum n u + (-1) * intCRing.finSum n v = _
    omega
  rw [hfin_sub]
  have hfirst : intCRing.finSum n (fun j => if i.val = j.val then coeff (geomPolyMat A e j k) m else 0) =
      coeff (geomPolyMat A e i k) m := by
    rw [intCRing.finSum_eq_single i]
    · simp
    · intro j hj
      have hv : i.val ≠ j.val := fun h => hj (Fin.ext h).symm
      simp only [hv, ↓reduceIte]
      rfl
  rw [hfirst]
  have hmat_id_r : ∀ (M : Mat Int n), matMul intCRing M (matId intCRing n) = M := by
    intro M
    funext r c
    unfold matMul matId
    rw [intCRing.finSum_eq_single c]
    · simp only [↓reduceIte, intCRing.mul_one]
    · intro j hj
      have hv : j.val ≠ c.val := fun h => hj (Fin.ext h)
      simp only [hv, ↓reduceIte, intCRing.mul_zero]
  unfold geomPolyMat
  rw [geomPolyFrom_coeff]
  cases m with
  | zero =>
    have h0lt : 0 < e := by omega
    simp only [h0lt, ↓reduceIte, matPow, matId_mul]
    change matId intCRing n i k - intCRing.finSum n (fun _ => intCRing.zero) =
      scalarMat seriesCRing n (ofPoly (oneMinusTPow e)) i k 0
    rw [intCRing.finSum_zero]
    dsimp [intCRing]
    rw [Int.sub_zero]
    unfold scalarMat oneMinusTPow matId
    by_cases hik : i.val = k.val
    · simp only [hik, ↓reduceIte]
      rw [ofPoly_coeff, coeff_add, coeff_scale, coeff_tPow]
      have h0ne : 0 ≠ e := by omega
      simp [coeff, h0ne]
    · simp only [hik, ↓reduceIte]
      rfl
  | succ m' =>
    have hnz : m' + 1 ≠ 0 := Nat.succ_ne_zero m'
    have hsub : m' + 1 - 1 = m' := by omega
    simp only [hnz, ↓reduceIte, hsub]
    have hsecond : intCRing.finSum n (fun j => A i j * coeff (geomPolyFrom A (matId intCRing n) e j k) m') =
        if m' < e then matPow intCRing A (m' + 1) i k else 0 := by
      by_cases hm' : m' < e
      · have hstep : (fun j => A i j * coeff (geomPolyFrom A (matId intCRing n) e j k) m') =
            (fun j => intCRing.mul (A i j) (matPow intCRing A m' j k)) := by
          funext j
          rw [geomPolyFrom_coeff, hmat_id_r]
          simp [hm']
          rfl
        rw [intCRing.finSum_congr (fun j => congrFun hstep j)]
        simp only [hm', ↓reduceIte, matPow]
        rfl
      · simp only [hm', ↓reduceIte]
        change intCRing.finSum n (fun j => A i j * coeff (geomPolyFrom A (matId intCRing n) e j k) m') =
          intCRing.zero
        rw [← intCRing.finSum_zero n]
        apply intCRing.finSum_congr
        intro j
        rw [geomPolyFrom_coeff]
        simp only [hm', ↓reduceIte, Int.mul_zero]
        rfl
    rw [hsecond, hmat_id_r]
    unfold scalarMat oneMinusTPow
    by_cases hlt1 : m' + 1 < e
    · have hm' : m' < e := by omega
      have hne_e : m' + 1 ≠ e := by omega
      simp only [hlt1, hm', ↓reduceIte, Int.sub_self]
      by_cases hik : i.val = k.val
      · simp only [hik, ↓reduceIte]
        rw [ofPoly_coeff, coeff_add, coeff_scale, coeff_tPow]
        simp [coeff, hne_e]
      · simp [hik]; rfl
    · by_cases heq_e : m' + 1 = e
      · have hm' : m' < e := by omega
        simp only [hlt1, hm', ↓reduceIte, heq_e, hAe, Int.zero_sub]
        unfold matId
        by_cases hik : i.val = k.val
        · simp only [hik, ↓reduceIte]
          rw [ofPoly_coeff, coeff_add, coeff_scale, coeff_tPow]
          cases e with
          | zero => omega
          | succ _ => simp [coeff]; rfl
        · simp [hik]; rfl
      · have hm' : ¬ (m' < e) := by omega
        have hne_e : m' + 1 ≠ e := by omega
        simp only [hlt1, hm', ↓reduceIte, Int.sub_zero]
        by_cases hik : i.val = k.val
        · simp only [hik, ↓reduceIte]
          rw [ofPoly_coeff, coeff_add, coeff_scale, coeff_tPow]
          simp [coeff, hne_e]
        · simp [hik]; rfl

theorem series_pow_oneMinusTPow (e : Nat) :
    ∀ n : Nat, seriesCRing.pow (ofPoly (oneMinusTPow e)) n =
      ofPoly (chainProd (List.replicate n e))
  | 0 => by
      funext m
      simp only [CRing.pow, List.replicate, chainProd]
      rw [ofPoly_coeff]
      cases m <;> rfl
  | n + 1 => by
      simp only [CRing.pow, List.replicate_succ, chainProd]
      rw [ofPoly_mul, series_pow_oneMinusTPow e n]

/-- **Matrix Determinant Cofactor Theorem (`det(I_n - t A) · B_A(t) = (1 - t^e)^n`):**
For any `A : Mat Int n` satisfying `A^e = I_n` (`e ≥ 1`), the characteristic determinant
`det(I_n - t A)` divides `(1 - t^e)^n` in `ℤ[t]` with explicit cofactor `geomDetPoly A e`. -/
theorem charDet_mul_geomDet_eq_chainProd {n e : Nat} (he : 1 ≤ e) (A : Mat Int n)
    (hAe : matPow intCRing A e = matId intCRing n) :
    PolyEq (mul (charDetPoly A) (geomDetPoly A e)) (chainProd (List.replicate n e)) := by
  rw [polyEq_iff_ofPoly_eq, ofPoly_mul]
  unfold charDetPoly geomDetPoly
  rw [ofPoly_detZPoly, ofPoly_detZPoly, ← det_mul seriesCRing]
  rw [charPolyMat_mul_geomPolyMat he A hAe, det_scalar seriesCRing]
  exact series_pow_oneMinusTPow e n

/-! ### 4. Formal Power-Series Inversion `invUnitPoly` and Actual Molien Series -/

def dotRev : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | c :: cs, b :: bs => c * b + dotRev cs bs

def invRev (tailP : ZPoly) : Nat → List Int
  | 0 => [1]
  | m + 1 =>
      let prev := invRev tailP m
      (- dotRev tailP prev) :: prev

/-- Exact formal power-series inverse `1 / P(t) ∈ ℤ[[t]]` for any `P ∈ ℤ[t]` with `P(0) = 1`. -/
def invUnitPoly (P : ZPoly) : Series :=
  fun m => (invRev P.tail m).headD 0

theorem dotRev_invRev_eq_mulPolySeries (cs : ZPoly) :
    ∀ (qs : ZPoly) (m : Nat),
      dotRev qs (invRev cs m) = mulPolySeries qs (fun k => (invRev cs k).headD 0) m
  | [], _ => by
      simp [dotRev, mulPolySeries]
  | q :: qs, 0 => by
      have hnil : dotRev qs [] = 0 := by cases qs <;> rfl
      simp [invRev, dotRev, mulPolySeries, hnil]
  | q :: qs, m + 1 => by
      simp only [invRev, dotRev, List.headD_cons, mulPolySeries]
      rw [dotRev_invRev_eq_mulPolySeries cs qs m]

theorem mulPolySeries_invUnitPoly {P : ZPoly} (h0 : coeff P 0 = 1) :
    mulPolySeries P (invUnitPoly P) = unitSeries := by
  cases P with
  | nil =>
    simp [coeff] at h0
  | cons c cs =>
    have hc : c = 1 := h0
    subst hc
    funext m
    cases m with
    | zero =>
      simp [mulPolySeries, invUnitPoly, invRev, unitSeries]
    | succ m' =>
      have hnz : m' + 1 ≠ 0 := Nat.succ_ne_zero m'
      have hhead : (invRev cs (m' + 1)).headD 0 = - dotRev cs (invRev cs m') := rfl
      change 1 * (invRev cs (m' + 1)).headD 0 + mulPolySeries cs (fun k => (invRev cs k).headD 0) m' =
        if m' + 1 = 0 then 1 else 0
      simp only [hnz, ↓reduceIte, Int.one_mul, hhead, dotRev_invRev_eq_mulPolySeries cs cs m']
      omega

theorem chainProd_mul_invCharDet {n e : Nat} (he : 1 ≤ e) (A : Mat Int n)
    (hAe : matPow intCRing A e = matId intCRing n) :
    mulPolySeries (chainProd (List.replicate n e)) (invUnitPoly (charDetPoly A)) =
      ofPoly (geomDetPoly A e) := by
  have hprod := polyEq_symm (charDet_mul_geomDet_eq_chainProd he A hAe)
  have hcomm := polyEq_trans hprod (mul_comm_polyEq (charDetPoly A) (geomDetPoly A e))
  rw [mulPolySeries_congr_left hcomm (invUnitPoly (charDetPoly A))]
  rw [mulPolySeries_mul, mulPolySeries_invUnitPoly (coeff0_charDetPoly A)]
  rfl

/-- Pointwise sum of a finite list of formal power series in `ℤ[[t]]`. -/
def sumSeries : List Series → Series
  | [] => fun _ => 0
  | s :: ss => fun m => s m + sumSeries ss m

theorem mulPolySeries_sumSeries (C : ZPoly) :
    ∀ (ss : List Series),
      mulPolySeries C (sumSeries ss) = sumSeries (ss.map (mulPolySeries C))
  | [] => by
      funext m
      have h0 : ∀ (P : ZPoly) (k : Nat), mulPolySeries P (fun _ => 0) k = 0 := by
        intro P
        induction P with
        | nil => intro _; rfl
        | cons c cs ih =>
          intro k
          cases k with
          | zero => simp [mulPolySeries]
          | succ k' => simp [mulPolySeries, ih k']
      exact h0 C m
  | s :: ss => by
      funext m
      simp only [sumSeries, List.map_cons]
      rw [← mulPolySeries_sumSeries C ss]
      -- Linearity of `mulPolySeries C` in the series argument:
      have hlin : ∀ (P : ZPoly) (f g : Series) (k : Nat),
          mulPolySeries P (fun x => f x + g x) k = mulPolySeries P f k + mulPolySeries P g k := by
        intro P
        induction P with
        | nil => intro _ _ _; rfl
        | cons c cs ih =>
          intro f g k
          cases k with
          | zero => simp [mulPolySeries, Int.mul_add]
          | succ k' =>
            simp only [mulPolySeries, Int.mul_add, ih f g k']
            omega
      exact hlin C s (sumSeries ss) m

theorem isPolyBelow_sumSeries (B : Nat) :
    ∀ (ss : List Series),
      (∀ s ∈ ss, IsPolyBelow B s) →
      IsPolyBelow B (sumSeries ss)
  | [], _ => fun _ _ => rfl
  | s :: ss, h => by
      intro m hm
      simp only [sumSeries]
      rw [h s (List.mem_cons_self ..) m hm,
          isPolyBelow_sumSeries B ss (fun x hx => h x (List.mem_cons_of_mem s hx)) m hm]
      simp

/-- **Scaled Molien Series (`|G| · M_G(t) = ∑_{A ∈ G} det(I_n - t A)^{-1} ∈ ℤ[[t]]`):**
Defined directly from a finite list of `n × n` matrices `G : List (Mat Int n)`. -/
def molienScaledSeries {n : Nat} (G : List (Mat Int n)) : Series :=
  sumSeries (G.map (fun A => invUnitPoly (charDetPoly A)))

/-- **Unconditional Matrix Molien Theorem (Scaled Series `|G| · M_G(t)`):**
For ANY dimension `n ≥ 1`, exponent `e ≥ 1`, and finite family `G : List (Mat Int n)` with
`∀ A ∈ G, A^e = I_n` (with NO external `hproper` hypothesis!):
1. `(1 - t^e)^n · molienScaledSeries G` is a polynomial of strict degree `< n * e`,
2. `molienScaledSeries G` has rational denominator dividing the explicit length-`n` strict
   divisibility chain `uniformStrictChain e n` (`e ∣ 2e ∣ ... ∣ 2^{n-1} e`), and
3. `molienScaledSeries G` satisfies `(Δ_e^n a)_m = 0` and exact Newton quasi-polynomiality
   of degree `< n` on every residue class modulo `e`. -/
theorem matrix_molien_unconditional {n e : Nat} (hn : 1 ≤ n) (he : 1 ≤ e)
    (G : List (Mat Int n))
    (hpow : ∀ A ∈ G, matPow intCRing A e = matId intCRing n) :
    let M := molienScaledSeries G
    IsPolyBelow (n * e) (mulPolySeries (chainProd (List.replicate n e)) M) ∧
    (∃ ds : List Nat,
      ds.length = n ∧
      IsDivChain ds ∧
      IsStrictIncPos ds ∧
      HasDenominatorDividing (chainProd ds) M) ∧
    (∀ m : Nat, iterModDiff e n M m = 0) ∧
    (∀ c : Nat, c < e → ∀ q : Nat,
      M (q * e + c) = newtonEval n (fun q' => M (q' * e + c)) q) := by
  dsimp only
  have hproper : IsPolyBelow (n * e)
      (mulPolySeries (chainProd (List.replicate n e)) (molienScaledSeries G)) := by
    unfold molienScaledSeries
    rw [mulPolySeries_sumSeries, List.map_map]
    apply isPolyBelow_sumSeries (n * e)
    intro s hs
    rcases List.mem_map.mp hs with ⟨A, hAG, rfl⟩
    dsimp only [Function.comp]
    rw [chainProd_mul_invCharDet he A (hpow A hAG)]
    exact isPolyBelow_geomDetPoly hn he A
  have hpos_rep : ∀ d ∈ List.replicate n e, 1 ≤ d := by
    intro d hd
    rw [List.eq_of_mem_replicate hd]
    exact he
  have hunif : HasDenominatorDividing (chainProd (List.replicate n e)) (molienScaledSeries G) :=
    ⟨coeff_chainProd_zero hpos_rep, n * e, hproper⟩
  rcases invariant_ring_strict_chain_of_uniform he hunif with ⟨hlen, hdiv, hinc, hden_ds⟩
  have hmp := modular_periodic_iff he n (molienScaledSeries G)
  have hdiff := hmp.1.mp hproper
  have hqp := hmp.2.mp hdiff
  exact ⟨hproper, ⟨uniformStrictChain e n, hlen, hdiv, hinc, hden_ds⟩, hdiff, hqp⟩

theorem mulPolySeries_scale_series (C : ZPoly) (k : Int) (a : Series) :
    mulPolySeries C (fun m => k * a m) = fun m => k * mulPolySeries C a m := by
  induction C with
  | nil =>
    funext m
    simp [mulPolySeries]
  | cons c cs ih =>
    funext m
    cases m with
    | zero =>
      simp only [mulPolySeries]
      rw [← Int.mul_assoc c k (a 0), Int.mul_comm c k, Int.mul_assoc]
    | succ m' =>
      simp only [mulPolySeries, ih]
      rw [← Int.mul_assoc c k (a (m' + 1)), Int.mul_comm c k, Int.mul_assoc, Int.mul_add]

/-- **Unconditional Matrix-Group Molien Theorem (Unscaled Dimension Sequence `a_m`):**
For ANY nonempty finite matrix group `G : List (Mat Int n)` (`G ≠ []`, `n ≥ 1`, `e ≥ 1`) with
`∀ A ∈ G, A^e = I_n` and Molien dimension sequence `a : Series` satisfying Molien's character
average `|G| · a_m = ∑_{A ∈ G} [t^m] det(I_n - t A)^{-1}` (`∀ m, G.length * a m = molienScaledSeries G m`),
with **zero external `hproper` assumption**:
1. `(1 - t^e)^n · a(t)` is a polynomial of strict degree `< n * e`,
2. `a` has rational generating series with denominator dividing `(1 - t^e)^n` and dividing
   the explicit length-`n` strict divisibility chain `uniformStrictChain e n`, and
3. `a` satisfies `(Δ_e^n a)_m = 0` for all `m ≥ 0` and exact Newton quasi-polynomiality
   of degree `< n` on every residue class modulo `e`. -/
theorem matrix_group_molien_theorem {n e : Nat} (hn : 1 ≤ n) (he : 1 ≤ e)
    (G : List (Mat Int n)) (hG_ne : G ≠ [])
    (hpow : ∀ A ∈ G, matPow intCRing A e = matId intCRing n)
    (a : Series)
    (hmolien : ∀ m : Nat, (G.length : Int) * a m = molienScaledSeries G m) :
    IsPolyBelow (n * e) (mulPolySeries (chainProd (List.replicate n e)) a) ∧
    HasDenominatorDividing (chainProd (List.replicate n e)) a ∧
    (∃ ds : List Nat,
      ds.length = n ∧
      IsDivChain ds ∧
      IsStrictIncPos ds ∧
      HasDenominatorDividing (chainProd ds) a) ∧
    (∀ m : Nat, iterModDiff e n a m = 0) ∧
    (∀ c : Nat, c < e → ∀ q : Nat,
      a (q * e + c) = newtonEval n (fun q' => a (q' * e + c)) q) := by
  have hscaled := matrix_molien_unconditional hn he G hpow
  rcases hscaled with ⟨hprop_M, _, _, _⟩
  have hlen_pos : (G.length : Int) ≠ 0 := by
    cases G with
    | nil => exact False.elim (hG_ne rfl)
    | cons _ _ => simp; omega
  have hproper_a : IsPolyBelow (n * e) (mulPolySeries (chainProd (List.replicate n e)) a) := by
    intro m hm
    have hM0 : mulPolySeries (chainProd (List.replicate n e)) (molienScaledSeries G) m = 0 :=
      hprop_M m hm
    have hfn : molienScaledSeries G = fun k => (G.length : Int) * a k :=
      funext (fun k => (hmolien k).symm)
    rw [hfn, mulPolySeries_scale_series] at hM0
    dsimp only at hM0
    rcases Int.mul_eq_zero.mp hM0 with h1 | h2
    · exact False.elim (hlen_pos h1)
    · exact h2
  have hpos_rep : ∀ d ∈ List.replicate n e, 1 ≤ d := by
    intro d hd
    rw [List.eq_of_mem_replicate hd]
    exact he
  have hunif : HasDenominatorDividing (chainProd (List.replicate n e)) a :=
    ⟨coeff_chainProd_zero hpos_rep, n * e, hproper_a⟩
  rcases invariant_ring_strict_chain_of_uniform he hunif with ⟨hlen, hdiv, hinc, hden_ds⟩
  have hmp := modular_periodic_iff he n a
  have hdiff := hmp.1.mp hproper_a
  have hqp := hmp.2.mp hdiff
  exact ⟨hproper_a, hunif, ⟨uniformStrictChain e n, hlen, hdiv, hinc, hden_ds⟩, hdiff, hqp⟩

/-! ### 5. Concrete Matrix-Group Non-Vacuity Instantiation (`G = ⟨-I₂⟩` on `k[x, y]`) -/

/-- `2 × 2` negation matrix `-I₂`. -/
def negId2 : Mat Int 2 :=
  fun i j => if i.val = j.val then -1 else 0

/-- Concrete finite matrix group `G = [I₂, -I₂] ≤ GL₂(ℤ)` (`|G| = 2`, `e = 2`). -/
def groupNegId2 : List (Mat Int 2) :=
  [matId intCRing 2, negId2]

theorem groupNegId2_pow2 :
    ∀ A ∈ groupNegId2, matPow intCRing A 2 = matId intCRing 2 := by
  intro A hA
  rcases List.mem_cons.mp hA with rfl | htail
  · funext i j
    rcases i with ⟨iv, hiv⟩
    rcases j with ⟨jv, hjv⟩
    match iv, jv with
    | 0, 0 => rfl
    | 0, 1 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | iv + 2, _ => omega
    | _, jv + 2 => omega
  · rcases List.mem_singleton.mp htail with rfl
    funext i j
    rcases i with ⟨iv, hiv⟩
    rcases j with ⟨jv, hjv⟩
    match iv, jv with
    | 0, 0 => rfl
    | 0, 1 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | iv + 2, _ => omega
    | _, jv + 2 => omega

/-- Unconditional end-to-end instantiation of `matrix_molien_unconditional` on the concrete
matrix group `groupNegId2 = [I₂, -I₂] ≤ GL₂(ℤ)`. -/
theorem groupNegId2_molien_verified :
    ∃ ds : List Nat,
      ds.length = 2 ∧
      IsDivChain ds ∧
      IsStrictIncPos ds ∧
      HasDenominatorDividing (chainProd ds) (molienScaledSeries groupNegId2) :=
  (matrix_molien_unconditional (by decide : 1 ≤ 2) (by decide : 1 ≤ 2)
    groupNegId2 groupNegId2_pow2).2.1

end Conjecture00000000593
