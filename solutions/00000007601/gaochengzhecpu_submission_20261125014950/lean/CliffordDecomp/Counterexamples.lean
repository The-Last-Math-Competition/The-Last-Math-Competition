/-
  CliffordDecomp/Counterexamples.lean
  Complete formal refutations of Conjecture 00000007601 across all multivector
  and metric regimes over exact rational arithmetic `ℚ = RatQ` (and for general `K`):

  1. General Vector–Bivector Parity Reversal Theorem (`vec_bivector_reversal`):
     For ANY `n ≥ 2`, ANY quadratic form `q`, ANY vector `u ∈ Cl^1`, and ANY bivector
     `B ∈ Cl^2`, `symPart(u, B) = u ∧ B` (outer!) and `antisymPart(u, B) = u ⌟ B` (inner!).
  2. Counterexample 1 (`cl2_vec_bivector_counterexample` in `Cl_{2,0}(ℚ)`):
     `A = e_1` (grade 1), `B = e_1 e_2` (grade 2):
     `symPart(A, B) = 0 ≠ e_2 = leftContract(A, B) = hestenesInner(A, B)`, and
     `antisymPart(A, B) = e_2 ≠ 0 = A ∧ B`.
  3. Counterexample 2 (`cl3_bivector_vec_counterexample` & `cl3_bivector_comm_counterexample` in `Cl_{3,0}(ℚ)`):
     (a) `A = e_1 e_2` (grade 2), `B = e_3` (grade 1):
         `symPart(A, B) = e_1 e_2 e_3 = A ∧ B ≠ 0` while `antisymPart(A, B) = 0` and all
         inner contractions vanish; moreover `⟨A, B⟩_{Q~} = 0` yet `symPart(A, B) ≠ 0`.
     (b) `B_1 = e_1 e_2`, `B_2 = e_2 e_3` (both grade 2):
         all inner contractions AND `B_1 ∧ B_2` vanish, yet `antisymPart(B_1, B_2) = e_1 e_3 ≠ 0`.
  4. Counterexample 3 (`cl4_bivector_three_part_counterexample` in `Cl_{4,0}(ℚ)`):
     `B_1 = e_1 e_2`, `B_2 = e_1 e_2 + e_2 e_3 + e_3 e_4` (both grade 2):
     `B_1 B_2 = -1 + e_1 e_3 + e_1 e_2 e_3 e_4` has three nonzero grades (0, 2, 4);
     `symPart(B_1, B_2) = -1 + e_1 e_2 e_3 e_4` mixes nonzero grade-0 inner contraction AND
     nonzero grade-4 outer product, while `antisymPart(B_1, B_2) = e_1 e_3` (grade 2) is neither!
  5. Counterexample 4 (Metric Orthogonality Refutations):
     (a) `cl2_inhomogeneous_nonorthogonal`: Even for positive-definite Euclidean `Cl_{2,0}(ℚ)`,
         `X = 1 + e_1` and `Y = e_2 + e_1 e_2` yield `symPart(X, Y) = antisymPart(X, Y) = e_2 + e_1 e_2 ≠ 0`
         with `⟨symPart, antisymPart⟩_{Q~} = 2 ≠ 0` and `⟨XY, XY⟩_{Q~} = 8 ≠ 4 = ⟨S, S⟩_{Q~} + ⟨A, A⟩_{Q~}`.
     (b) `cl11_indefinite_isotropic_decomp` & `cl111_self_orthogonal_bivector`:
         For indefinite `Cl_{1,1}(ℚ)` (`q = (1, -1)`), `u = e_1 + e_2`, `v = e_1` gives nonzero `u v`
         with `⟨u v, u v⟩_{Q~} = 0` (`⟨S, S⟩_{Q~} = 1`, `⟨A, A⟩_{Q~} = -1`); and in `Cl_{1,1,1}(ℚ)`
         (`q = (1, -1, 1)`), `u = e_1 + e_2`, `v = e_3` gives `A = u ∧ v ≠ 0` self-orthogonal
         (`⟨A, A⟩_{Q~} = 0` and `⟨A A⟩_0 = 0`).
  6. Master Formal Disproof (`clifford_sym_antisym_conjecture_false`).
-/
import CliffordDecomp.PositiveTheorems

namespace CliffordDecomp
namespace ClSpace

/-! ### Exact Boolean Equality Reflective Checker on `ClSpace RatQ n` -/

def ratEqBool (a b : RatQ) : Bool :=
  RatQ.isZero (a - b)

theorem ratEqBool_iff (a b : RatQ) : ratEqBool a b = true ↔ a = b := by
  unfold ratEqBool
  rw [RatQ.isZero_iff]
  constructor
  · intro h
    have h1 := congrArg (· + b) h
    dsimp at h1
    rw [CommRing2.sub_eq_add_neg, CommRing2.add_assoc, CommRing2.neg_add_cancel,
        CommRing2.add_zero, CommRing2.zero_add] at h1
    exact h1
  · intro h
    rw [h, CommRing2.sub_self]

def clEqBool : {n : Nat} → ClSpace RatQ n → ClSpace RatQ n → Bool
  | 0, a, b => ratEqBool a b
  | _ + 1, (x0, x1), (y0, y1) => clEqBool x0 y0 && clEqBool x1 y1

theorem clEqBool_iff {n : Nat} (x y : ClSpace RatQ n) : clEqBool x y = true ↔ x = y := by
  induction n with
  | zero => exact ratEqBool_iff x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    dsimp [clEqBool]
    rw [Bool.and_eq_true, ih x0 y0, ih x1 y1]
    exact ⟨fun ⟨h0, h1⟩ => Prod.ext h0 h1, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem cl_eq_of_bool {n : Nat} {x y : ClSpace RatQ n} (h : clEqBool x y = true) : x = y :=
  (clEqBool_iff x y).mp h

theorem cl_ne_of_bool {n : Nat} {x y : ClSpace RatQ n} (h : clEqBool x y = false) : x ≠ y := by
  intro heq
  rw [(clEqBool_iff x y).mpr heq] at h
  contradiction

theorem rat_eq_of_bool {a b : RatQ} (h : ratEqBool a b = true) : a = b :=
  (ratEqBool_iff a b).mp h

theorem rat_ne_of_bool {a b : RatQ} (h : ratEqBool a b = false) : a ≠ b := by
  intro heq
  rw [(ratEqBool_iff a b).mpr heq] at h
  contradiction

/-! ### 1. General Vector–Bivector Parity Reversal Theorem -/

section GeneralReversal
variable {K : Type u} [CommRing2 K]

private theorem odd_element_even_grade_zero {n : Nat} {z : ClSpace K n}
    (hodd : invol z = neg z) (k : Nat) :
    gradeProj (2 * k) z = zero := by
  have h1 : gradeProj (2 * k) (invol z) = gradeProj (2 * k) (neg z) := congrArg (gradeProj (2 * k)) hodd
  rw [gradeProj_invol, invol_gradeProj, CommRing2.signPow_even, one_smul, gradeProj_neg] at h1
  have h2 : add (gradeProj (2 * k) z) (gradeProj (2 * k) z) = zero := by
    calc
      add (gradeProj (2 * k) z) (gradeProj (2 * k) z)
        = add (gradeProj (2 * k) z) (neg (gradeProj (2 * k) z)) := by
            conv => lhs; rhs; rw [h1]
      _ = zero := add_neg_cancel _
  have h3 := congrArg (smul (CommRing2.half : K)) h2
  rw [half_smul_add_self, smul_zero] at h3
  exact h3

private theorem sumUpTo_gradeProj_le3 {n : Nat} (z : ClSpace K n)
    (hg0 : gradeProj 0 z = zero) (hg2 : gradeProj 2 z = zero)
    (hgt3 : ∀ m, 3 < m → gradeProj m z = zero) :
    z = add (gradeProj 1 z) (gradeProj 3 z) := by
  conv => lhs; rw [← grade_decomp_complete z]
  have hsum : ∀ m,
      sumUpTo (fun k => gradeProj k z) m =
      if m = 0 then zero
      else if m = 1 then gradeProj 1 z
      else if m = 2 then gradeProj 1 z
      else add (gradeProj 1 z) (gradeProj 3 z) := by
    intro m
    induction m with
    | zero =>
      dsimp [sumUpTo]; exact hg0
    | succ m ihm =>
      dsimp [sumUpTo]
      rw [ihm]
      cases m with
      | zero =>
        dsimp; exact zero_add _
      | succ m1 =>
        cases m1 with
        | zero =>
          dsimp; rw [hg2, add_zero]
        | succ m2 =>
          cases m2 with
          | zero => dsimp
          | succ m3 =>
            dsimp
            rw [hgt3 (m3 + 1 + 1 + 1 + 1) (by omega), add_zero]
  rw [hsum n]
  by_cases hn0 : n = 0
  · subst hn0
    dsimp
    rw [gradeProj_of_gt (by omega : 0 < 1) z, gradeProj_of_gt (by omega : 0 < 3) z, add_zero]
  · rw [if_neg hn0]
    by_cases hn1 : n = 1
    · subst hn1
      dsimp
      rw [gradeProj_of_gt (by omega : 1 < 3) z, add_zero]
    · rw [if_neg hn1]
      by_cases hn2 : n = 2
      · subst hn2
        dsimp
        rw [gradeProj_of_gt (by omega : 2 < 3) z, add_zero]
      · rw [if_neg hn2]

/-- **Universal Vector–Bivector Parity Reversal Theorem:**
    In ANY Clifford algebra `Cl(n, q)` with `n ≥ 2`, for ANY grade-1 vector `u` and
    ANY grade-2 bivector `B`:
    - `symPart(u, B) = u ∧ B` (**symmetric part is the outer product!**), and
    - `antisymPart(u, B) = leftContract(u, B) = hestenesInner(u, B)` (**antisymmetric part is the inner product!**). -/
theorem vec_bivector_reversal {n : Nat} (hn : 2 ≤ n) (q : Fin n → K)
    {u b : ClSpace K n} (hu : HasGrade 1 u) (hb : HasGrade 2 b) :
    symPart q u b = wedge u b ∧
    antisymPart q u b = leftContract q u b ∧
    antisymPart q u b = hestenesInner q u b := by
  have hu_inv : invol u = neg u := by
    rw [← hu, invol_gradeProj, hu]
    dsimp [CommRing2.signPow]
    rw [neg_smul, one_smul]
  have hb_inv : invol b = b := by
    rw [← hb, invol_gradeProj, hb, CommRing2.signPow_even 1, one_smul]
  have hodd_ub : invol (mul q u b) = neg (mul q u b) := by
    rw [invol_mul, hu_inv, hb_inv, neg_mul]
  have hodd_bu : invol (mul q b u) = neg (mul q b u) := by
    rw [invol_mul, hb_inv, hu_inv, mul_neg]
  have htop_ub := homogeneous_mul_top_grade q hu hb
  have htop_bu := homogeneous_mul_top_grade q hb hu
  have hub_decomp : mul q u b = add (gradeProj 1 (mul q u b)) (gradeProj 3 (mul q u b)) :=
    sumUpTo_gradeProj_le3 (mul q u b)
      (odd_element_even_grade_zero hodd_ub 0)
      (odd_element_even_grade_zero hodd_ub 1)
      (fun m hm => htop_ub.1 m (by omega))
  have hbu_decomp : mul q b u = add (gradeProj 1 (mul q b u)) (gradeProj 3 (mul q b u)) :=
    sumUpTo_gradeProj_le3 (mul q b u)
      (odd_element_even_grade_zero hodd_bu 0)
      (odd_element_even_grade_zero hodd_bu 1)
      (fun m hm => htop_bu.1 m (by omega))
  have hswap3 : gradeProj 3 (mul q b u) = gradeProj 3 (mul q u b) := by
    have hp := gradeProj_mul_parity q (r := 1) (s := 2) (m := 3) (j := 0) rfl hu hb
    rw [CommRing2.signPow_even 1, one_smul] at hp
    exact hp
  have hswap1 : gradeProj 1 (mul q b u) = neg (gradeProj 1 (mul q u b)) := by
    have hp := gradeProj_mul_parity q (r := 1) (s := 2) (m := 1) (j := 1) rfl hu hb
    have hsign : CommRing2.signPow K (1 * 2 + 1) = -(1 : K) := CommRing2.signPow_odd 1
    rw [hsign, neg_smul, one_smul] at hp
    exact hp
  have hsym : symPart q u b = wedge u b := by
    unfold symPart anticomm
    rw [hub_decomp, hbu_decomp, hswap1, hswap3]
    have hcancel :
        add (add (gradeProj 1 (mul q u b)) (gradeProj 3 (mul q u b)))
            (add (neg (gradeProj 1 (mul q u b))) (gradeProj 3 (mul q u b))) =
        add (gradeProj 3 (mul q u b)) (gradeProj 3 (mul q u b)) := by
      calc
        add (add (gradeProj 1 (mul q u b)) (gradeProj 3 (mul q u b)))
            (add (neg (gradeProj 1 (mul q u b))) (gradeProj 3 (mul q u b)))
          = add (add (gradeProj 1 (mul q u b)) (neg (gradeProj 1 (mul q u b))))
                (add (gradeProj 3 (mul q u b)) (gradeProj 3 (mul q u b))) := by
              simp only [add_assoc, add_left_comm, add_comm]
        _ = add (gradeProj 3 (mul q u b)) (gradeProj 3 (mul q u b)) := by
              rw [add_neg_cancel, zero_add]
    rw [hcancel, half_smul_add_self]
    exact htop_ub.2.1
  have hanti : antisymPart q u b = gradeProj 1 (mul q u b) := by
    conv => lhs; unfold antisymPart comm sub; rw [hub_decomp, hbu_decomp, hswap1, hswap3, neg_add, neg_neg]
    have hcancel :
        add (add (gradeProj 1 (mul q u b)) (gradeProj 3 (mul q u b)))
            (add (gradeProj 1 (mul q u b)) (neg (gradeProj 3 (mul q u b)))) =
        add (gradeProj 1 (mul q u b)) (gradeProj 1 (mul q u b)) := by
      calc
        add (add (gradeProj 1 (mul q u b)) (gradeProj 3 (mul q u b)))
            (add (gradeProj 1 (mul q u b)) (neg (gradeProj 3 (mul q u b))))
          = add (add (gradeProj 1 (mul q u b)) (gradeProj 1 (mul q u b)))
                (add (gradeProj 3 (mul q u b)) (neg (gradeProj 3 (mul q u b)))) := by
              simp only [add_assoc, add_left_comm, add_comm]
        _ = add (gradeProj 1 (mul q u b)) (gradeProj 1 (mul q u b)) := by
              rw [add_neg_cancel, add_zero]
    rw [hcancel, half_smul_add_self]
  have hlc : leftContract q u b = gradeProj 1 (mul q u b) := by
    rw [leftContract_of_hasGrade q (by omega) hn hu hb, if_pos (by decide : 1 ≤ 2)]
  have hhi : hestenesInner q u b = gradeProj 1 (mul q u b) := by
    rw [hestenesInner_of_hasGrade q (Nat.le_refl 1) (by omega) (by decide) hn hu hb,
        if_pos (by decide : 1 ≤ 2)]
  exact ⟨hsym, by rw [hanti, hlc], by rw [hanti, hhi]⟩

end GeneralReversal

/-! ### 2. Concrete Basis Blades and Signatures over `ℚ` -/

def qEuclid3 : Fin 3 → RatQ := fun _ => 1
def qEuclid4 : Fin 4 → RatQ := fun _ => 1

def qSplit11 : Fin 2 → RatQ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -(1 : RatQ)

def qIndef111 : Fin 3 → RatQ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -(1 : RatQ)
  | ⟨2, _⟩ => 1

/-- Standard basis generators `e_i` (0-indexed) in `ClSpace RatQ n`. -/
def eGen (n : Nat) (i : Fin n) : ClSpace RatQ n :=
  basisVec i

/-! ### Counterexample 1: `Cl_{2,0}(ℚ)` Vector × Bivector -/

/-- **Counterexample 1 (`Cl_{2,0}(ℚ)`, `n = 2`, positive-definite Euclidean metric):**
    Let `A = e_1` (grade 1) and `B = e_1 e_2` (grade 2).
    - `symPart(A, B) = 0`, whereas `leftContract(A, B) = hestenesInner(A, B) = e_2 ≠ 0`
    - `antisymPart(A, B) = e_2 ≠ 0`, whereas `A ∧ B = 0`!
    Here the antisymmetric commutator IS the inner contraction, while the symmetric part vanishes! -/
theorem cl2_vec_bivector_counterexample :
    let e1 := eGen 2 ⟨0, by decide⟩
    let e2 := eGen 2 ⟨1, by decide⟩
    let B := mul qEuclid2 e1 e2
    HasGrade 1 e1 ∧
    HasGrade 2 B ∧
    mul qEuclid2 e1 B = e2 ∧
    mul qEuclid2 B e1 = neg e2 ∧
    symPart qEuclid2 e1 B = zero ∧
    antisymPart qEuclid2 e1 B = e2 ∧
    wedge e1 B = zero ∧
    leftContract qEuclid2 e1 B = e2 ∧
    hestenesInner qEuclid2 e1 B = e2 ∧
    symPart qEuclid2 e1 B ≠ leftContract qEuclid2 e1 B ∧
    symPart qEuclid2 e1 B ≠ hestenesInner qEuclid2 e1 B ∧
    antisymPart qEuclid2 e1 B ≠ wedge e1 B := by
  refine ⟨cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_eq_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl⟩

/-! ### Counterexample 2: `Cl_{3,0}(ℚ)` Bivector × Vector & Bivector × Bivector -/

/-- **Counterexample 2a (`Cl_{3,0}(ℚ)`, `n = 3`, Bivector × Vector):**
    Let `A = e_1 e_2` (grade 2) and `B = e_3` (grade 1).
    - `A B = B A = e_1 e_2 e_3 ≠ 0`
    - `symPart(A, B) = e_1 e_2 e_3 = A ∧ B ≠ 0` (**symmetric part is pure outer product!**)
    - `antisymPart(A, B) = 0`, and all inner contractions (`leftContract`, `rightContract`, `hestenesInner`) vanish!
    - Moreover `⟨A, B⟩_{Q~} = 0` (mutually metric-orthogonal), yet `symPart(A, B) ≠ 0`! -/
theorem cl3_bivector_vec_counterexample :
    let e1 := eGen 3 ⟨0, by decide⟩
    let e2 := eGen 3 ⟨1, by decide⟩
    let e3 := eGen 3 ⟨2, by decide⟩
    let A := mul qEuclid3 e1 e2
    let e123 := mul qEuclid3 A e3
    HasGrade 2 A ∧
    HasGrade 1 e3 ∧
    symPart qEuclid3 A e3 = e123 ∧
    wedge A e3 = e123 ∧
    e123 ≠ zero ∧
    antisymPart qEuclid3 A e3 = zero ∧
    leftContract qEuclid3 A e3 = zero ∧
    rightContract qEuclid3 A e3 = zero ∧
    hestenesInner qEuclid3 A e3 = zero ∧
    metricForm qEuclid3 A e3 = 0 ∧
    symPart qEuclid3 A e3 ≠ rightContract qEuclid3 A e3 ∧
    symPart qEuclid3 A e3 ≠ hestenesInner qEuclid3 A e3 ∧
    antisymPart qEuclid3 A e3 ≠ wedge A e3 := by
  refine ⟨cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_ne_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_eq_of_bool rfl, rat_eq_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl,
          cl_ne_of_bool rfl⟩

/-- **Counterexample 2b (`Cl_{3,0}(ℚ)`, `n = 3`, Bivector Commutator):**
    Let `B_1 = e_1 e_2` and `B_2 = e_2 e_3` (both grade 2).
    All inner contractions AND the outer product `B_1 ∧ B_2` vanish, yet the antisymmetric
    commutator `antisymPart(B_1, B_2) = e_1 e_3 ≠ 0` (the `so(3)` Lie bracket in grade 2)! -/
theorem cl3_bivector_comm_counterexample :
    let e1 := eGen 3 ⟨0, by decide⟩
    let e2 := eGen 3 ⟨1, by decide⟩
    let e3 := eGen 3 ⟨2, by decide⟩
    let B1 := mul qEuclid3 e1 e2
    let B2 := mul qEuclid3 e2 e3
    let e13 := mul qEuclid3 e1 e3
    HasGrade 2 B1 ∧
    HasGrade 2 B2 ∧
    symPart qEuclid3 B1 B2 = zero ∧
    antisymPart qEuclid3 B1 B2 = e13 ∧
    e13 ≠ zero ∧
    wedge B1 B2 = zero ∧
    leftContract qEuclid3 B1 B2 = zero ∧
    rightContract qEuclid3 B1 B2 = zero ∧
    hestenesInner qEuclid3 B1 B2 = zero ∧
    antisymPart qEuclid3 B1 B2 ≠ wedge B1 B2 := by
  refine ⟨cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_ne_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_eq_of_bool rfl, cl_ne_of_bool rfl⟩

/-! ### Counterexample 3: `Cl_{4,0}(ℚ)` Three-Grade Bivector Product -/

/-- **Counterexample 3 (`Cl_{4,0}(ℚ)`, `n = 4`, Three-Part Bivector Decomposition):**
    Let `B_1 = e_1 e_2` and `B_2 = e_1 e_2 + e_2 e_3 + e_3 e_4` (both homogeneous of grade 2).
    - `B_1 B_2 = -1 + e_1 e_3 + e_1 e_2 e_3 e_4` has nonzero components in grades `0, 2, 4`!
    - `symPart(B_1, B_2) = -1 + e_1 e_2 e_3 e_4 = hestenesInner(B_1, B_2) + (B_1 ∧ B_2)`
      simultaneously mixes a nonzero grade-0 inner product (`-1`) AND a nonzero grade-4 outer
      product (`e_1 e_2 e_3 e_4`)!
    - `antisymPart(B_1, B_2) = e_1 e_3` (pure grade 2) has zero inner part and zero outer part! -/
theorem cl4_bivector_three_part_counterexample :
    let e1 := eGen 4 ⟨0, by decide⟩
    let e2 := eGen 4 ⟨1, by decide⟩
    let e3 := eGen 4 ⟨2, by decide⟩
    let e4 := eGen 4 ⟨3, by decide⟩
    let B1 := mul qEuclid4 e1 e2
    let B2 := add (add (mul qEuclid4 e1 e2) (mul qEuclid4 e2 e3)) (mul qEuclid4 e3 e4)
    let e13 := mul qEuclid4 e1 e3
    let e1234 := mul qEuclid4 (mul qEuclid4 e1 e2) (mul qEuclid4 e3 e4)
    HasGrade 2 B1 ∧
    HasGrade 2 B2 ∧
    hestenesInner qEuclid4 B1 B2 = scalar (-(1 : RatQ)) ∧
    wedge B1 B2 = e1234 ∧
    symPart qEuclid4 B1 B2 = add (scalar (-(1 : RatQ))) e1234 ∧
    antisymPart qEuclid4 B1 B2 = e13 ∧
    gradeProj 0 (symPart qEuclid4 B1 B2) ≠ zero ∧
    gradeProj 4 (symPart qEuclid4 B1 B2) ≠ zero ∧
    gradeProj 2 (antisymPart qEuclid4 B1 B2) ≠ zero ∧
    symPart qEuclid4 B1 B2 ≠ hestenesInner qEuclid4 B1 B2 ∧
    symPart qEuclid4 B1 B2 ≠ wedge B1 B2 ∧
    antisymPart qEuclid4 B1 B2 ≠ wedge B1 B2 := by
  refine ⟨cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_eq_of_bool rfl,
          cl_eq_of_bool rfl, cl_eq_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl,
          cl_ne_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl, cl_ne_of_bool rfl⟩

/-! ### Counterexample 4: Refutations of Metric Orthogonality of the Decomposition -/

/-- **Counterexample 4a (`Cl_{2,0}(ℚ)`, Positive-Definite Metric, Inhomogeneous Multivectors):**
    Even when `Q` is positive definite (`metricForm_pos_of_ne_zero`), for `X = 1 + e_1` and
    `Y = e_2 + e_1 e_2` in `Cl_{2,0}(ℚ)`:
    - `X Y = 2 (e_2 + e_1 e_2)` and `Y X = 0`
    - `symPart(X, Y) = antisymPart(X, Y) = e_2 + e_1 e_2 ≠ 0` (collinear, identical!)
    - `⟨symPart(X, Y), antisymPart(X, Y)⟩_{Q~} = 2 ≠ 0`
    - Pythagorean norm additivity fails: `⟨XY, XY⟩_{Q~} = 8 ≠ 4 = ⟨S, S⟩_{Q~} + ⟨A, A⟩_{Q~}`! -/
theorem cl2_inhomogeneous_nonorthogonal :
    let e1 := eGen 2 ⟨0, by decide⟩
    let e2 := eGen 2 ⟨1, by decide⟩
    let X := add one e1
    let Y := add e2 (mul qEuclid2 e1 e2)
    let S := symPart qEuclid2 X Y
    let A := antisymPart qEuclid2 X Y
    (∀ i, RatQ.IsPos (qEuclid2 i)) ∧
    S = A ∧
    S ≠ zero ∧
    metricForm qEuclid2 S A = 2 ∧
    metricForm qEuclid2 S A ≠ 0 ∧
    metricForm qEuclid2 (mul qEuclid2 X Y) (mul qEuclid2 X Y) ≠
      metricForm qEuclid2 S S + metricForm qEuclid2 A A := by
  refine ⟨?_, cl_eq_of_bool rfl, cl_ne_of_bool rfl, rat_eq_of_bool rfl,
          rat_ne_of_bool rfl, rat_ne_of_bool rfl⟩
  intro i
  match i with
  | ⟨0, _⟩ => change (0 : Int) < 1; decide
  | ⟨1, _⟩ => change (0 : Int) < 1; decide

/-- **Counterexample 4b (`Cl_{1,1}(ℚ)` & `Cl_{1,1,1}(ℚ)`, Indefinite Metrics on Grade-1 Vectors):**
    (i) In `Cl_{1,1}(ℚ)` (`q = (1, -1)`), vectors `u = e_1 + e_2` and `v = e_1` yield
        `u v = 1 - e_1 e_2 ≠ 0` with `⟨S, S⟩_{Q~} = 1`, `⟨A, A⟩_{Q~} = -1`, and `⟨u v, u v⟩_{Q~} = 0`.
    (ii) In `Cl_{1,1,1}(ℚ)` (`q = (1, -1, 1)`), vectors `u' = e_1 + e_2` and `v' = e_3` yield
         nonzero antisymmetric part `A' = u' ∧ v' ≠ 0` which is **self-orthogonal** under BOTH
         `metricForm` (`⟨A', A'⟩_{Q~} = 0`) and `scalarTrace` (`⟨A' A'⟩_0 = 0`). -/
theorem indefinite_metric_grade1_counterexamples :
    let f1 := eGen 2 ⟨0, by decide⟩
    let f2 := eGen 2 ⟨1, by decide⟩
    let u := add f1 f2
    let v := f1
    let S := symPart qSplit11 u v
    let A := antisymPart qSplit11 u v
    let g1 := eGen 3 ⟨0, by decide⟩
    let g2 := eGen 3 ⟨1, by decide⟩
    let g3 := eGen 3 ⟨2, by decide⟩
    let u' := add g1 g2
    let v' := g3
    let A' := antisymPart qIndef111 u' v'
    mul qSplit11 u v ≠ zero ∧
    metricForm qSplit11 S S = 1 ∧
    metricForm qSplit11 A A = -(1 : RatQ) ∧
    metricForm qSplit11 (mul qSplit11 u v) (mul qSplit11 u v) = 0 ∧
    A' ≠ zero ∧
    metricForm qIndef111 A' A' = 0 ∧
    scalarTrace qIndef111 A' A' = 0 := by
  refine ⟨cl_ne_of_bool rfl, rat_eq_of_bool rfl, rat_eq_of_bool rfl, rat_eq_of_bool rfl,
          cl_ne_of_bool rfl, rat_eq_of_bool rfl, rat_eq_of_bool rfl⟩

/-! ### Master Formal Statement and Disproof of Conjecture 00000007601 -/

/-- Formalization of the universal Clifford product decomposition conjecture (00000007601):
    For every dimension `n`, quadratic form `q : Fin n → ℚ`, and elements `X, Y ∈ Cl(n, q)`
    (even under the charitable restriction that `q` is positive definite or on general elements),
    the commutator/anticommutator decomposition `XY = symPart(X, Y) + antisymPart(X, Y)` satisfies:
    (1) `symPart(X, Y)` equals a standard inner contraction (`leftContract`, `rightContract`, or `hestenesInner`),
    (2) `antisymPart(X, Y)` equals the outer product `X ∧ Y`, and
    (3) `⟨symPart(X, Y), antisymPart(X, Y)⟩_{Q~} = 0`. -/
def CliffordProductDecompConjecture : Prop :=
  ∀ (n : Nat) (q : Fin n → RatQ) (X Y : ClSpace RatQ n),
    mul q X Y = add (symPart q X Y) (antisymPart q X Y) ∧
    (symPart q X Y = leftContract q X Y ∨
     symPart q X Y = rightContract q X Y ∨
     symPart q X Y = hestenesInner q X Y) ∧
    antisymPart q X Y = wedge X Y ∧
    metricForm q (symPart q X Y) (antisymPart q X Y) = 0

/-- Charitable homogeneous-blade variant restricting `q` to positive-definite Euclidean metrics
    and `X, Y` to homogeneous multivectors of nonzero grades `1 ≤ r, s ≤ n`. -/
def CliffordHomogeneousDecompConjecture : Prop :=
  ∀ (n : Nat) (q : Fin n → RatQ),
    (∀ i, RatQ.IsPos (q i)) →
    ∀ (r s : Nat), 1 ≤ r → r ≤ n → 1 ≤ s → s ≤ n →
    ∀ (X Y : ClSpace RatQ n), HasGrade r X → HasGrade s Y →
      (symPart q X Y = leftContract q X Y ∨
       symPart q X Y = rightContract q X Y ∨
       symPart q X Y = hestenesInner q X Y) ∧
      antisymPart q X Y = wedge X Y

/-- **Main Refutation Theorem (Homogeneous Euclidean Version):** Even when `q` is positive definite
    and `X, Y` are homogeneous blades (`n = 2`, `r = 1`, `s = 2`), the conjecture is FALSE. -/
theorem clifford_homogeneous_decomp_conjecture_false : ¬ CliffordHomogeneousDecompConjecture := by
  intro hConj
  let e1 := eGen 2 ⟨0, by decide⟩
  let e2 := eGen 2 ⟨1, by decide⟩
  let B := mul qEuclid2 e1 e2
  have hpos : ∀ i : Fin 2, RatQ.IsPos (qEuclid2 i) := by
    intro i
    match i with
    | ⟨0, _⟩ => change (0 : Int) < 1; decide
    | ⟨1, _⟩ => change (0 : Int) < 1; decide
  have h := hConj 2 qEuclid2 hpos 1 2 (by decide) (by decide) (by decide) (by decide)
                  e1 B (cl_eq_of_bool rfl) (cl_eq_of_bool rfl)
  exact cl_ne_of_bool rfl h.2

/-- **Main Refutation Theorem (Full Conjecture 00000007601):** Conjecture 00000007601 is FALSE. -/
theorem clifford_product_decomp_conjecture_false : ¬ CliffordProductDecompConjecture := by
  intro hConj
  let e1 := eGen 2 ⟨0, by decide⟩
  let e2 := eGen 2 ⟨1, by decide⟩
  let B := mul qEuclid2 e1 e2
  have h := hConj 2 qEuclid2 e1 B
  exact cl_ne_of_bool rfl h.2.2.1

end ClSpace
end CliffordDecomp
