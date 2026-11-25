/-
  CliffordDecomp/GradingAndProducts.lean
  Canonical Z-grading (as a module), commutator/anticommutator symmetric-antisymmetric
  product decomposition, exterior (wedge) product, inner contractions (left, right,
  Hestenes), and metric bilinear forms on `ClSpace K n`.
-/
import CliffordDecomp.Algebra

namespace CliffordDecomp
namespace ClSpace

/-- Triangular number `k * (k - 1) / 2` governing the reversion sign `(-1)^{k(k-1)/2}`. -/
def triNum : Nat → Nat
  | 0 => 0
  | k + 1 => triNum k + k

theorem two_mul_triNum (k : Nat) : 2 * triNum k = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [triNum]
    have h : 2 * (triNum k + k) = 2 * triNum k + 2 * k := Nat.left_distrib 2 (triNum k) k
    rw [h, ih]
    cases k with
    | zero => rfl
    | succ m =>
      change (m + 1) * m + 2 * (m + 1) = (m + 2) * (m + 1)
      rw [Nat.mul_comm (m + 1) m, ← Nat.right_distrib m 2 (m + 1)]

section Grading
variable {K : Type u} [CommRing2 K]

/-- Canonical grade-`k` projection `⟨X⟩_k` on `ClSpace K n`. -/
def gradeProj : {n : Nat} → Nat → ClSpace K n → ClSpace K n
  | 0, 0, a => a
  | 0, _ + 1, _ => (0 : K)
  | _ + 1, 0, (x0, _) => (gradeProj 0 x0, zero)
  | _ + 1, k + 1, (x0, x1) => (gradeProj (k + 1) x0, gradeProj k x1)

/-- Predicate stating that `x` is homogeneous of grade `k`. -/
def HasGrade {n : Nat} (k : Nat) (x : ClSpace K n) : Prop :=
  gradeProj k x = x

theorem gradeProj_zero_elem {n : Nat} (k : Nat) :
    gradeProj k (zero : ClSpace K n) = zero := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => exact Prod.ext (ih 0) rfl
    | succ k => exact Prod.ext (ih (k + 1)) (ih k)

theorem gradeProj_add {n : Nat} (k : Nat) (x y : ClSpace K n) :
    gradeProj k (add x y) = add (gradeProj k x) (gradeProj k y) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact (CommRing2.add_zero 0).symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    cases k with
    | zero => exact Prod.ext (ih 0 x0 y0) (add_zero zero).symm
    | succ k => exact Prod.ext (ih (k + 1) x0 y0) (ih k x1 y1)

theorem gradeProj_neg {n : Nat} (k : Nat) (x : ClSpace K n) :
    gradeProj k (neg x) = neg (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact CommRing2.neg_zero.symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero => exact Prod.ext (ih 0 x0) neg_zero.symm
    | succ k => exact Prod.ext (ih (k + 1) x0) (ih k x1)

theorem gradeProj_smul {n : Nat} (k : Nat) (c : K) (x : ClSpace K n) :
    gradeProj k (smul c x) = smul c (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact (CommRing2.mul_zero c).symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero => exact Prod.ext (ih 0 x0) (smul_zero c).symm
    | succ k => exact Prod.ext (ih (k + 1) x0) (ih k x1)

theorem gradeProj_zero_eq_scalar {n : Nat} (x : ClSpace K n) :
    gradeProj 0 x = scalar (scalarPart x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    exact Prod.ext (ih x0) rfl

theorem gradeProj_scalar_zero {n : Nat} (c : K) :
    gradeProj 0 (scalar (n := n) c) = scalar c := by
  rw [gradeProj_zero_eq_scalar, scalarPart_scalar]

theorem gradeProj_scalar_succ {n : Nat} (k : Nat) (c : K) :
    gradeProj (k + 1) (scalar (n := n) c) = zero := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    dsimp [scalar, gradeProj]
    exact Prod.ext (ih k) (gradeProj_zero_elem k)

theorem gradeProj_of_gt {n k : Nat} (h : n < k) (x : ClSpace K n) :
    gradeProj k x = zero := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero => omega
    | succ k =>
      exact Prod.ext (ih (by omega) x0) (ih (by omega) x1)

theorem gradeProj_idem {n : Nat} (k : Nat) (x : ClSpace K n) :
    gradeProj k (gradeProj k x) = gradeProj k x := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero => exact Prod.ext (ih 0 x0) rfl
    | succ k => exact Prod.ext (ih (k + 1) x0) (ih k x1)

theorem gradeProj_orthog {n : Nat} {j k : Nat} (hjk : j ≠ k) (x : ClSpace K n) :
    gradeProj j (gradeProj k x) = zero := by
  induction n generalizing j k with
  | zero =>
    cases j with
    | zero =>
      cases k with
      | zero => exact absurd rfl hjk
      | succ k => rfl
    | succ j => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases j with
    | zero =>
      cases k with
      | zero => exact absurd rfl hjk
      | succ k => exact Prod.ext (ih (by omega) x0) rfl
    | succ j =>
      cases k with
      | zero => exact Prod.ext (ih (by omega) x0) (gradeProj_zero_elem j)
      | succ k => exact Prod.ext (ih (by omega) x0) (ih (by omega) x1)

/-- Finite sum `∑_{k=0}^m f(k)` in `ClSpace K n`. -/
def sumUpTo {n : Nat} (f : Nat → ClSpace K n) : Nat → ClSpace K n
  | 0 => f 0
  | m + 1 => add (sumUpTo f m) (f (m + 1))

/-- **Completeness of Grade Decomposition:** `X = ∑_{k=0}^n ⟨X⟩_k`. -/
theorem grade_decomp_complete {n : Nat} (x : ClSpace K n) :
    sumUpTo (fun k => gradeProj k x) n = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    have hsplit : ∀ m : Nat,
        sumUpTo (n := n + 1) (fun k => gradeProj k ((x0, x1) : ClSpace K (n + 1))) (m + 1) =
        ((sumUpTo (fun k => gradeProj k x0) (m + 1), sumUpTo (fun k => gradeProj k x1) m) : ClSpace K (n + 1)) := by
      intro m
      induction m with
      | zero =>
        dsimp [sumUpTo, gradeProj, add]
        exact Prod.ext rfl (zero_add (gradeProj 0 x1))
      | succ m ihm =>
        change add (sumUpTo (n := n + 1) (fun k => gradeProj k (x0, x1)) (m + 1))
                   (gradeProj (m + 2) (x0, x1)) =
               (add (sumUpTo (fun k => gradeProj k x0) (m + 1)) (gradeProj (m + 2) x0),
                add (sumUpTo (fun k => gradeProj k x1) m) (gradeProj (m + 1) x1))
        rw [ihm]
        rfl
    rw [hsplit n]
    dsimp [sumUpTo]
    rw [ih x0, gradeProj_of_gt (Nat.lt_succ_self n) x0, add_zero, ih x1]

theorem gradeProj_vec_one {n : Nat} (v : Fin n → K) :
    gradeProj 1 (vec v) = vec v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [vec, gradeProj]
    exact Prod.ext (ih _) (by rw [gradeProj_smul, ← scalar_one, gradeProj_scalar_zero])

theorem gradeProj_vec_ne_one {n : Nat} {k : Nat} (hk : k ≠ 1) (v : Fin n → K) :
    gradeProj k (vec v) = zero := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    dsimp [vec]
    cases k with
    | zero =>
      dsimp [gradeProj]
      exact Prod.ext (ih (by omega) _) rfl
    | succ k =>
      cases k with
      | zero => exact absurd rfl hk
      | succ m =>
        dsimp [gradeProj]
        exact Prod.ext (ih (by omega) _)
          (by dsimp [zero]; rw [gradeProj_smul, ← scalar_one, gradeProj_scalar_succ, smul_zero])

/-- Grade involution acts on grade `k` by `(-1)^k`. -/
theorem invol_gradeProj {n : Nat} (k : Nat) (x : ClSpace K n) :
    invol (gradeProj k x) = smul (CommRing2.signPow K k) (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (one_smul x).symm
    | succ k => exact (smul_zero (n := 0) _).symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero =>
      apply Prod.ext <;> dsimp [gradeProj, invol, smul, CommRing2.signPow]
      · exact ih 0 x0
      · rw [invol_zero, neg_zero, one_smul]
    | succ k =>
      apply Prod.ext <;> dsimp [gradeProj, invol, smul]
      · exact ih (k + 1) x0
      · rw [ih k x1, ← neg_smul]
        rfl

theorem gradeProj_invol {n : Nat} (k : Nat) (x : ClSpace K n) :
    gradeProj k (invol x) = invol (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero =>
      apply Prod.ext <;> dsimp [gradeProj, invol]
      · exact ih 0 x0
      · rw [invol_zero, neg_zero]
    | succ k =>
      apply Prod.ext <;> dsimp [gradeProj, invol]
      · exact ih (k + 1) x0
      · rw [gradeProj_neg, ih k x1]

/-- **Reversion Sign Theorem:** Reversion acts on grade `k` by `(-1)^{k(k-1)/2}`. -/
theorem rev_gradeProj {n : Nat} (k : Nat) (x : ClSpace K n) :
    rev (gradeProj k x) = smul (CommRing2.signPow K (triNum k)) (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (one_smul x).symm
    | succ k => exact (smul_zero (n := 0) _).symm
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero =>
      apply Prod.ext <;> dsimp [gradeProj, rev, smul, triNum, CommRing2.signPow]
      · exact ih 0 x0
      · rw [rev_zero, invol_zero, one_smul]
    | succ k =>
      apply Prod.ext <;> dsimp [gradeProj, rev, smul]
      · exact ih (k + 1) x0
      · rw [ih k x1, invol_smul, invol_gradeProj, smul_smul, ← CommRing2.signPow_add]
        rfl

theorem gradeProj_rev {n : Nat} (k : Nat) (x : ClSpace K n) :
    gradeProj k (rev x) = rev (gradeProj k x) := by
  induction n generalizing k with
  | zero =>
    cases k <;> rfl
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    cases k with
    | zero =>
      apply Prod.ext <;> dsimp [gradeProj, rev]
      · exact ih 0 x0
      · rw [rev_zero, invol_zero]
    | succ k =>
      apply Prod.ext <;> dsimp [gradeProj, rev]
      · exact ih (k + 1) x0
      · rw [gradeProj_invol, ih k x1]

theorem rev_of_hasGrade {n k : Nat} {x : ClSpace K n} (hx : HasGrade k x) :
    rev x = smul (CommRing2.signPow K (triNum k)) x := by
  rw [← hx, rev_gradeProj, hx]

/-! ### Commutator & Anticommutator Symmetric–Antisymmetric Decomposition -/

/-- Anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  add (mul q x y) (mul q y x)

/-- Commutator `[X, Y] = X Y - Y X`. -/
def comm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  sub (mul q x y) (mul q y x)

/-- Symmetric part `(1/2) {X, Y} = (1/2) (X Y + Y X)`. -/
def symPart {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  smul CommRing2.half (anticomm q x y)

/-- Antisymmetric part `(1/2) [X, Y] = (1/2) (X Y - Y X)`. -/
def antisymPart {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  smul CommRing2.half (comm q x y)

theorem symPart_symm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    symPart q x y = symPart q y x := by
  unfold symPart anticomm
  rw [add_comm]

theorem antisymPart_antisymm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    antisymPart q x y = neg (antisymPart q y x) := by
  unfold antisymPart comm sub
  rw [← smul_neg, neg_add, neg_neg, add_comm]

/-- **Universal Commutator–Anticommutator Product Decomposition:**
    `X Y = (1/2){X, Y} + (1/2)[X, Y]` for all `X, Y ∈ Cl(n, q)`. -/
theorem mul_eq_symPart_add_antisymPart {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    mul q x y = add (symPart q x y) (antisymPart q x y) := by
  unfold symPart antisymPart anticomm comm sub
  rw [← smul_add]
  have hsum :
      add (add (mul q x y) (mul q y x)) (add (mul q x y) (neg (mul q y x))) =
      add (mul q x y) (mul q x y) := by
    calc
      add (add (mul q x y) (mul q y x)) (add (mul q x y) (neg (mul q y x)))
        = add (add (mul q x y) (mul q x y)) (add (mul q y x) (neg (mul q y x))) := by
            simp only [add_assoc, add_left_comm, add_comm]
      _ = add (add (mul q x y) (mul q x y)) zero := by rw [add_neg_cancel]
      _ = add (mul q x y) (mul q x y) := add_zero _
  rw [hsum, half_smul_add_self]

/-- **Uniqueness of Symmetric–Antisymmetric Product Decomposition:**
    If `S` is symmetric, `A` is antisymmetric, and `S(X, Y) + A(X, Y) = X Y` for all `X, Y`,
    then necessarily `S = symPart q` and `A = antisymPart q`. -/
theorem sym_antisym_decomp_unique {n : Nat} (q : Fin n → K)
    (S A : ClSpace K n → ClSpace K n → ClSpace K n)
    (hS : ∀ x y, S x y = S y x)
    (hA : ∀ x y, A y x = neg (A x y))
    (hDecomp : ∀ x y, add (S x y) (A x y) = mul q x y) :
    (∀ x y, S x y = symPart q x y) ∧ (∀ x y, A x y = antisymPart q x y) := by
  constructor
  · intro x y
    have hxy := hDecomp x y
    have hyx := hDecomp y x
    rw [← hS x y, hA x y] at hyx
    have h2S : add (add (S x y) (A x y)) (add (S x y) (neg (A x y))) = anticomm q x y := by
      rw [hxy, hyx]; rfl
    have hsimp : add (add (S x y) (A x y)) (add (S x y) (neg (A x y))) = add (S x y) (S x y) := by
      calc
        add (add (S x y) (A x y)) (add (S x y) (neg (A x y)))
          = add (add (S x y) (S x y)) (add (A x y) (neg (A x y))) := by
              simp only [add_assoc, add_left_comm, add_comm]
        _ = add (S x y) (S x y) := by rw [add_neg_cancel, add_zero]
    rw [hsimp] at h2S
    unfold symPart
    rw [← h2S, half_smul_add_self]
  · intro x y
    have hxy := hDecomp x y
    have hyx := hDecomp y x
    rw [← hS x y, hA x y] at hyx
    have h2A : sub (add (S x y) (A x y)) (add (S x y) (neg (A x y))) = comm q x y := by
      rw [hxy, hyx]; rfl
    have hsimp : sub (add (S x y) (A x y)) (add (S x y) (neg (A x y))) = add (A x y) (A x y) := by
      unfold sub
      rw [neg_add, neg_neg]
      calc
        add (add (S x y) (A x y)) (add (neg (S x y)) (A x y))
          = add (add (S x y) (neg (S x y))) (add (A x y) (A x y)) := by
              simp only [add_assoc, add_left_comm, add_comm]
        _ = add (A x y) (A x y) := by rw [add_neg_cancel, zero_add]
    rw [hsimp] at h2A
    unfold antisymPart
    rw [← h2A, half_smul_add_self]

/-! ### Exterior (Outer / Wedge) Product and Inner Contractions -/

/-- Zero quadratic form on `K^n` yielding the exterior algebra `Λ(K^n) = Cl(n, 0)`. -/
def zeroForm {n : Nat} : Fin n → K := fun _ => 0

/-- Exterior (outer / wedge) product `X ∧ Y` on `ClSpace K n`. -/
def wedge {n : Nat} (x y : ClSpace K n) : ClSpace K n :=
  mul zeroForm x y

/-- Grade-filtering & top-grade theorem for products of homogeneous elements:
    If `x` has grade `r` and `y` has grade `s`, then:
    (1) `⟨x * y⟩_m = 0` for all `m > r + s`, and
    (2) `⟨x * y⟩_{r + s} = x ∧ y` (which itself has grade `r + s`). -/
theorem homogeneous_mul_top_grade {n : Nat} (q : Fin n → K)
    {r s : Nat} {x y : ClSpace K n} (hx : HasGrade r x) (hy : HasGrade s y) :
    (∀ m : Nat, r + s < m → gradeProj m (mul q x y) = zero) ∧
    gradeProj (r + s) (mul q x y) = wedge x y ∧
    HasGrade (r + s) (wedge x y) := by
  induction n generalizing r s with
  | zero =>
    have hzero_case :
        (r = 0 ∧ s = 0) ∨ (0 < r ∨ 0 < s) := by omega
    cases hzero_case with
    | inl hrs0 =>
      rcases hrs0 with ⟨hr, hs⟩
      subst hr; subst hs
      refine ⟨fun m hm => ?_, rfl, rfl⟩
      cases m with
      | zero => omega
      | succ m => rfl
    | inr hpos =>
      cases hpos with
      | inl hr =>
        have hx0 : x = (zero : ClSpace K 0) := by
          rw [← hx]; cases r with | zero => omega | succ r => rfl
        subst hx0
        refine ⟨fun m _ => ?_, ?_, ?_⟩
        · rw [zero_mul, gradeProj_zero_elem]
        · unfold wedge; rw [zero_mul, zero_mul, gradeProj_zero_elem]
        · unfold HasGrade wedge; rw [zero_mul, gradeProj_zero_elem]
      | inr hs =>
        have hy0 : y = (zero : ClSpace K 0) := by
          rw [← hy]; cases s with | zero => omega | succ s => rfl
        subst hy0
        refine ⟨fun m _ => ?_, ?_, ?_⟩
        · rw [mul_zero, gradeProj_zero_elem]
        · unfold wedge; rw [mul_zero, mul_zero, gradeProj_zero_elem]
        · unfold HasGrade wedge; rw [mul_zero, gradeProj_zero_elem]
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    let q' := finTail q
    have hwedge_step :
        wedge (n := n + 1) (x0, x1) (y0, y1) =
        ((wedge x0 y0, add (wedge x1 y0) (wedge (invol x0) y1)) : ClSpace K (n + 1)) := by
      unfold wedge
      change (add (mul (finTail zeroForm) x0 y0)
                  (smul (finHead (zeroForm : Fin (n + 1) → K)) (mul (finTail zeroForm) (invol x1) y1)),
              add (mul (finTail zeroForm) x1 y0) (mul (finTail zeroForm) (invol x0) y1)) =
             (mul zeroForm x0 y0, add (mul zeroForm x1 y0) (mul zeroForm (invol x0) y1))
      have hzf : finTail (zeroForm : Fin (n + 1) → K) = zeroForm := rfl
      have hzh : finHead (zeroForm : Fin (n + 1) → K) = (0 : K) := rfl
      rw [hzf, hzh, zero_smul, add_zero]
    cases r with
    | zero =>
      dsimp [HasGrade, gradeProj] at hx
      have hx0 : HasGrade 0 x0 := congrArg Prod.fst hx
      have hx1 : x1 = zero := (congrArg Prod.snd hx).symm
      subst hx1
      have hx0_inv : HasGrade 0 (invol x0) := by
        unfold HasGrade; rw [gradeProj_invol, hx0]
      cases s with
      | zero =>
        dsimp [HasGrade, gradeProj] at hy
        have hy0 : HasGrade 0 y0 := congrArg Prod.fst hy
        have hy1 : y1 = zero := (congrArg Prod.snd hy).symm
        subst hy1
        have ih00 := ih q' hx0 hy0
        refine ⟨fun m hm => ?_, ?_, ?_⟩
        · cases m with
          | zero => omega
          | succ m =>
            dsimp [mul, gradeProj]
            rw [invol_zero, zero_mul, smul_zero, add_zero, zero_mul, mul_zero, add_zero,
                gradeProj_zero_elem]
            exact Prod.ext (ih00.1 (m + 1) (by omega)) rfl
        · dsimp [mul, gradeProj]
          rw [hwedge_step, invol_zero, zero_mul, smul_zero, add_zero]
          unfold wedge at *
          rw [zero_mul, mul_zero, add_zero]
          exact Prod.ext ih00.2.1 rfl
        · unfold HasGrade
          rw [hwedge_step]
          unfold wedge
          rw [zero_mul, mul_zero, add_zero]
          exact Prod.ext ih00.2.2 rfl
      | succ s =>
        dsimp [HasGrade, gradeProj] at hy
        have hy0 : HasGrade (s + 1) y0 := congrArg Prod.fst hy
        have hy1 : HasGrade s y1 := congrArg Prod.snd hy
        have ih_0_s1 := ih q' hx0 hy0
        have ih_inv0_s := ih q' hx0_inv hy1
        refine ⟨fun m hm => ?_, ?_, ?_⟩
        · cases m with
          | zero => omega
          | succ m =>
            dsimp [mul, gradeProj]
            rw [invol_zero, zero_mul, smul_zero, add_zero, zero_mul, zero_add]
            exact Prod.ext (ih_0_s1.1 (m + 1) (by omega)) (ih_inv0_s.1 m (by omega))
        · have hrs : 0 + (s + 1) = s + 1 := Nat.zero_add (s + 1)
          rw [hrs, hwedge_step]
          dsimp [mul, gradeProj]
          rw [invol_zero, zero_mul, smul_zero, add_zero, zero_mul, zero_add]
          have hw0 : wedge (zero : ClSpace K n) y0 = zero := zero_mul zeroForm y0
          rw [hw0, zero_add]
          exact Prod.ext (by simpa [hrs] using ih_0_s1.2.1) (by simpa using ih_inv0_s.2.1)
        · have hrs : 0 + (s + 1) = s + 1 := Nat.zero_add (s + 1)
          unfold HasGrade
          rw [hrs, hwedge_step]
          have hw0 : wedge (zero : ClSpace K n) y0 = zero := zero_mul zeroForm y0
          rw [hw0, zero_add]
          dsimp [gradeProj]
          exact Prod.ext (by simpa [hrs] using ih_0_s1.2.2) (by simpa using ih_inv0_s.2.2)
    | succ r =>
      dsimp [HasGrade, gradeProj] at hx
      have hx0 : HasGrade (r + 1) x0 := congrArg Prod.fst hx
      have hx1 : HasGrade r x1 := congrArg Prod.snd hx
      have hx0_inv : HasGrade (r + 1) (invol x0) := by
        unfold HasGrade; rw [gradeProj_invol, hx0]
      have hx1_inv : HasGrade r (invol x1) := by
        unfold HasGrade; rw [gradeProj_invol, hx1]
      cases s with
      | zero =>
        dsimp [HasGrade, gradeProj] at hy
        have hy0 : HasGrade 0 y0 := congrArg Prod.fst hy
        have hy1 : y1 = zero := (congrArg Prod.snd hy).symm
        subst hy1
        have ih_r1_0 := ih q' hx0 hy0
        have ih_r_0 := ih q' hx1 hy0
        refine ⟨fun m hm => ?_, ?_, ?_⟩
        · cases m with
          | zero => omega
          | succ m =>
            dsimp [mul, gradeProj]
            rw [mul_zero, smul_zero, add_zero, mul_zero, add_zero]
            exact Prod.ext (ih_r1_0.1 (m + 1) (by omega)) (ih_r_0.1 m (by omega))
        · have hrs : (r + 1) + 0 = r + 1 := Nat.add_zero (r + 1)
          rw [hrs, hwedge_step]
          dsimp [mul, gradeProj]
          rw [mul_zero, smul_zero, add_zero, mul_zero, add_zero]
          have hw0 : wedge (invol x0) zero = zero := mul_zero zeroForm (invol x0)
          rw [hw0, add_zero]
          exact Prod.ext (by simpa [hrs] using ih_r1_0.2.1) (by simpa using ih_r_0.2.1)
        · have hrs : (r + 1) + 0 = r + 1 := Nat.add_zero (r + 1)
          unfold HasGrade
          rw [hrs, hwedge_step]
          have hw0 : wedge (invol x0) zero = zero := mul_zero zeroForm (invol x0)
          rw [hw0, add_zero]
          dsimp [gradeProj]
          exact Prod.ext (by simpa [hrs] using ih_r1_0.2.2) (by simpa using ih_r_0.2.2)
      | succ s =>
        dsimp [HasGrade, gradeProj] at hy
        have hy0 : HasGrade (s + 1) y0 := congrArg Prod.fst hy
        have hy1 : HasGrade s y1 := congrArg Prod.snd hy
        have ih00 := ih q' hx0 hy0
        have ih11 := ih q' hx1_inv hy1
        have ih10 := ih q' hx1 hy0
        have ih01 := ih q' hx0_inv hy1
        refine ⟨fun m hm => ?_, ?_, ?_⟩
        · cases m with
          | zero => omega
          | succ m =>
            dsimp [mul, gradeProj]
            rw [gradeProj_add, gradeProj_smul, gradeProj_add]
            rw [ih00.1 (m + 1) (by omega), ih11.1 (m + 1) (by omega),
                smul_zero, add_zero,
                ih10.1 m (by omega), ih01.1 m (by omega), add_zero]
            rfl
        · have hrs : (r + 1) + (s + 1) = (r + s + 1) + 1 := by omega
          rw [hrs, hwedge_step]
          dsimp [mul, gradeProj]
          rw [gradeProj_add, gradeProj_smul, gradeProj_add]
          have h11_zero : gradeProj (r + s + 2) (mul q' (invol x1) y1) = zero :=
            ih11.1 (r + s + 2) (by omega)
          have hrs2 : (r + s + 1) + 1 = (r + 1) + (s + 1) := by omega
          have hrs1a : r + s + 1 = r + (s + 1) := by omega
          have hrs1b : r + s + 1 = (r + 1) + s := by omega
          apply Prod.ext
          · change add (gradeProj (r + s + 2) (mul q' x0 y0))
                       (smul (finHead q) (gradeProj (r + s + 2) (mul q' (invol x1) y1))) =
                   wedge x0 y0
            rw [h11_zero, smul_zero, add_zero]
            simpa [hrs2] using ih00.2.1
          · rw [hrs1a]
            have t1 : gradeProj (r + (s + 1)) (mul q' x1 y0) = wedge x1 y0 := ih10.2.1
            have t2 : gradeProj (r + (s + 1)) (mul q' (invol x0) y1) = wedge (invol x0) y1 := by
              rw [← hrs1a, hrs1b]; exact ih01.2.1
            rw [t1, t2]
        · have hrs : (r + 1) + (s + 1) = (r + s + 1) + 1 := by omega
          unfold HasGrade
          rw [hrs, hwedge_step]
          dsimp [gradeProj]
          rw [gradeProj_add]
          have hrs2 : (r + s + 1) + 1 = (r + 1) + (s + 1) := by omega
          have hrs1a : r + s + 1 = r + (s + 1) := by omega
          have hrs1b : r + s + 1 = (r + 1) + s := by omega
          apply Prod.ext
          · simpa [hrs2] using ih00.2.2
          · have u1 : gradeProj (r + s + 1) (wedge x1 y0) = wedge x1 y0 := by
              rw [hrs1a]; exact ih10.2.2
            have u2 : gradeProj (r + s + 1) (wedge (invol x0) y1) = wedge (invol x0) y1 := by
              rw [hrs1b]; exact ih01.2.2
            rw [u1, u2]

/-- Left contraction `X ⌟ Y = ∑_{0 ≤ r ≤ s ≤ n} ⟨⟨X⟩_r ⟨Y⟩_s⟩_{s - r}`. -/
def leftContract {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  sumUpTo (fun r =>
    sumUpTo (fun s =>
      if r ≤ s then gradeProj (s - r) (mul q (gradeProj r x) (gradeProj s y)) else zero) n) n

/-- Right contraction `X ⌞ Y = ∑_{0 ≤ s ≤ r ≤ n} ⟨⟨X⟩_r ⟨Y⟩_s⟩_{r - s}`. -/
def rightContract {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  sumUpTo (fun r =>
    sumUpTo (fun s =>
      if s ≤ r then gradeProj (r - s) (mul q (gradeProj r x) (gradeProj s y)) else zero) n) n

/-- Hestenes inner product `X · Y = ∑_{r=1}^n ∑_{s=1}^n ⟨⟨X⟩_r ⟨Y⟩_s⟩_{|r - s|}`
    (vanishing on scalars `r = 0` or `s = 0` per Hestenes–Sobczyk). -/
def hestenesInner {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : ClSpace K n :=
  sumUpTo (fun r =>
    sumUpTo (fun s =>
      if 1 ≤ r ∧ 1 ≤ s then
        gradeProj (if r ≤ s then s - r else r - s) (mul q (gradeProj r x) (gradeProj s y))
      else zero) n) n

theorem sumUpTo_eq_zero {n : Nat} (f : Nat → ClSpace K n) (m : Nat)
    (hz : ∀ j, j ≤ m → f j = zero) :
    sumUpTo f m = zero := by
  induction m with
  | zero => exact hz 0 (Nat.le_refl 0)
  | succ k ihk =>
    dsimp [sumUpTo]
    rw [ihk (fun j hj => hz j (by omega)), hz (k + 1) (Nat.le_refl _), add_zero]

theorem sumUpTo_single {n : Nat} (f : Nat → ClSpace K n) (m i : Nat)
    (hi : i ≤ m) (hzero : ∀ j, j ≤ m → j ≠ i → f j = zero) :
    sumUpTo f m = f i := by
  induction m with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; rfl
  | succ m ih =>
    dsimp [sumUpTo]
    by_cases him : i = m + 1
    · subst him
      have hprev : sumUpTo f m = zero :=
        sumUpTo_eq_zero f m (fun j hj => hzero j (by omega) (by omega))
      rw [hprev, zero_add]
    · rw [ih (by omega) (fun j hj hne => hzero j (by omega) hne),
          hzero (m + 1) (by omega) (fun h => him h.symm), add_zero]

theorem leftContract_of_hasGrade {n : Nat} (q : Fin n → K)
    {r s : Nat} (hr : r ≤ n) (hs : s ≤ n) {x y : ClSpace K n}
    (hx : HasGrade r x) (hy : HasGrade s y) :
    leftContract q x y = (if r ≤ s then gradeProj (s - r) (mul q x y) else zero) := by
  unfold leftContract
  rw [sumUpTo_single _ n r hr]
  · rw [sumUpTo_single _ n s hs]
    · rw [hx, hy]
    · intro j _ hj
      have hyj : gradeProj j y = zero := by
        rw [← hy]; exact gradeProj_orthog hj y
      rw [hyj, mul_zero, gradeProj_zero_elem]
      split <;> rfl
  · intro i _ hi
    have hxi : gradeProj i x = zero := by
      rw [← hx]; exact gradeProj_orthog hi x
    have hsum0 : ∀ m, sumUpTo (fun s' =>
        if i ≤ s' then gradeProj (s' - i) (mul q (gradeProj i x) (gradeProj s' y)) else zero) m = zero := by
      intro m
      induction m with
      | zero =>
        rw [hxi]; dsimp [sumUpTo]; rw [zero_mul, gradeProj_zero_elem]; split <;> rfl
      | succ m ihm =>
        dsimp [sumUpTo]
        rw [ihm, zero_add, hxi, zero_mul, gradeProj_zero_elem]
        split <;> rfl
    exact hsum0 n

theorem rightContract_of_hasGrade {n : Nat} (q : Fin n → K)
    {r s : Nat} (hr : r ≤ n) (hs : s ≤ n) {x y : ClSpace K n}
    (hx : HasGrade r x) (hy : HasGrade s y) :
    rightContract q x y = (if s ≤ r then gradeProj (r - s) (mul q x y) else zero) := by
  unfold rightContract
  rw [sumUpTo_single _ n r hr]
  · rw [sumUpTo_single _ n s hs]
    · rw [hx, hy]
    · intro j _ hj
      have hyj : gradeProj j y = zero := by
        rw [← hy]; exact gradeProj_orthog hj y
      rw [hyj, mul_zero, gradeProj_zero_elem]
      split <;> rfl
  · intro i _ hi
    have hxi : gradeProj i x = zero := by
      rw [← hx]; exact gradeProj_orthog hi x
    have hsum0 : ∀ m, sumUpTo (fun s' =>
        if s' ≤ i then gradeProj (i - s') (mul q (gradeProj i x) (gradeProj s' y)) else zero) m = zero := by
      intro m
      induction m with
      | zero =>
        rw [hxi]; dsimp [sumUpTo]; rw [zero_mul, gradeProj_zero_elem]; split <;> rfl
      | succ m ihm =>
        dsimp [sumUpTo]
        rw [ihm, zero_add, hxi, zero_mul, gradeProj_zero_elem]
        split <;> rfl
    exact hsum0 n

theorem hestenesInner_of_hasGrade {n : Nat} (q : Fin n → K)
    {r s : Nat} (hr1 : 1 ≤ r) (hr : r ≤ n) (hs1 : 1 ≤ s) (hs : s ≤ n) {x y : ClSpace K n}
    (hx : HasGrade r x) (hy : HasGrade s y) :
    hestenesInner q x y = gradeProj (if r ≤ s then s - r else r - s) (mul q x y) := by
  unfold hestenesInner
  rw [sumUpTo_single _ n r hr]
  · rw [sumUpTo_single _ n s hs]
    · rw [if_pos ⟨hr1, hs1⟩, hx, hy]
    · intro j _ hj
      have hyj : gradeProj j y = zero := by
        rw [← hy]; exact gradeProj_orthog hj y
      rw [hyj, mul_zero, gradeProj_zero_elem]
      split <;> rfl
  · intro i _ hi
    have hxi : gradeProj i x = zero := by
      rw [← hx]; exact gradeProj_orthog hi x
    have hsum0 : ∀ m, sumUpTo (fun s' =>
        if 1 ≤ i ∧ 1 ≤ s' then
          gradeProj (if i ≤ s' then s' - i else i - s') (mul q (gradeProj i x) (gradeProj s' y))
        else zero) m = zero := by
      intro m
      induction m with
      | zero =>
        rw [hxi]; dsimp [sumUpTo]; rw [zero_mul, gradeProj_zero_elem]; split <;> rfl
      | succ m ihm =>
        dsimp [sumUpTo]
        rw [ihm, zero_add, hxi, zero_mul, gradeProj_zero_elem]
        split <;> rfl
    exact hsum0 n

/-! ### Canonical Metric Bilinear Form `⟨X, Y⟩_{Q~} = ⟨X~ Y⟩_0` and Scalar Trace `⟨X Y⟩_0` -/

/-- Canonical reversion metric bilinear form `⟨X, Y⟩_{Q~} = scalarPart(X~ * Y)`. -/
def metricForm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : K :=
  scalarPart (mul q (rev x) y)

/-- Untwisted scalar trace bilinear form `⟨X, Y⟩_0 = scalarPart(X * Y)`. -/
def scalarTrace {n : Nat} (q : Fin n → K) (x y : ClSpace K n) : K :=
  scalarPart (mul q x y)

theorem metricForm_step {n : Nat} (q : Fin (n + 1) → K) (x0 x1 y0 y1 : ClSpace K n) :
    metricForm q (x0, x1) (y0, y1) =
      metricForm (finTail q) x0 y0 + finHead q * metricForm (finTail q) x1 y1 := by
  unfold metricForm
  dsimp [rev, mul, scalarPart]
  rw [scalarPart_add, scalarPart_smul, invol_invol]

theorem metricForm_zero_left {n : Nat} (q : Fin n → K) (y : ClSpace K n) :
    metricForm q zero y = 0 := by
  unfold metricForm
  rw [rev_zero, zero_mul, scalarPart_zero]

theorem metricForm_zero_right {n : Nat} (q : Fin n → K) (x : ClSpace K n) :
    metricForm q x zero = 0 := by
  unfold metricForm
  rw [mul_zero, scalarPart_zero]

theorem metricForm_add_left {n : Nat} (q : Fin n → K) (x1 x2 y : ClSpace K n) :
    metricForm q (add x1 x2) y = metricForm q x1 y + metricForm q x2 y := by
  unfold metricForm
  rw [rev_add, right_distrib, scalarPart_add]

theorem metricForm_add_right {n : Nat} (q : Fin n → K) (x y1 y2 : ClSpace K n) :
    metricForm q x (add y1 y2) = metricForm q x y1 + metricForm q x y2 := by
  unfold metricForm
  rw [left_distrib, scalarPart_add]

theorem metricForm_smul_left {n : Nat} (q : Fin n → K) (c : K) (x y : ClSpace K n) :
    metricForm q (smul c x) y = c * metricForm q x y := by
  unfold metricForm
  rw [rev_smul, smul_mul, scalarPart_smul]

theorem metricForm_smul_right {n : Nat} (q : Fin n → K) (c : K) (x y : ClSpace K n) :
    metricForm q x (smul c y) = c * metricForm q x y := by
  unfold metricForm
  rw [mul_smul, scalarPart_smul]

/-- Symmetry of the canonical metric bilinear form: `⟨X, Y⟩_{Q~} = ⟨Y, X⟩_{Q~}`. -/
theorem metricForm_symm {n : Nat} (q : Fin n → K) (x y : ClSpace K n) :
    metricForm q x y = metricForm q y x := by
  induction n with
  | zero => exact CommRing2.mul_comm x y
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    rw [metricForm_step, metricForm_step, ih (finTail q) x0 y0, ih (finTail q) x1 y1]

/-- Distinct homogeneous grades are mutually orthogonal under `metricForm` for ANY `q`. -/
theorem metricForm_grade_orthog {n : Nat} (q : Fin n → K) {r s : Nat} (hrs : r ≠ s)
    (x y : ClSpace K n) :
    metricForm q (gradeProj r x) (gradeProj s y) = 0 := by
  induction n generalizing r s with
  | zero =>
    cases r with
    | zero =>
      cases s with
      | zero => exact absurd rfl hrs
      | succ s => exact CommRing2.mul_zero _
    | succ r => exact CommRing2.zero_mul _
  | succ n ih =>
    rcases x with ⟨x0, x1⟩; rcases y with ⟨y0, y1⟩
    cases r with
    | zero =>
      cases s with
      | zero => exact absurd rfl hrs
      | succ s =>
        dsimp [gradeProj]
        rw [metricForm_step, ih (finTail q) (by omega) x0 y0,
            metricForm_zero_left, CommRing2.mul_zero, CommRing2.add_zero]
    | succ r =>
      cases s with
      | zero =>
        dsimp [gradeProj]
        rw [metricForm_step, ih (finTail q) (by omega) x0 y0,
            metricForm_zero_right, CommRing2.mul_zero, CommRing2.add_zero]
      | succ s =>
        dsimp [gradeProj]
        rw [metricForm_step, ih (finTail q) (by omega) x0 y0,
            ih (finTail q) (by omega) x1 y1, CommRing2.mul_zero, CommRing2.add_zero]

/-- On grade-1 vectors, `metricForm` agrees identically with the polar metric `B_Q(u, v)`. -/
theorem metricForm_vec {n : Nat} (q u v : Fin n → K) :
    metricForm q (vec u) (vec v) = polarForm q u v := by
  induction n with
  | zero => exact CommRing2.zero_mul 0
  | succ n ih =>
    dsimp [vec, polarForm]
    rw [metricForm_step, ih, metricForm_smul_left, metricForm_smul_right]
    have hone : metricForm (finTail q) (one : ClSpace K n) one = 1 := by
      unfold metricForm
      rw [rev_one, one_mul, ← scalar_one, scalarPart_scalar]
    rw [hone, CommRing2.mul_one, CommRing2.add_comm]

theorem metricForm_scalar {n : Nat} (q : Fin n → K) (a b : K) :
    metricForm q (scalar a) (scalar b) = a * b := by
  unfold metricForm
  rw [rev_scalar, scalar_mul, ← scalar_smul, scalarPart_scalar]

end Grading

/-! ### Positive Definiteness of `metricForm` for Positive-Definite Rational Metrics -/

section PositiveDefinite
theorem metricForm_nonneg {n : Nat} (q : Fin n → RatQ)
    (hq : ∀ i, RatQ.IsPos (q i)) (x : ClSpace RatQ n) :
    RatQ.IsNonneg (metricForm q x x) := by
  induction n with
  | zero => exact RatQ.sq_nonneg x
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    rw [metricForm_step]
    have h0 := ih (finTail q) (fun i => hq i.succ) x0
    have h1 := ih (finTail q) (fun i => hq i.succ) x1
    have hq0 : RatQ.IsNonneg (finHead q) := Or.inr (hq ⟨0, Nat.zero_lt_succ n⟩)
    exact RatQ.nonneg_add h0 (RatQ.nonneg_mul hq0 h1)

/-- When all diagonal entries `q_i > 0` over `ℚ`, `metricForm` is a strictly positive-definite
    inner product on all of `Cl(n, q)`. -/
theorem metricForm_pos_of_ne_zero {n : Nat} (q : Fin n → RatQ)
    (hq : ∀ i, RatQ.IsPos (q i)) {x : ClSpace RatQ n} (hx : x ≠ zero) :
    RatQ.IsPos (metricForm q x x) := by
  induction n with
  | zero => exact RatQ.sq_pos_of_ne_zero hx
  | succ n ih =>
    rcases x with ⟨x0, x1⟩
    rw [metricForm_step]
    by_cases hx0 : x0 = zero
    · subst hx0
      have hx1 : x1 ≠ zero := fun h1 => hx (Prod.ext rfl h1)
      rw [metricForm_zero_left, CommRing2.zero_add]
      exact RatQ.pos_mul (hq ⟨0, Nat.zero_lt_succ n⟩) (ih (finTail q) (fun i => hq i.succ) hx1)
    · have hp0 := ih (finTail q) (fun i => hq i.succ) hx0
      have hn1 := metricForm_nonneg (finTail q) (fun i => hq i.succ) x1
      have hqn1 := RatQ.nonneg_mul (Or.inr (hq ⟨0, Nat.zero_lt_succ n⟩)) hn1
      exact RatQ.add_pos_of_pos_of_nonneg hp0 hqn1

end PositiveDefinite

end ClSpace
end CliffordDecomp
