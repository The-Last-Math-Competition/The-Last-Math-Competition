/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Commutative rings, `n × n` matrices, Laplace determinants, and full determinant
 multiplicativity `det (A * B) = det A * det B` from first principles in core Lean 4.
-/

namespace Conjecture00000000593

/-- Lightweight commutative ring structure with propositional `=` axioms. -/
structure CRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

namespace CRing

section BasicLemmas
variable {R : Type} (S : CRing R)

theorem add_zero (a : R) : S.add a S.zero = a := by
  rw [S.add_comm, S.zero_add]

theorem add_right_neg (a : R) : S.add a (S.neg a) = S.zero := by
  rw [S.add_comm, S.add_left_neg]

theorem mul_one (a : R) : S.mul a S.one = a := by
  rw [S.mul_comm, S.one_mul]

theorem right_distrib (a b c : R) : S.mul (S.add a b) c = S.add (S.mul a c) (S.mul b c) := by
  rw [S.mul_comm, S.left_distrib, S.mul_comm c a, S.mul_comm c b]

theorem add_left_cancel {a b c : R} (h : S.add a b = S.add a c) : b = c := by
  have h1 : S.add (S.neg a) (S.add a b) = S.add (S.neg a) (S.add a c) :=
    congrArg (S.add (S.neg a)) h
  rw [← S.add_assoc, ← S.add_assoc, S.add_left_neg, S.zero_add, S.zero_add] at h1
  exact h1

theorem mul_zero (a : R) : S.mul a S.zero = S.zero := by
  apply S.add_left_cancel (a := S.mul a S.zero)
  rw [← S.left_distrib, S.add_zero, S.add_zero]

theorem zero_mul (a : R) : S.mul S.zero a = S.zero := by
  rw [S.mul_comm, S.mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : S.add a b = S.zero) : b = S.neg a := by
  apply S.add_left_cancel (a := a)
  rw [h, S.add_right_neg]

theorem neg_zero : S.neg S.zero = S.zero := by
  symm
  exact S.neg_eq_of_add_eq_zero (S.add_zero S.zero)

theorem neg_neg (a : R) : S.neg (S.neg a) = a := by
  symm
  exact S.neg_eq_of_add_eq_zero (S.add_left_neg a)

theorem mul_neg (a b : R) : S.mul a (S.neg b) = S.neg (S.mul a b) := by
  apply S.neg_eq_of_add_eq_zero
  rw [← S.left_distrib, S.add_right_neg, S.mul_zero]

theorem neg_mul (a b : R) : S.mul (S.neg a) b = S.neg (S.mul a b) := by
  rw [S.mul_comm, S.mul_neg, S.mul_comm]

theorem neg_add (a b : R) : S.neg (S.add a b) = S.add (S.neg a) (S.neg b) := by
  symm
  apply S.neg_eq_of_add_eq_zero
  have h : S.add (S.add a b) (S.add (S.neg a) (S.neg b)) =
      S.add a (S.add (S.add b (S.neg b)) (S.neg a)) := by
    rw [S.add_assoc, S.add_comm (S.neg a) (S.neg b), ← S.add_assoc b (S.neg b) (S.neg a)]
  rw [h, S.add_right_neg, S.zero_add, S.add_right_neg]

end BasicLemmas

def pow {R : Type} (S : CRing R) (a : R) : Nat → R
  | 0 => S.one
  | n + 1 => S.mul a (pow S a n)

def altSign {R : Type} (S : CRing R) : Nat → R
  | 0 => S.one
  | k + 1 => S.neg (altSign S k)

theorem altSign_add {R : Type} (S : CRing R) :
    ∀ (a b : Nat), S.altSign (a + b) = S.mul (S.altSign a) (S.altSign b)
  | 0, b => by
    simp only [Nat.zero_add, altSign]
    rw [S.one_mul]
  | a + 1, b => by
    rw [Nat.succ_add]
    simp only [altSign]
    rw [altSign_add S a b, S.neg_mul]

/-- Finite sum `∑_{i : Fin n} f i` in `S`. -/
def finSum {R : Type} (S : CRing R) : (n : Nat) → (Fin n → R) → R
  | 0, _ => S.zero
  | n + 1, f => S.add (f ⟨0, Nat.zero_lt_succ n⟩) (finSum S n (fun i => f i.succ))

theorem finSum_congr {R : Type} (S : CRing R) {n : Nat} {f g : Fin n → R}
    (h : ∀ i : Fin n, f i = g i) :
    S.finSum n f = S.finSum n g := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [finSum]
    rw [h ⟨0, Nat.zero_lt_succ n'⟩, ih (fun i => h i.succ)]

theorem finSum_zero {R : Type} (S : CRing R) (n : Nat) :
    S.finSum n (fun _ => S.zero) = S.zero := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [finSum, ih, S.zero_add]

theorem finSum_add {R : Type} (S : CRing R) {n : Nat} (f g : Fin n → R) :
    S.finSum n (fun i => S.add (f i) (g i)) = S.add (S.finSum n f) (S.finSum n g) := by
  induction n with
  | zero => simp only [finSum, S.zero_add]
  | succ n' ih =>
    simp only [finSum, ih]
    rw [S.add_assoc, ← S.add_assoc (g ⟨0, Nat.zero_lt_succ n'⟩),
        S.add_comm (g ⟨0, Nat.zero_lt_succ n'⟩) (S.finSum n' (fun i => f i.succ)),
        S.add_assoc, ← S.add_assoc]

theorem finSum_mul_left {R : Type} (S : CRing R) {n : Nat} (c : R) (f : Fin n → R) :
    S.finSum n (fun i => S.mul c (f i)) = S.mul c (S.finSum n f) := by
  induction n with
  | zero => simp only [finSum, S.mul_zero]
  | succ n' ih =>
    simp only [finSum, ih, S.left_distrib]

theorem finSum_mul_right {R : Type} (S : CRing R) {n : Nat} (f : Fin n → R) (c : R) :
    S.finSum n (fun i => S.mul (f i) c) = S.mul (S.finSum n f) c := by
  induction n with
  | zero => simp only [finSum, S.zero_mul]
  | succ n' ih =>
    simp only [finSum, ih, S.right_distrib]

theorem finSum_eq_single {R : Type} (S : CRing R) {n : Nat} (j : Fin n) (f : Fin n → R)
    (h : ∀ i : Fin n, i ≠ j → f i = S.zero) :
    S.finSum n f = f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n' ih =>
    simp only [finSum]
    rcases j with ⟨jv, hjv⟩
    cases jv with
    | zero =>
      have hrest : S.finSum n' (fun i => f i.succ) = S.zero := by
        rw [← S.finSum_zero n']
        apply S.finSum_congr
        intro i
        apply h i.succ
        intro heq
        have hv : (i.succ).val = 0 := congrArg Fin.val heq
        simp only [Fin.val_succ] at hv
        omega
      rw [hrest, S.add_zero]
    | succ jv' =>
      have h0 : f ⟨0, Nat.zero_lt_succ n'⟩ = S.zero := by
        apply h ⟨0, Nat.zero_lt_succ n'⟩
        intro heq
        have hv : 0 = jv' + 1 := congrArg Fin.val heq
        omega
      rw [h0, S.zero_add]
      have hj' : jv' < n' := by omega
      have hsub := ih ⟨jv', hj'⟩ (fun i => f i.succ) (by
        intro i hi
        apply h i.succ
        intro heq
        apply hi
        apply Fin.ext
        have hv : (i.succ).val = jv' + 1 := congrArg Fin.val heq
        simp only [Fin.val_succ] at hv
        dsimp
        omega)
      exact hsub

end CRing

/-- `Int` as a `CRing`. -/
def intCRing : CRing Int where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

/-- `n × n` matrices over `R`. -/
abbrev Mat (R : Type) (n : Nat) := Fin n → Fin n → R

/-- Identity matrix `I_n`. -/
def matId {R : Type} (S : CRing R) (n : Nat) : Mat R n :=
  fun i j => if i.val = j.val then S.one else S.zero

/-- Scalar matrix `c · I_n`. -/
def scalarMat {R : Type} (S : CRing R) (n : Nat) (c : R) : Mat R n :=
  fun i j => if i.val = j.val then c else S.zero

/-- Matrix multiplication `A * B`. -/
def matMul {R : Type} (S : CRing R) {n : Nat} (A B : Mat R n) : Mat R n :=
  fun i k => S.finSum n (fun j => S.mul (A i j) (B j k))

/-- Matrix power `A^s` (`A^0 = I_n`, `A^{s+1} = A * A^s`). -/
def matPow {R : Type} (S : CRing R) {n : Nat} (A : Mat R n) : Nat → Mat R n
  | 0 => matId S n
  | s + 1 => matMul S A (matPow S A s)

theorem matId_mul {R : Type} (S : CRing R) {n : Nat} (B : Mat R n) :
    matMul S (matId S n) B = B := by
  funext i k
  unfold matMul matId
  rw [S.finSum_eq_single i]
  · simp [S.one_mul]
  · intro j hij
    have hval : i.val ≠ j.val := fun hv => hij (Fin.ext hv).symm
    simp [hval, S.zero_mul]

/-- Order-preserving injection `Fin n → Fin (n + 1)` skipping index `j`. -/
def skipIdx {n : Nat} (j : Fin (n + 1)) (k : Fin n) : Fin (n + 1) :=
  if k.val < j.val then
    ⟨k.val, by omega⟩
  else
    ⟨k.val + 1, by omega⟩

/-- Submatrix obtained by deleting row `r` and column `c`. -/
def minor {R : Type} {n : Nat} (M : Mat R (n + 1)) (r c : Fin (n + 1)) : Mat R n :=
  fun i k => M (skipIdx r i) (skipIdx c k)

/-- Laplace determinant expanded along row `0`. -/
def det {R : Type} (S : CRing R) : {n : Nat} → Mat R n → R
  | 0, _ => S.one
  | n + 1, M =>
      let r0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      S.finSum (n + 1) (fun j =>
        S.mul (S.altSign j.val)
          (S.mul (M r0 j) (det S (minor M r0 j))))

theorem det_id {R : Type} (S : CRing R) : ∀ n : Nat, det S (matId S n) = S.one
  | 0 => rfl
  | n + 1 => by
      simp only [det]
      rw [S.finSum_eq_single ⟨0, Nat.zero_lt_succ n⟩]
      · simp only [CRing.altSign, matId, ↓reduceIte, S.one_mul]
        have hmin : minor (matId S (n + 1)) ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ =
            matId S n := by
          funext i k
          unfold minor skipIdx matId
          have hi : ¬ (i.val < 0) := by omega
          have hk : ¬ (k.val < 0) := by omega
          simp only [hi, hk, ↓reduceIte]
          by_cases hik : i.val = k.val
          · simp [hik]
          · have hne : i.val + 1 ≠ k.val + 1 := by omega
            simp [hik, hne]
        rw [hmin, det_id S n]
      · intro j hj
        have hjv : 0 ≠ j.val := fun hv => hj (Fin.ext hv.symm)
        simp only [matId, hjv, ↓reduceIte, S.zero_mul, S.mul_zero]

theorem det_scalar {R : Type} (S : CRing R) (c : R) :
    ∀ n : Nat, det S (scalarMat S n c) = S.pow c n
  | 0 => rfl
  | n + 1 => by
      simp only [det, CRing.pow]
      rw [S.finSum_eq_single ⟨0, Nat.zero_lt_succ n⟩]
      · simp only [CRing.altSign, scalarMat, ↓reduceIte, S.one_mul]
        have hmin : minor (scalarMat S (n + 1) c) ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ =
            scalarMat S n c := by
          funext i k
          unfold minor skipIdx scalarMat
          have hi : ¬ (i.val < 0) := by omega
          have hk : ¬ (k.val < 0) := by omega
          simp only [hi, hk, ↓reduceIte]
          by_cases hik : i.val = k.val
          · simp [hik]
          · have hne : i.val + 1 ≠ k.val + 1 := by omega
            simp [hik, hne]
        rw [hmin, det_scalar S c n]
      · intro j hj
        have hjv : 0 ≠ j.val := fun hv => hj (Fin.ext hv.symm)
        simp only [scalarMat, hjv, ↓reduceIte, S.zero_mul, S.mul_zero]

/-! ### Row-Multilinear Alternating Characterization & `det_mul` -/

/-- Axiomatic characterization of an alternating row-multilinear function `Φ : Mat R n → R`. -/
structure IsAltRowMultilinear {R : Type} (S : CRing R) (n : Nat) (Φ : Mat R n → R) : Prop where
  row_add : ∀ (M₁ M₂ M : Mat R n) (i : Fin n),
    (∀ r : Fin n, r ≠ i → ∀ c : Fin n, M r c = M₁ r c ∧ M₂ r c = M₁ r c) →
    (∀ c : Fin n, M i c = S.add (M₁ i c) (M₂ i c)) →
    Φ M = S.add (Φ M₁) (Φ M₂)
  row_scale : ∀ (a : R) (M₁ M : Mat R n) (i : Fin n),
    (∀ r : Fin n, r ≠ i → ∀ c : Fin n, M r c = M₁ r c) →
    (∀ c : Fin n, M i c = S.mul a (M₁ i c)) →
    Φ M = S.mul a (Φ M₁)
  adj_eq : ∀ (M : Mat R n) (i : Fin n) (hi : i.val + 1 < n),
    (∀ c : Fin n, M i c = M ⟨i.val + 1, hi⟩ c) →
    Φ M = S.zero

/-- Replace row `i` of `M` by vector `v`. -/
def replaceRow {R : Type} {n : Nat} (M : Mat R n) (i : Fin n) (v : Fin n → R) : Mat R n :=
  fun r c => if r.val = i.val then v c else M r c

/-- Swap rows `i` and `k` of `M`. -/
def swapRows {R : Type} {n : Nat} (i k : Fin n) (M : Mat R n) : Mat R n :=
  fun r c =>
    if r.val = i.val then M k c
    else if r.val = k.val then M i c
    else M r c

theorem alt_row_zero {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R n → R}
    (hΦ : IsAltRowMultilinear S n Φ) (M : Mat R n) (i : Fin n)
    (hz : ∀ c : Fin n, M i c = S.zero) : Φ M = S.zero := by
  have hsc := hΦ.row_scale S.zero M M i (fun _ _ _ => rfl) (fun c => by rw [hz c, S.zero_mul])
  rw [S.zero_mul] at hsc
  exact hsc

theorem alt_swap_adj {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R n → R}
    (hΦ : IsAltRowMultilinear S n Φ) (M : Mat R n) (i : Fin n) (hi : i.val + 1 < n) :
    Φ (swapRows i ⟨i.val + 1, hi⟩ M) = S.neg (Φ M) := by
  let i1 : Fin n := ⟨i.val + 1, hi⟩
  let sumVec : Fin n → R := fun c => S.add (M i c) (M i1 c)
  let M_both := replaceRow (replaceRow M i sumVec) i1 sumVec
  let M_u_sum := replaceRow M i1 sumVec
  let M_v_sum := replaceRow (replaceRow M i (M i1)) i1 sumVec
  let M_uu := replaceRow M i1 (M i)
  let M_vv := replaceRow M i (M i1)
  have hboth0 : Φ M_both = S.zero := by
    apply hΦ.adj_eq M_both i hi
    intro c
    unfold M_both replaceRow
    dsimp [i1]
    have hne : i.val ≠ i.val + 1 := by omega
    simp [hne]
  have hsplit_top : Φ M_both = S.add (Φ M_u_sum) (Φ M_v_sum) := by
    apply hΦ.row_add M_u_sum M_v_sum M_both i
    · intro r hr c
      have hrv : r.val ≠ i.val := fun hv => hr (Fin.ext hv)
      unfold M_both M_u_sum M_v_sum replaceRow
      by_cases hr1 : r.val = i1.val <;> simp [hrv, hr1]
    · intro c
      unfold M_both M_u_sum M_v_sum replaceRow sumVec
      have hne : i.val ≠ i1.val := by dsimp [i1]; omega
      simp [hne]
  have hsplit_u : Φ M_u_sum = S.add (Φ M_uu) (Φ M) := by
    apply hΦ.row_add M_uu M M_u_sum i1
    · intro r hr c
      have hrv : r.val ≠ i1.val := fun hv => hr (Fin.ext hv)
      unfold M_u_sum M_uu replaceRow
      simp [hrv]
    · intro c
      unfold M_u_sum M_uu replaceRow sumVec
      simp
  have hsplit_v : Φ M_v_sum = S.add (Φ (swapRows i i1 M)) (Φ M_vv) := by
    apply hΦ.row_add (swapRows i i1 M) M_vv M_v_sum i1
    · intro r hr c
      have hrv : r.val ≠ i1.val := fun hv => hr (Fin.ext hv)
      unfold M_v_sum M_vv swapRows replaceRow
      by_cases hri : r.val = i.val
      · have hne_ii1 : i.val ≠ i1.val := by dsimp [i1]; omega
        simp [hrv, hri, hne_ii1]
      · simp [hrv, hri]
    · intro c
      unfold M_v_sum M_vv swapRows replaceRow sumVec
      have hne : i1.val ≠ i.val := by dsimp [i1]; omega
      simp [hne]
  have huu0 : Φ M_uu = S.zero := by
    apply hΦ.adj_eq M_uu i hi
    intro c
    unfold M_uu replaceRow
    dsimp [i1]
    have hne : i.val ≠ i.val + 1 := by omega
    simp [hne]
  have hvv0 : Φ M_vv = S.zero := by
    apply hΦ.adj_eq M_vv i hi
    intro c
    unfold M_vv replaceRow
    dsimp [i1]
    have hne : i.val + 1 ≠ i.val := by omega
    simp [hne]
  rw [hsplit_u, huu0, S.zero_add, hsplit_v, hvv0, S.add_zero] at hsplit_top
  rw [hboth0] at hsplit_top
  exact S.neg_eq_of_add_eq_zero hsplit_top.symm

theorem alt_eq_rows_lt {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R n → R}
    (hΦ : IsAltRowMultilinear S n Φ) :
    ∀ (d : Nat) (M : Mat R n) (i k : Fin n),
      i.val < k.val → k.val - i.val ≤ d →
      (∀ c : Fin n, M i c = M k c) → Φ M = S.zero
  | 0, _, i, k, hik, hd, _ => by omega
  | d + 1, M, i, k, hik, hd, heq => by
      by_cases h1 : k.val = i.val + 1
      · have hk_eq : k = ⟨i.val + 1, by omega⟩ := Fin.ext h1
        rw [hk_eq] at heq
        exact hΦ.adj_eq M i (by omega) heq
      · let km1 : Fin n := ⟨k.val - 1, by omega⟩
        have hkm1_succ : km1.val + 1 < n := by dsimp [km1]; omega
        have hk_eq : (⟨km1.val + 1, hkm1_succ⟩ : Fin n) = k := by
          apply Fin.ext
          dsimp [km1]
          omega
        let M' := swapRows km1 ⟨km1.val + 1, hkm1_succ⟩ M
        have hswap := alt_swap_adj hΦ M km1 hkm1_succ
        have hM'0 : Φ M' = S.zero := by
          apply alt_eq_rows_lt hΦ d M' i km1 (by dsimp [km1]; omega) (by dsimp [km1]; omega)
          intro c
          dsimp [M']
          unfold swapRows
          have hi1 : i.val ≠ km1.val := by dsimp [km1]; omega
          have hi2 : i.val ≠ km1.val + 1 := by dsimp [km1]; omega
          simp only [hi1, hi2, ↓reduceIte]
          rw [hk_eq]
          exact heq c
        have hneg : S.neg (Φ M) = S.zero := hswap.symm.trans hM'0
        have hnn := congrArg S.neg hneg
        rw [S.neg_neg, S.neg_zero] at hnn
        exact hnn

theorem alt_row_finSum {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R n → R}
    (hΦ : IsAltRowMultilinear S n Φ) (M : Mat R n) (i : Fin n) :
    ∀ (m : Nat) (w : Fin m → R) (V : Fin m → Fin n → R),
      Φ (replaceRow M i (fun c => S.finSum m (fun j => S.mul (w j) (V j c)))) =
        S.finSum m (fun j => S.mul (w j) (Φ (replaceRow M i (V j))))
  | 0, _, _ => by
      simp only [CRing.finSum]
      apply alt_row_zero hΦ _ i
      intro c
      unfold replaceRow
      simp
  | m + 1, w, V => by
      simp only [CRing.finSum]
      let headM := replaceRow M i (fun c => S.mul (w ⟨0, Nat.zero_lt_succ m⟩) (V ⟨0, Nat.zero_lt_succ m⟩ c))
      let tailM := replaceRow M i (fun c => S.finSum m (fun j => S.mul (w j.succ) (V j.succ c)))
      have hadd := hΦ.row_add headM tailM
          (replaceRow M i (fun c => S.add (S.mul (w ⟨0, Nat.zero_lt_succ m⟩) (V ⟨0, Nat.zero_lt_succ m⟩ c))
            (S.finSum m (fun j => S.mul (w j.succ) (V j.succ c))))) i
          (by
            intro r hr c
            have hrv : r.val ≠ i.val := fun hv => hr (Fin.ext hv)
            unfold headM tailM replaceRow
            simp [hrv])
          (by
            intro c
            unfold headM tailM replaceRow
            simp)
      have hsc := hΦ.row_scale (w ⟨0, Nat.zero_lt_succ m⟩)
          (replaceRow M i (V ⟨0, Nat.zero_lt_succ m⟩)) headM i
          (by
            intro r hr c
            have hrv : r.val ≠ i.val := fun hv => hr (Fin.ext hv)
            unfold headM replaceRow
            simp [hrv])
          (by
            intro c
            unfold headM replaceRow
            simp)
      rw [hadd, hsc, alt_row_finSum hΦ M i m (fun j => w j.succ) (fun j => V j.succ)]

/-- Standard basis vector `e_j` of length `n`. -/
def stdBasis {R : Type} (S : CRing R) (n : Nat) (j : Fin n) : Fin n → R :=
  fun c => if c.val = j.val then S.one else S.zero

/-- Insert `e_j` as row `0`, `0` in column `j` below row `0`, and `N : Mat R n` in the complement. -/
def insertRow0ColJ {R : Type} (S : CRing R) {n : Nat} (j : Fin (n + 1)) (N : Mat R n) :
    Mat R (n + 1) :=
  fun r c =>
    if hr : r.val = 0 then
      if c.val = j.val then S.one else S.zero
    else
      if hc : c.val = j.val then
        S.zero
      else if hlt : c.val < j.val then
        N ⟨r.val - 1, by omega⟩ ⟨c.val, by omega⟩
      else
        N ⟨r.val - 1, by omega⟩ ⟨c.val - 1, by omega⟩

theorem insertRow0ColJ_altMultilinear {R : Type} {S : CRing R} {n : Nat}
    {Φ : Mat R (n + 1) → R} (hΦ : IsAltRowMultilinear S (n + 1) Φ) (j : Fin (n + 1)) :
    IsAltRowMultilinear S n (fun N => Φ (insertRow0ColJ S j N)) where
  row_add := by
    intro N₁ N₂ N i hother hsum
    apply hΦ.row_add (insertRow0ColJ S j N₁) (insertRow0ColJ S j N₂) (insertRow0ColJ S j N) i.succ
    · intro r hr c
      unfold insertRow0ColJ
      by_cases hr0 : r.val = 0
      · simp [hr0]
      · have hne_idx : (⟨r.val - 1, by omega⟩ : Fin n) ≠ i := by
          intro heq
          apply hr
          apply Fin.ext
          have hv := congrArg Fin.val heq
          dsimp at hv
          simp only [Fin.val_succ]
          omega
        by_cases hc : c.val = j.val
        · simp [hr0, hc]
        · by_cases hlt : c.val < j.val
          · simp only [hr0, hc, hlt, ↓reduceDIte]
            exact hother ⟨r.val - 1, by omega⟩ hne_idx ⟨c.val, by omega⟩
          · simp only [hr0, hc, hlt, ↓reduceDIte]
            exact hother ⟨r.val - 1, by omega⟩ hne_idx ⟨c.val - 1, by omega⟩
    · intro c
      unfold insertRow0ColJ
      have hr0 : ¬ ((i.succ).val = 0) := by simp
      have hsub : (i.succ).val - 1 = i.val := by simp
      have hfin : (⟨(i.succ).val - 1, by omega⟩ : Fin n) = i := Fin.ext hsub
      by_cases hc : c.val = j.val
      · simp [hr0, hc, S.zero_add]
      · by_cases hlt : c.val < j.val
        · simp only [hr0, hc, hlt, ↓reduceDIte, hfin]
          exact hsum ⟨c.val, by omega⟩
        · simp only [hr0, hc, hlt, ↓reduceDIte, hfin]
          exact hsum ⟨c.val - 1, by omega⟩
  row_scale := by
    intro a N₁ N i hother hsc
    apply hΦ.row_scale a (insertRow0ColJ S j N₁) (insertRow0ColJ S j N) i.succ
    · intro r hr c
      unfold insertRow0ColJ
      by_cases hr0 : r.val = 0
      · simp [hr0]
      · have hne_idx : (⟨r.val - 1, by omega⟩ : Fin n) ≠ i := by
          intro heq
          apply hr
          apply Fin.ext
          have hv := congrArg Fin.val heq
          dsimp at hv
          simp only [Fin.val_succ]
          omega
        by_cases hc : c.val = j.val
        · simp [hr0, hc]
        · by_cases hlt : c.val < j.val
          · simp only [hr0, hc, hlt, ↓reduceDIte]
            exact hother ⟨r.val - 1, by omega⟩ hne_idx ⟨c.val, by omega⟩
          · simp only [hr0, hc, hlt, ↓reduceDIte]
            exact hother ⟨r.val - 1, by omega⟩ hne_idx ⟨c.val - 1, by omega⟩
    · intro c
      unfold insertRow0ColJ
      have hr0 : ¬ ((i.succ).val = 0) := by simp
      have hfin : (⟨(i.succ).val - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp)
      by_cases hc : c.val = j.val
      · simp [hr0, hc, S.mul_zero]
      · by_cases hlt : c.val < j.val
        · simp only [hr0, hc, hlt, ↓reduceDIte, hfin]
          exact hsc ⟨c.val, by omega⟩
        · simp only [hr0, hc, hlt, ↓reduceDIte, hfin]
          exact hsc ⟨c.val - 1, by omega⟩
  adj_eq := by
    intro N i hi heq
    have hi_succ : (i.succ).val + 1 < n + 1 := by simp; omega
    apply hΦ.adj_eq (insertRow0ColJ S j N) i.succ hi_succ
    intro c
    unfold insertRow0ColJ
    have hr1 : ¬ ((i.succ).val = 0) := by simp
    have hr2 : ¬ ((⟨(i.succ).val + 1, hi_succ⟩ : Fin (n + 1)).val = 0) := by simp
    have hf1 : (⟨(i.succ).val - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp)
    have hf2 : (⟨(⟨(i.succ).val + 1, hi_succ⟩ : Fin (n + 1)).val - 1, by omega⟩ : Fin n) =
        ⟨i.val + 1, hi⟩ := Fin.ext (by simp)
    by_cases hc : c.val = j.val
    · simp [hr1, hr2, hc]
    · by_cases hlt : c.val < j.val
      · simp only [hr1, hr2, hc, hlt, ↓reduceDIte, hf1, hf2]
        exact heq ⟨c.val, by omega⟩
      · simp only [hr1, hr2, hc, hlt, ↓reduceDIte, hf1, hf2]
        exact heq ⟨c.val - 1, by omega⟩

/-- Partial column-clearing matrix: rows `1 .. k` have column `j` zeroed out. -/
def clearColStage {R : Type} (S : CRing R) {n : Nat} (A : Mat R (n + 1)) (j : Fin (n + 1))
    (k : Nat) : Mat R (n + 1) :=
  fun r c =>
    if r.val = 0 then
      if c.val = j.val then S.one else S.zero
    else if r.val ≤ k then
      if c.val = j.val then S.zero else A r c
    else
      A r c

theorem alt_clearColStage_eq {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R (n + 1) → R}
    (hΦ : IsAltRowMultilinear S (n + 1) Φ) (A : Mat R (n + 1)) (j : Fin (n + 1)) :
    ∀ k : Nat, k ≤ n → Φ (clearColStage S A j 0) = Φ (clearColStage S A j k)
  | 0, _ => rfl
  | k + 1, hk => by
      rw [alt_clearColStage_eq hΦ A j k (by omega)]
      let rk : Fin (n + 1) := ⟨k + 1, by omega⟩
      let ejM := replaceRow (clearColStage S A j (k + 1)) rk (stdBasis S (n + 1) j)
      let scM := replaceRow (clearColStage S A j (k + 1)) rk
          (fun c => S.mul (A rk j) (stdBasis S (n + 1) j c))
      have hadd := hΦ.row_add (clearColStage S A j (k + 1)) scM (clearColStage S A j k) rk
          (by
            intro r hr c
            have hrv : r.val ≠ k + 1 := fun hv => hr (Fin.ext hv)
            unfold scM replaceRow clearColStage
            dsimp [rk]
            by_cases hr0 : r.val = 0
            · simp [hrv, hr0]
            · by_cases hle : r.val ≤ k
              · have hle2 : r.val ≤ k + 1 := by omega
                simp [hrv, hr0, hle, hle2]
              · have hle2 : ¬ (r.val ≤ k + 1) := by omega
                simp [hrv, hr0, hle, hle2])
          (by
            intro c
            unfold scM replaceRow clearColStage stdBasis
            have hr0 : ¬ (rk.val = 0) := by dsimp [rk]; omega
            have hle1 : ¬ (rk.val ≤ k) := by dsimp [rk]; omega
            have hle2 : rk.val ≤ k + 1 := by dsimp [rk]; omega
            simp only [hr0, hle1, hle2, ↓reduceIte]
            by_cases hc : c.val = j.val
            · have hcj : c = j := Fin.ext hc
              subst hcj
              simp [S.mul_one, S.zero_add]
            · simp [hc, S.mul_zero, S.add_zero])
      have hsc := hΦ.row_scale (A rk j) ejM scM rk
          (by
            intro r hr c
            have hrv : r.val ≠ rk.val := fun hv => hr (Fin.ext hv)
            unfold ejM scM replaceRow
            simp [hrv])
          (by
            intro c
            unfold ejM scM replaceRow
            simp)
      have hej0 : Φ ejM = S.zero := by
        apply alt_eq_rows_lt hΦ (k + 1) ejM ⟨0, Nat.zero_lt_succ n⟩ rk (by dsimp [rk]; omega) (by dsimp [rk]; omega)
        intro c
        unfold ejM replaceRow clearColStage stdBasis
        have h0_ne : (0 : Nat) ≠ rk.val := by dsimp [rk]; omega
        simp [h0_ne]
      rw [hadd, hsc, hej0, S.mul_zero, S.add_zero]

/-- Stage `m` of shifting `e_j` from row `m` to row `j` in `I_{n+1}`. -/
def permStdMat {R : Type} (S : CRing R) (n : Nat) (j : Fin (n + 1)) (m : Nat) : Mat R (n + 1) :=
  fun r c =>
    if r.val < m then
      if c.val = r.val then S.one else S.zero
    else if r.val = m then
      if c.val = j.val then S.one else S.zero
    else if r.val ≤ j.val then
      if c.val + 1 = r.val then S.one else S.zero
    else
      if c.val = r.val then S.one else S.zero

theorem alt_permStdMat_step {R : Type} {S : CRing R} {n : Nat} {Φ : Mat R (n + 1) → R}
    (hΦ : IsAltRowMultilinear S (n + 1) Φ) (j : Fin (n + 1)) :
    ∀ d m : Nat, m ≤ j.val → j.val - m = d →
      Φ (permStdMat S n j m) = S.mul (S.altSign d) (Φ (permStdMat S n j j.val))
  | 0, m, hmj, hd => by
      have hmeq : m = j.val := by omega
      subst hmeq
      simp only [CRing.altSign, S.one_mul]
  | d + 1, m, hmj, hd => by
      have hlt : m < j.val := by omega
      have hm1 : m + 1 < n + 1 := by omega
      have hswap_eq : swapRows ⟨m, by omega⟩ ⟨m + 1, hm1⟩ (permStdMat S n j (m + 1)) =
          permStdMat S n j m := by
        funext r c
        unfold swapRows permStdMat
        by_cases hrm : r.val = m
        · have hnot_lt : ¬ (m + 1 < m + 1) := by omega
          have hnot_lt2 : ¬ (r.val < m) := by omega
          simp [hrm, hnot_lt, hnot_lt2]
        · by_cases hrm1 : r.val = m + 1
          · have hlt1 : m < m + 1 := by omega
            have hnot_lt2 : ¬ (r.val < m) := by omega
            have hle : r.val ≤ j.val := by omega
            have hceq : (c.val = m) ↔ (c.val + 1 = r.val) := by omega
            simp only [hrm, hrm1, hlt1, ↓reduceIte]
            have h1 : ¬ (m + 1 < m) := by omega
            have h2 : ¬ (m + 1 = m) := by omega
            have h3 : m + 1 ≤ j.val := by omega
            simp only [h1, h2, h3, ↓reduceIte]
            by_cases hc : c.val = m
            · have hc2 : c.val + 1 = m + 1 := by omega
              simp [hc, hc2]
            · have hc2 : c.val + 1 ≠ m + 1 := by omega
              simp [hc, hc2]
          · by_cases h1 : r.val < m
            · have h2 : r.val < m + 1 := by omega
              simp [hrm, hrm1, h1, h2]
            · have h2 : ¬ (r.val < m + 1) := by omega
              simp [hrm, hrm1, h1, h2]
      rw [← hswap_eq, alt_swap_adj hΦ (permStdMat S n j (m + 1)) ⟨m, by omega⟩ hm1]
      rw [alt_permStdMat_step hΦ j d (m + 1) (by omega) (by omega)]
      simp only [CRing.altSign, S.neg_mul]

/-- **Universal Uniqueness of Alternating Row-Multilinear Forms:**
Every alternating row-multilinear form `Φ` satisfies `Φ(A) = det(A) · Φ(I_n)`. -/
theorem alt_eq_det_mul_id {R : Type} (S : CRing R) :
    ∀ (n : Nat) (Φ : Mat R n → R),
      IsAltRowMultilinear S n Φ →
      ∀ A : Mat R n, Φ A = S.mul (det S A) (Φ (matId S n))
  | 0, Φ, _, A => by
      have hA : A = matId S 0 := by funext i; exact Fin.elim0 i
      rw [hA]
      simp only [det, S.one_mul]
  | n + 1, Φ, hΦ, A => by
      let r0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      have hrow0 : A = replaceRow A r0
          (fun c => S.finSum (n + 1) (fun j => S.mul (A r0 j) (stdBasis S (n + 1) j c))) := by
        funext r c
        unfold replaceRow stdBasis
        by_cases hr : r.val = 0
        · have hr_eq : r = r0 := Fin.ext hr
          subst hr_eq
          simp only [↓reduceIte]
          rw [S.finSum_eq_single c]
          · simp [S.mul_one]
          · intro j hj
            have hcv : c.val ≠ j.val := fun hv => hj (Fin.ext hv).symm
            simp [hcv, S.mul_zero]
        · simp [r0, hr]
      have hexp := alt_row_finSum hΦ A r0 (n + 1) (fun j => A r0 j) (fun j => stdBasis S (n + 1) j)
      rw [← hrow0] at hexp
      rw [hexp]
      simp only [det]
      rw [← S.finSum_mul_right]
      apply S.finSum_congr
      intro j
      -- Show `replaceRow A r0 (stdBasis S (n + 1) j) = clearColStage S A j 0`
      have hst0 : replaceRow A r0 (stdBasis S (n + 1) j) = clearColStage S A j 0 := by
        funext r c
        unfold replaceRow clearColStage stdBasis
        by_cases hr : r.val = 0
        · simp [r0, hr]
        · have hnot0 : ¬ (r.val ≤ 0) := by omega
          simp [r0, hr, hnot0]
      -- Show `clearColStage S A j n = insertRow0ColJ S j (minor A r0 j)`
      have hstn : clearColStage S A j n = insertRow0ColJ S j (minor A r0 j) := by
        funext r c
        unfold clearColStage insertRow0ColJ minor skipIdx
        dsimp [r0]
        by_cases hr : r.val = 0
        · simp [hr]
        · have hle : r.val ≤ n := by omega
          have hr_not_lt0 : ¬ (r.val - 1 < 0) := by omega
          have hr_fin : (⟨r.val - 1 + 1, by omega⟩ : Fin (n + 1)) = r := Fin.ext (by dsimp; omega)
          by_cases hc : c.val = j.val
          · simp [hr, hle, hc]
          · by_cases hlt : c.val < j.val
            · simp only [hr, hle, hc, ↓reduceIte, hlt, ↓reduceDIte, hr_not_lt0, hr_fin]
            · have hsub_not_lt : ¬ (c.val - 1 < j.val) := by omega
              have hc_fin : (⟨c.val - 1 + 1, by omega⟩ : Fin (n + 1)) = c := Fin.ext (by dsimp; omega)
              simp only [hr, hle, hc, ↓reduceIte, hlt, ↓reduceDIte, hr_not_lt0, hsub_not_lt,
                hr_fin, hc_fin]
      rw [hst0, alt_clearColStage_eq hΦ A j n (Nat.le_refl n), hstn]
      have hΨ := insertRow0ColJ_altMultilinear hΦ j
      rw [alt_eq_det_mul_id S n (fun N => Φ (insertRow0ColJ S j N)) hΨ (minor A r0 j)]
      have hperm0 : insertRow0ColJ S j (matId S n) = permStdMat S n j 0 := by
        funext r c
        unfold insertRow0ColJ permStdMat matId
        have hnot_lt0 : ¬ (r.val < 0) := by omega
        by_cases hr : r.val = 0
        · simp [hr, hnot_lt0]
        · by_cases hc : c.val = j.val
          · by_cases hle : r.val ≤ j.val
            · have hne : j.val + 1 ≠ r.val := by omega
              simp [hr, hnot_lt0, hc, hle, hne]
            · have hne : j.val ≠ r.val := by omega
              simp [hr, hnot_lt0, hc, hle, hne]
          · by_cases hlt : c.val < j.val
            · by_cases hle : r.val ≤ j.val
              · simp only [hr, hnot_lt0, hc, hlt, hle, ↓reduceDIte, ↓reduceIte]
                by_cases hcr : r.val - 1 = c.val
                · have hcr2 : c.val + 1 = r.val := by omega
                  simp [hcr, hcr2]
                · have hcr2 : c.val + 1 ≠ r.val := by omega
                  simp [hcr, hcr2]
              · have hne1 : r.val - 1 ≠ c.val := by omega
                have hne2 : c.val ≠ r.val := by omega
                simp [hr, hnot_lt0, hc, hlt, hle, hne1, hne2]
            · by_cases hle : r.val ≤ j.val
              · have hne1 : r.val - 1 ≠ c.val - 1 := by omega
                have hne2 : c.val + 1 ≠ r.val := by omega
                simp [hr, hnot_lt0, hc, hlt, hle, hne1, hne2]
              · simp only [hr, hnot_lt0, hc, hlt, hle, ↓reduceDIte, ↓reduceIte]
                by_cases hcr : r.val - 1 = c.val - 1
                · have hcr2 : c.val = r.val := by omega
                  simp [hcr, hcr2]
                · have hcr2 : c.val ≠ r.val := by omega
                  simp [hcr, hcr2]
      have hpermj : permStdMat S n j j.val = matId S (n + 1) := by
        funext r c
        unfold permStdMat matId
        by_cases hlt : r.val < j.val
        · simp only [hlt, ↓reduceIte]
          by_cases hcr : c.val = r.val <;> (have hrc : r.val = c.val ↔ c.val = r.val := eq_comm; simp [hcr, hrc])
        · by_cases heq : r.val = j.val
          · simp only [hlt, heq, ↓reduceIte]
            by_cases hcj : c.val = j.val <;> (have hjc : j.val = c.val ↔ c.val = j.val := eq_comm; simp [hcj, hjc])
          · have hnot_le : ¬ (r.val ≤ j.val) := by omega
            simp only [hlt, heq, hnot_le, ↓reduceIte]
            by_cases hcr : c.val = r.val <;> (have hrc : r.val = c.val ↔ c.val = r.val := eq_comm; simp [hcr, hrc])
      rw [hperm0, alt_permStdMat_step hΦ j j.val 0 (Nat.zero_le j.val) (Nat.sub_zero j.val), hpermj]
      -- Rearrange `A_{0,j} * (det(minor) * (altSign j * Φ(I))) = (altSign j * (A_{0,j} * det(minor))) * Φ(I)`
      let a0 := A r0 j
      let dm := det S (minor A r0 j)
      let sg := S.altSign j.val
      let phiI := Φ (matId S (n + 1))
      change S.mul a0 (S.mul dm (S.mul sg phiI)) = S.mul (S.mul sg (S.mul a0 dm)) phiI
      rw [← S.mul_assoc dm sg phiI, S.mul_comm dm sg, S.mul_assoc sg dm phiI]
      rw [← S.mul_assoc a0 sg (S.mul dm phiI), S.mul_comm a0 sg]
      rw [S.mul_assoc sg a0 (S.mul dm phiI), ← S.mul_assoc a0 dm phiI]
      rw [← S.mul_assoc sg (S.mul a0 dm) phiI]

/-! ### Proof that `det S` Itself Is Alternating Row-Multilinear -/

theorem rect_antisym_sum_zero {R : Type} (S : CRing R) :
    ∀ (m : Nat) (T : Fin (m + 2) → Fin (m + 1) → R),
      (∀ (p : Fin (m + 1)) (q : Fin (m + 2)), p.val < q.val →
        S.add (T q p) (T ⟨p.val, by omega⟩ ⟨q.val - 1, by omega⟩) = S.zero) →
      S.finSum (m + 2) (fun j => S.finSum (m + 1) (fun k => T j k)) = S.zero
  | 0, T, hanti => by
      simp only [CRing.finSum, S.add_zero]
      have h01 := hanti ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
      rw [S.add_comm]
      exact h01
  | m + 1, T, hanti => by
      have houter : S.finSum (m + 1 + 2) (fun j => S.finSum (m + 1 + 1) (fun k => T j k)) =
          S.add (S.finSum (m + 2) (fun k => T ⟨0, Nat.zero_lt_succ (m + 2)⟩ k))
            (S.finSum (m + 2) (fun j' =>
              S.add (T j'.succ ⟨0, Nat.zero_lt_succ (m + 1)⟩)
                (S.finSum (m + 1) (fun k' => T j'.succ k'.succ)))) := rfl
      rw [houter, S.finSum_add, ← S.add_assoc]
      have hpair :
          S.add (S.finSum (m + 2) (fun k => T ⟨0, Nat.zero_lt_succ (m + 2)⟩ k))
            (S.finSum (m + 2) (fun j' => T j'.succ ⟨0, Nat.zero_lt_succ (m + 1)⟩)) = S.zero := by
        rw [← S.finSum_add, ← S.finSum_zero (m + 2)]
        apply S.finSum_congr
        intro r
        rw [S.add_comm]
        have hpq := hanti ⟨0, Nat.zero_lt_succ (m + 1)⟩ r.succ (by simp)
        have hsub : (⟨(r.succ).val - 1, by omega⟩ : Fin (m + 2)) = r := Fin.ext (by simp)
        rw [hsub] at hpq
        exact hpq
      rw [hpair, S.zero_add]
      apply rect_antisym_sum_zero S m (fun j' k' => T j'.succ k'.succ)
      intro p q hpq
      have hstep := hanti p.succ q.succ (by simp; exact hpq)
      have hp_eq : (⟨(p.succ).val, by omega⟩ : Fin (m + 3)) =
          (⟨p.val, by omega⟩ : Fin (m + 2)).succ := Fin.ext rfl
      have hq_eq : (⟨(q.succ).val - 1, by omega⟩ : Fin (m + 2)) =
          (⟨q.val - 1, by omega⟩ : Fin (m + 1)).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hp_eq, hq_eq] at hstep
      exact hstep

theorem double_minor_comm {R : Type} {m : Nat} (M : Mat R (m + 2))
    (p : Fin (m + 1)) (q : Fin (m + 2)) (hpq : p.val < q.val) :
    minor (minor M ⟨0, Nat.zero_lt_succ (m + 1)⟩ q) ⟨0, Nat.zero_lt_succ m⟩ p =
      minor (minor M ⟨0, Nat.zero_lt_succ (m + 1)⟩ ⟨p.val, by omega⟩)
        ⟨0, Nat.zero_lt_succ m⟩ ⟨q.val - 1, by omega⟩ := by
  funext r c
  unfold minor skipIdx
  have hr1 : ¬ (r.val < 0) := by omega
  have hr2 : ¬ (r.val + 1 < 0) := by omega
  simp only [hr1, hr2, ↓reduceIte]
  by_cases hcp : c.val < p.val
  · have hcq1 : c.val < q.val := by omega
    have hcq2 : c.val < q.val - 1 := by omega
    simp [hcp, hcq1, hcq2]
  · by_cases hcq : c.val < q.val - 1
    · have hcp1 : ¬ (c.val + 1 < p.val) := by omega
      have hcq1 : c.val + 1 < q.val := by omega
      simp [hcp, hcq, hcp1, hcq1]
    · have hcq1 : ¬ (c.val + 1 < q.val) := by omega
      have hcp2 : ¬ (c.val + 1 < p.val) := by omega
      simp [hcp, hcq, hcq1, hcp2]

theorem det_isAltRowMultilinear {R : Type} (S : CRing R) (n : Nat) :
    IsAltRowMultilinear S n (det S) := by
  induction n with
  | zero =>
    exact {
      row_add := fun _ _ _ i => Fin.elim0 i
      row_scale := fun _ _ _ i => Fin.elim0 i
      adj_eq := fun _ i => Fin.elim0 i
    }
  | succ n ih =>
    let r0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    exact {
      row_add := by
        intro M₁ M₂ M i hother hsum
        simp only [det]
        rw [← S.finSum_add]
        apply S.finSum_congr
        intro j
        by_cases hi0 : i.val = 0
        · have hi_eq : i = r0 := Fin.ext hi0
          subst hi_eq
          have hmin1 : minor M r0 j = minor M₁ r0 j := by
            funext r c
            unfold minor skipIdx
            have hr : ¬ (r.val < 0) := by omega
            simp only [r0, hr, ↓reduceIte]
            exact (hother ⟨r.val + 1, by omega⟩ (fun heq => by
              have hv := congrArg Fin.val heq; dsimp [r0] at hv; omega) (skipIdx j c)).1
          have hmin2 : minor M₂ r0 j = minor M₁ r0 j := by
            funext r c
            unfold minor skipIdx
            have hr : ¬ (r.val < 0) := by omega
            simp only [r0, hr, ↓reduceIte]
            exact (hother ⟨r.val + 1, by omega⟩ (fun heq => by
              have hv := congrArg Fin.val heq; dsimp [r0] at hv; omega) (skipIdx j c)).2
          rw [hmin1, hmin2, hsum j, S.right_distrib, S.left_distrib]
        · have hr0_ne : r0 ≠ i := fun heq => hi0 (congrArg Fin.val heq).symm
          have hM01 : M r0 j = M₁ r0 j := (hother r0 hr0_ne j).1
          have hM02 : M₂ r0 j = M₁ r0 j := (hother r0 hr0_ne j).2
          let i' : Fin n := ⟨i.val - 1, by omega⟩
          have hmin_add := ih.row_add (minor M₁ r0 j) (minor M₂ r0 j) (minor M r0 j) i'
              (by
                intro r hr c
                unfold minor skipIdx
                have hnot0 : ¬ (r.val < 0) := by omega
                simp only [r0, hnot0, ↓reduceIte]
                apply hother ⟨r.val + 1, by omega⟩
                intro heq
                apply hr
                apply Fin.ext
                have hv := congrArg Fin.val heq
                dsimp [i'] at hv ⊢
                omega)
              (by
                intro c
                unfold minor skipIdx
                have hnot0 : ¬ (i'.val < 0) := by omega
                simp only [r0, hnot0, ↓reduceIte]
                have hfin : (⟨i'.val + 1, by omega⟩ : Fin (n + 1)) = i := Fin.ext (by dsimp [i']; omega)
                rw [hfin]
                exact hsum (skipIdx j c))
          rw [hM01, hM02, hmin_add, S.left_distrib, S.left_distrib]
      row_scale := by
        intro a M₁ M i hother hsc
        simp only [det]
        rw [← S.finSum_mul_left]
        apply S.finSum_congr
        intro j
        by_cases hi0 : i.val = 0
        · have hi_eq : i = r0 := Fin.ext hi0
          subst hi_eq
          have hmin1 : minor M r0 j = minor M₁ r0 j := by
            funext r c
            unfold minor skipIdx
            have hr : ¬ (r.val < 0) := by omega
            simp only [r0, hr, ↓reduceIte]
            exact hother ⟨r.val + 1, by omega⟩ (fun heq => by
              have hv := congrArg Fin.val heq; dsimp [r0] at hv; omega) (skipIdx j c)
          rw [hmin1, hsc j]
          let sg := S.altSign j.val
          let m0 := M₁ r0 j
          let dm := det S (minor M₁ r0 j)
          change S.mul sg (S.mul (S.mul a m0) dm) = S.mul a (S.mul sg (S.mul m0 dm))
          rw [S.mul_assoc a m0 dm, ← S.mul_assoc sg a (S.mul m0 dm),
              S.mul_comm sg a, S.mul_assoc a sg (S.mul m0 dm)]
        · have hr0_ne : r0 ≠ i := fun heq => hi0 (congrArg Fin.val heq).symm
          have hM01 : M r0 j = M₁ r0 j := hother r0 hr0_ne j
          let i' : Fin n := ⟨i.val - 1, by omega⟩
          have hmin_sc := ih.row_scale a (minor M₁ r0 j) (minor M r0 j) i'
              (by
                intro r hr c
                unfold minor skipIdx
                have hnot0 : ¬ (r.val < 0) := by omega
                simp only [r0, hnot0, ↓reduceIte]
                apply hother ⟨r.val + 1, by omega⟩
                intro heq
                apply hr
                apply Fin.ext
                have hv := congrArg Fin.val heq
                dsimp [i'] at hv ⊢
                omega)
              (by
                intro c
                unfold minor skipIdx
                have hnot0 : ¬ (i'.val < 0) := by omega
                simp only [r0, hnot0, ↓reduceIte]
                have hfin : (⟨i'.val + 1, by omega⟩ : Fin (n + 1)) = i := Fin.ext (by dsimp [i']; omega)
                rw [hfin]
                exact hsc (skipIdx j c))
          rw [hM01, hmin_sc]
          let sg := S.altSign j.val
          let m0 := M₁ r0 j
          let dm := det S (minor M₁ r0 j)
          change S.mul sg (S.mul m0 (S.mul a dm)) = S.mul a (S.mul sg (S.mul m0 dm))
          rw [← S.mul_assoc m0 a dm, S.mul_comm m0 a, S.mul_assoc a m0 dm,
              ← S.mul_assoc sg a (S.mul m0 dm), S.mul_comm sg a, S.mul_assoc a sg (S.mul m0 dm)]
      adj_eq := by
        intro M i hi heq
        cases n with
        | zero => omega
        | succ m =>
          by_cases hi0 : i.val = 0
          · -- Row 0 equals Row 1 on `Mat R (m + 2)`: double Laplace expansion!
            have hi_eq : i = ⟨0, Nat.zero_lt_succ (m + 1)⟩ := Fin.ext hi0
            have hi1_eq : (⟨i.val + 1, hi⟩ : Fin (m + 2)) = ⟨1, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            have heq0 : ∀ c : Fin (m + 2),
                M ⟨0, Nat.zero_lt_succ (m + 1)⟩ c = M ⟨1, by omega⟩ c := by
              intro c
              rw [← hi_eq, ← hi1_eq]
              exact heq c
            let r0' : Fin (m + 2) := ⟨0, Nat.zero_lt_succ (m + 1)⟩
            let r0'' : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
            change S.finSum (m + 2) (fun j =>
                S.mul (S.altSign j.val)
                  (S.mul (M r0' j)
                    (S.finSum (m + 1) (fun k =>
                      S.mul (S.altSign k.val)
                        (S.mul (minor M r0' j r0'' k)
                          (det S (minor (minor M r0' j) r0'' k))))))) = S.zero
            have hpush : ∀ j : Fin (m + 2),
                S.mul (S.altSign j.val)
                  (S.mul (M r0' j)
                    (S.finSum (m + 1) (fun k =>
                      S.mul (S.altSign k.val)
                        (S.mul (minor M r0' j r0'' k)
                          (det S (minor (minor M r0' j) r0'' k)))))) =
                S.finSum (m + 1) (fun k =>
                  S.mul (S.altSign (j.val + k.val))
                    (S.mul (S.mul (M r0' j) (M r0' (skipIdx j k)))
                      (det S (minor (minor M r0' j) r0'' k)))) := by
              intro j
              rw [← S.finSum_mul_left, ← S.finSum_mul_left]
              apply S.finSum_congr
              intro k
              have hm1 : minor M r0' j r0'' k = M r0' (skipIdx j k) := by
                unfold minor skipIdx
                have hn0 : ¬ (0 < 0) := by omega
                simp only [r0'', r0', hn0, ↓reduceIte]
                exact (heq0 (skipIdx j k)).symm
              rw [hm1, S.altSign_add]
              let sj := S.altSign j.val
              let sk := S.altSign k.val
              let a := M r0' j
              let b := M r0' (skipIdx j k)
              let d := det S (minor (minor M r0' j) r0'' k)
              change S.mul sj (S.mul a (S.mul sk (S.mul b d))) =
                S.mul (S.mul sj sk) (S.mul (S.mul a b) d)
              rw [← S.mul_assoc a sk (S.mul b d), S.mul_comm a sk, S.mul_assoc sk a (S.mul b d)]
              rw [← S.mul_assoc sj sk _, ← S.mul_assoc a b d]
            have hcongr := S.finSum_congr hpush
            rw [hcongr]
            apply rect_antisym_sum_zero S m
            intro p q hpq
            let p_ext : Fin (m + 2) := ⟨p.val, by omega⟩
            let q_sub : Fin (m + 1) := ⟨q.val - 1, by omega⟩
            have hsk1 : skipIdx q p = p_ext := by
              unfold skipIdx
              simp [hpq, p_ext]
            have hsk2 : skipIdx p_ext q_sub = q := by
              unfold skipIdx
              have hnot : ¬ (q_sub.val < p_ext.val) := by dsimp [q_sub, p_ext]; omega
              simp only [hnot, ↓reduceIte]
              apply Fin.ext
              dsimp [q_sub]
              omega
            have hdbl := double_minor_comm M p q hpq
            rw [hsk1, hsk2, hdbl]
            have hidx_sum : q.val + p.val = (p_ext.val + q_sub.val) + 1 := by
              dsimp [p_ext, q_sub]
              omega
            rw [hidx_sum]
            simp only [CRing.altSign]
            rw [S.mul_comm (M r0' q) (M r0' p_ext), S.neg_mul]
            exact S.add_left_neg _
          · -- `i.val ≥ 1`: every row-0 minor has adjacent equal rows `i.val - 1` and `i.val`!
            let r0' : Fin (m + 2) := ⟨0, Nat.zero_lt_succ (m + 1)⟩
            change S.finSum (m + 2) (fun j =>
              S.mul (S.altSign j.val)
                (S.mul (M r0' j) (det S (minor M r0' j)))) = S.zero
            rw [← S.finSum_zero (m + 2)]
            apply S.finSum_congr
            intro j
            let i' : Fin (m + 1) := ⟨i.val - 1, by omega⟩
            have hi'_lt : i'.val + 1 < m + 1 := by dsimp [i']; omega
            have hmin0 : det S (minor M r0' j) = S.zero := by
              apply ih.adj_eq (minor M r0' j) i' hi'_lt
              intro c
              unfold minor skipIdx
              have hn1 : ¬ (i'.val < 0) := by omega
              have hn2 : ¬ (i'.val + 1 < 0) := by omega
              simp only [r0', hn1, hn2, ↓reduceIte]
              have hf1 : (⟨i'.val + 1, by omega⟩ : Fin (m + 2)) = i := Fin.ext (by dsimp [i']; omega)
              have hf2 : (⟨i'.val + 1 + 1, by omega⟩ : Fin (m + 2)) = ⟨i.val + 1, hi⟩ :=
                Fin.ext (by dsimp [i']; omega)
              rw [hf1, hf2]
              exact heq (skipIdx j c)
            rw [hmin0, S.mul_zero, S.mul_zero]
    }

theorem det_mul_altMultilinear {R : Type} (S : CRing R) {n : Nat} (B : Mat R n) :
    IsAltRowMultilinear S n (fun A => det S (matMul S A B)) :=
  let hdet := det_isAltRowMultilinear S n
  {
    row_add := by
      intro A₁ A₂ A i hother hsum
      apply hdet.row_add (matMul S A₁ B) (matMul S A₂ B) (matMul S A B) i
      · intro r hr c
        unfold matMul
        constructor
        · apply S.finSum_congr; intro k; rw [(hother r hr k).1]
        · apply S.finSum_congr; intro k; rw [(hother r hr k).2]
      · intro c
        unfold matMul
        rw [← S.finSum_add]
        apply S.finSum_congr
        intro k
        rw [hsum k, S.right_distrib]
    row_scale := by
      intro a A₁ A i hother hsc
      apply hdet.row_scale a (matMul S A₁ B) (matMul S A B) i
      · intro r hr c
        unfold matMul
        apply S.finSum_congr; intro k; rw [hother r hr k]
      · intro c
        unfold matMul
        rw [← S.finSum_mul_left]
        apply S.finSum_congr
        intro k
        rw [hsc k, S.mul_assoc]
    adj_eq := by
      intro A i hi heq
      apply hdet.adj_eq (matMul S A B) i hi
      intro c
      unfold matMul
      apply S.finSum_congr
      intro k
      rw [heq k]
  }

/-- **Full Multiplicativity of the Determinant (`det (A * B) = det A * det B`):**
Valid for all `n × n` matrices `A, B` over any commutative ring `S : CRing R`. -/
theorem det_mul {R : Type} (S : CRing R) {n : Nat} (A B : Mat R n) :
    det S (matMul S A B) = S.mul (det S A) (det S B) := by
  have h := alt_eq_det_mul_id S n (fun M => det S (matMul S M B))
      (det_mul_altMultilinear S B) A
  rw [matId_mul S B] at h
  exact h

end Conjecture00000000593
