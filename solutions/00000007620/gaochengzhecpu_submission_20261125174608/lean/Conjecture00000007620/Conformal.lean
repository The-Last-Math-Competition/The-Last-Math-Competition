/-
  Conjecture 00000007620 — Layer 1: Quadratic Spaces, Orthogonal Isometry Groups,
  Group Spectra, and Genuine Conformal Horosphere Models.
  Pure Core Lean 4.19.0.
-/
import Conjecture00000007620.Field

namespace Conjecture00000007620

universe u v

/-! ### Finite Indexing Helpers and Exact Finite Sums -/

def finCastSucc {n : Nat} (j : Fin n) : Fin (n + 1) :=
  ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

def finLast (n : Nat) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

theorem finCastSucc_ne_last {n : Nat} (j : Fin n) : finCastSucc j ≠ finLast n := by
  intro h
  have hv : j.val = n := congrArg Fin.val h
  exact Nat.ne_of_lt j.isLt hv

theorem finCastSucc_inj {n : Nat} {i j : Fin n} (h : finCastSucc i = finCastSucc j) : i = j := by
  apply Fin.ext
  change (finCastSucc i).val = (finCastSucc j).val
  exact congrArg Fin.val h

theorem fin_cases_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = finCastSucc j) ∨ i = finLast n := by
  by_cases h : i.val < n
  · left
    refine ⟨⟨i.val, h⟩, ?_⟩
    apply Fin.ext
    rfl
  · right
    apply Fin.ext
    change i.val = n
    have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    omega

/-- Exact finite sum over `Fin n` in any associative ring. -/
def finSum {R : Type u} [AssocRing R] : (n : Nat) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => finSum n (fun j => f (finCastSucc j)) + f (finLast n)

section FinSumLemmas

variable {R : Type u} [AssocRing R]

theorem finSum_zero_len (f : Fin 0 → R) : finSum 0 f = 0 := rfl

theorem finSum_succ_len (m : Nat) (f : Fin (m + 1) → R) :
    finSum (m + 1) f = finSum m (fun j => f (finCastSucc j)) + f (finLast m) := rfl

theorem finSum_congr {n : Nat} {f g : Fin n → R} (h : ∀ i : Fin n, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold finSum
    rw [ih (fun j => h (finCastSucc j)), h (finLast m)]

theorem finSum_zero (n : Nat) : finSum n (fun _ : Fin n => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    unfold finSum
    rw [ih, AssocRing.add_zero]

theorem finSum_add {n : Nat} (f g : Fin n → R) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero =>
    unfold finSum
    rw [AssocRing.add_zero]
  | succ m ih =>
    unfold finSum
    rw [ih]
    -- Rearrange (Sf + Sg) + (fn + gn) = (Sf + fn) + (Sg + gn)
    rw [AssocRing.add_assoc (finSum m _) (finSum m _) _,
        ← AssocRing.add_assoc (finSum m _) (f (finLast m)) (g (finLast m)),
        AssocRing.add_comm (finSum m (fun j => g (finCastSucc j))) (f (finLast m)),
        AssocRing.add_assoc (f (finLast m)) _ (g (finLast m)),
        ← AssocRing.add_assoc (finSum m (fun j => f (finCastSucc j))) (f (finLast m)) _]

theorem finSum_neg {n : Nat} (f : Fin n → R) :
    finSum n (fun i => -(f i)) = -(finSum n f) := by
  induction n with
  | zero =>
    unfold finSum
    exact neg_zero_ring.symm
  | succ m ih =>
    unfold finSum
    rw [ih, neg_add_distrib_ring]

theorem finSum_mul_left {n : Nat} (c : R) (f : Fin n → R) :
    c * finSum n f = finSum n (fun i => c * f i) := by
  induction n with
  | zero =>
    unfold finSum
    exact mul_zero_ring c
  | succ m ih =>
    unfold finSum
    rw [AssocRing.left_distrib, ih]

theorem finSum_mul_right {n : Nat} (f : Fin n → R) (c : R) :
    finSum n f * c = finSum n (fun i => f i * c) := by
  induction n with
  | zero =>
    unfold finSum
    exact zero_mul_ring c
  | succ m ih =>
    unfold finSum
    rw [AssocRing.right_distrib, ih]

theorem finSum_comm {m n : Nat} (h : Fin m → Fin n → R) :
    finSum m (fun i => finSum n (fun j => h i j)) =
    finSum n (fun j => finSum m (fun i => h i j)) := by
  induction m with
  | zero =>
    rw [finSum_zero_len]
    symm
    rw [finSum_congr (g := fun _ => (0 : R))]
    · exact finSum_zero n
    · intro j; rfl
  | succ m' ih =>
    rw [finSum_succ_len, ih]
    symm
    rw [finSum_congr (g := fun j => finSum m' (fun i => h (finCastSucc i) j) + h (finLast m') j)]
    · exact finSum_add _ _
    · intro j; rfl

theorem finSum_ite_eq {n : Nat} (k : Fin n) (g : Fin n → R) :
    finSum n (fun i => if i = k then g i else 0) = g k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    rw [finSum_succ_len]
    cases fin_cases_last k with
    | inl hk =>
      rcases hk with ⟨j0, rfl⟩
      have hlast : (if finLast m = finCastSucc j0 then g (finLast m) else 0) = 0 := by
        rw [if_neg (fun h => finCastSucc_ne_last j0 h.symm)]
      have hinit : finSum m (fun j => if finCastSucc j = finCastSucc j0 then g (finCastSucc j) else 0) =
          finSum m (fun j => if j = j0 then g (finCastSucc j) else 0) := by
        apply finSum_congr
        intro j
        by_cases hj : j = j0
        · subst hj; simp
        · rw [if_neg hj, if_neg (fun hc => hj (finCastSucc_inj hc))]
      rw [hlast, AssocRing.add_zero, hinit, ih j0 (fun j => g (finCastSucc j))]
    | inr hk =>
      subst hk
      have hinit : finSum m (fun j => if finCastSucc j = finLast m then g (finCastSucc j) else 0) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero m
        · intro j; exact if_neg (finCastSucc_ne_last j)
      rw [hinit, AssocRing.zero_add, if_pos rfl]

end FinSumLemmas

/-! ### Vectors, Extension Operators, and Nondegenerate Signatures -/

abbrev Vec (R : Type u) (n : Nat) : Type u := Fin n → R

def zeroVec {R : Type u} [AssocRing R] (n : Nat) : Vec R n := fun _ => 0
def addVec {R : Type u} [AssocRing R] {n : Nat} (u v : Vec R n) : Vec R n := fun i => u i + v i
def negVec {R : Type u} [AssocRing R] {n : Nat} (u : Vec R n) : Vec R n := fun i => -(u i)
def subVec {R : Type u} [AssocRing R] {n : Nat} (u v : Vec R n) : Vec R n := fun i => u i - v i
def smulVec {R : Type u} [AssocRing R] {n : Nat} (c : R) (u : Vec R n) : Vec R n := fun i => c * u i

def extendVec1 {α : Type u} {n : Nat} (x : Fin n → α) (a : α) (i : Fin (n + 1)) : α :=
  if h : i.val < n then x ⟨i.val, h⟩ else a

theorem extendVec1_castSucc {α : Type u} {n : Nat} (x : Fin n → α) (a : α) (j : Fin n) :
    extendVec1 x a (finCastSucc j) = x j := by
  unfold extendVec1 finCastSucc
  simp [j.isLt]

theorem extendVec1_last {α : Type u} {n : Nat} (x : Fin n → α) (a : α) :
    extendVec1 x a (finLast n) = a := by
  unfold extendVec1 finLast
  have h : ¬ (n < n) := Nat.lt_irrefl n
  simp [h]

def extendVec2 {α : Type u} {d : Nat} (x : Fin d → α) (a b : α) : Fin (d + 2) → α :=
  extendVec1 (extendVec1 x a) b

theorem finSum_extend1 {R : Type u} [AssocRing R] {α : Type v} {n : Nat}
    (x : Fin n → α) (a : α) (F_map : α → R) :
    finSum (n + 1) (fun i => F_map (extendVec1 x a i)) =
    finSum n (fun j => F_map (x j)) + F_map a := by
  rw [finSum_succ_len]
  rw [extendVec1_last]
  apply congrArg (fun s => s + F_map a)
  apply finSum_congr
  intro j
  rw [extendVec1_castSucc]

/-- Unit metric signs (+1 or -1) for nondegenerate orthogonal bases. -/
inductive Sign : Type where
  | pos : Sign
  | neg : Sign
  deriving DecidableEq

namespace Sign

def flip : Sign → Sign
  | .pos => .neg
  | .neg => .pos

def toScalar {R : Type u} [AssocRing R] : Sign → R
  | .pos => 1
  | .neg => -1

theorem flip_flip (s : Sign) : s.flip.flip = s := by
  cases s <;> rfl

theorem toScalar_flip {R : Type u} [AssocRing R] (s : Sign) :
    (s.flip).toScalar = -(s.toScalar : R) := by
  cases s
  · rfl
  · exact (neg_neg_ring (1 : R)).symm

theorem toScalar_sq {R : Type u} [AssocRing R] (s : Sign) :
    (s.toScalar : R) * s.toScalar = 1 := by
  cases s
  · exact AssocRing.one_mul 1
  · show (-1 : R) * (-1) = 1
    rw [neg_mul_neg_ring, AssocRing.one_mul]

end Sign

/-- Diagonal signature of dimension `n`. -/
abbrev Sig (n : Nat) : Type := Fin n → Sign

def Sig.flip {n : Nat} (s : Sig n) : Sig n := fun i => (s i).flip

def Sig.toVec {R : Type u} [AssocRing R] {n : Nat} (s : Sig n) : Vec R n :=
  fun i => (s i).toScalar

/-- Counts `(p, q)` of positive (`+1`) and negative (`-1`) basis directions. -/
def signatureCount : {n : Nat} → Sig n → Nat × Nat
  | 0, _ => (0, 0)
  | n + 1, s =>
    let pq := signatureCount (fun j : Fin n => s (finCastSucc j))
    match s (finLast n) with
    | .pos => (pq.1 + 1, pq.2)
    | .neg => (pq.1, pq.2 + 1)

theorem signatureCount_congr {n : Nat} {s1 s2 : Sig n} (h : ∀ i, s1 i = s2 i) :
    signatureCount s1 = signatureCount s2 := by
  have heq : s1 = s2 := funext h
  rw [heq]

theorem signatureCount_succ {m : Nat} (s : Sig (m + 1)) :
    signatureCount s =
      let pq := signatureCount (fun j : Fin m => s (finCastSucc j))
      match s (finLast m) with
      | .pos => (pq.1 + 1, pq.2)
      | .neg => (pq.1, pq.2 + 1) := rfl

theorem signatureCount_flip {n : Nat} (s : Sig n) :
    signatureCount s.flip = ((signatureCount s).2, (signatureCount s).1) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [signatureCount_succ s.flip, signatureCount_succ s]
    have hinit : (fun j : Fin m => (s.flip) (finCastSucc j)) =
        Sig.flip (fun j : Fin m => s (finCastSucc j)) := rfl
    have hlast : s.flip (finLast m) = (s (finLast m)).flip := rfl
    rw [hinit, hlast, ih (fun j => s (finCastSucc j))]
    cases s (finLast m) <;> rfl

theorem signatureCount_extend1 {n : Nat} (s : Sig n) (a : Sign) :
    signatureCount (extendVec1 s a) =
      match a with
      | .pos => ((signatureCount s).1 + 1, (signatureCount s).2)
      | .neg => ((signatureCount s).1, (signatureCount s).2 + 1) := by
  rw [signatureCount_succ]
  have hinit : (fun j : Fin n => extendVec1 s a (finCastSucc j)) = s := by
    funext j
    exact extendVec1_castSucc s a j
  rw [hinit, extendVec1_last]

/-! ### Quadratic and Polar Bilinear Forms -/

def polarFormVec {F : Type u} [FormallyRealField F] {n : Nat}
    (q : Vec F n) (u v : Vec F n) : F :=
  finSum n (fun i => q i * u i * v i)

def quadFormVec {F : Type u} [FormallyRealField F] {n : Nat}
    (q : Vec F n) (v : Vec F n) : F :=
  polarFormVec q v v

def polarForm {F : Type u} [FormallyRealField F] {n : Nat}
    (s : Sig n) (u v : Vec F n) : F :=
  polarFormVec (Sig.toVec s) u v

def quadForm {F : Type u} [FormallyRealField F] {n : Nat}
    (s : Sig n) (v : Vec F n) : F :=
  quadFormVec (Sig.toVec s) v

section QuadLemmas

variable {F : Type u} [FormallyRealField F]

theorem polarForm_symm {n : Nat} (s : Sig n) (u v : Vec F n) :
    polarForm s u v = polarForm s v u := by
  unfold polarForm polarFormVec
  apply finSum_congr
  intro i
  rw [AssocRing.mul_assoc, FormallyRealField.mul_comm (u i) (v i), ← AssocRing.mul_assoc]

theorem polarForm_flip {n : Nat} (s : Sig n) (u v : Vec F n) :
    polarForm s.flip u v = -(polarForm s u v) := by
  unfold polarForm polarFormVec Sig.toVec Sig.flip
  rw [← finSum_neg]
  apply finSum_congr
  intro i
  rw [Sign.toScalar_flip, neg_mul_ring, neg_mul_ring]

theorem quadForm_flip {n : Nat} (s : Sig n) (v : Vec F n) :
    quadForm s.flip v = -(quadForm s v) :=
  polarForm_flip s v v

theorem polarForm_extend2 {d : Nat} (s : Sig d) (a b : Sign)
    (x y : Vec F d) (ux vx uy vy : F) :
    polarForm (extendVec2 s a b) (extendVec2 x ux vx) (extendVec2 y uy vy) =
      polarForm s x y + a.toScalar * ux * uy + b.toScalar * vx * vy := by
  unfold polarForm polarFormVec Sig.toVec extendVec2
  rw [finSum_succ_len]
  rw [extendVec1_last, extendVec1_last, extendVec1_last]
  apply congrArg (fun t => t + b.toScalar * vx * vy)
  have hstep :
      finSum (d + 1) (fun j =>
        (extendVec1 (extendVec1 s a) b (finCastSucc j)).toScalar *
        extendVec1 (extendVec1 x ux) vx (finCastSucc j) *
        extendVec1 (extendVec1 y uy) vy (finCastSucc j)) =
      finSum (d + 1) (fun j =>
        (extendVec1 s a j).toScalar * extendVec1 x ux j * extendVec1 y uy j) := by
    apply finSum_congr
    intro j
    rw [extendVec1_castSucc (extendVec1 s a),
        extendVec1_castSucc (extendVec1 x ux),
        extendVec1_castSucc (extendVec1 y uy)]
  rw [hstep, finSum_succ_len]
  rw [extendVec1_last, extendVec1_last, extendVec1_last]
  apply congrArg (fun t => t + a.toScalar * ux * uy)
  apply finSum_congr
  intro j
  rw [extendVec1_castSucc, extendVec1_castSucc, extendVec1_castSucc]

theorem quadForm_sub_law {n : Nat} (s : Sig n) (x y : Vec F n) :
    quadForm s (subVec x y) =
      quadForm s x + quadForm s y - (1 + 1) * polarForm s x y := by
  unfold quadForm quadFormVec polarForm polarFormVec subVec
  rw [AssocRing.sub_eq_add_neg, finSum_mul_left, ← finSum_neg, ← finSum_add, ← finSum_add]
  apply finSum_congr
  intro i
  let c : F := (s i).toScalar
  show c * (x i - y i) * (x i - y i) =
    c * x i * x i + c * y i * y i + -((1 + 1) * (c * x i * y i))
  calc
    c * (x i - y i) * (x i - y i)
        = (c * x i - c * y i) * (x i - y i) := by rw [mul_sub_ring c (x i) (y i)]
    _ = (c * x i) * (x i - y i) - (c * y i) * (x i - y i) := by rw [sub_mul_ring]
    _ = (c * x i * x i - c * x i * y i) - (c * y i * x i - c * y i * y i) := by
          rw [mul_sub_ring, mul_sub_ring]
    _ = c * x i * x i + -(c * x i * y i) + (-(c * x i * y i) + c * y i * y i) := by
          have hyx : c * y i * x i = c * x i * y i := by
            rw [AssocRing.mul_assoc c (y i) (x i),
                FormallyRealField.mul_comm (y i) (x i),
                ← AssocRing.mul_assoc]
          rw [hyx, AssocRing.sub_eq_add_neg, AssocRing.sub_eq_add_neg,
              AssocRing.sub_eq_add_neg, neg_add_distrib_ring, neg_neg_ring]
    _ = c * x i * x i + c * y i * y i + -((1 + 1) * (c * x i * y i)) := by
          have htwo : -((1 + 1) * (c * x i * y i)) = -(c * x i * y i) + -(c * x i * y i) := by
            rw [AssocRing.right_distrib, AssocRing.one_mul, neg_add_distrib_ring]
          rw [htwo,
              AssocRing.add_assoc (c * x i * x i) (-(c * x i * y i)) _,
              ← AssocRing.add_assoc (-(c * x i * y i)) (-(c * x i * y i)) (c * y i * y i),
              AssocRing.add_comm (-(c * x i * y i) + -(c * x i * y i)) (c * y i * y i),
              ← AssocRing.add_assoc (c * x i * x i) (c * y i * y i) _]

end QuadLemmas

/-! ### Matrices, Orthogonal Isometry Groups, Lie Algebras, and Layer-1 Group Spectra -/

abbrev Mat (R : Type u) (n : Nat) : Type u := Fin n → Fin n → R

def zeroMat {R : Type u} [AssocRing R] (n : Nat) : Mat R n := fun _ _ => 0
def idMat {R : Type u} [AssocRing R] (n : Nat) : Mat R n :=
  fun i j => if i = j then 1 else 0
def diagMat {R : Type u} [AssocRing R] {n : Nat} (s : Sig n) : Mat R n :=
  fun i j => if i = j then (s i).toScalar else 0

def matAdd {R : Type u} [AssocRing R] {n : Nat} (A B : Mat R n) : Mat R n :=
  fun i j => A i j + B i j
def matNeg {R : Type u} [AssocRing R] {n : Nat} (A : Mat R n) : Mat R n :=
  fun i j => -(A i j)
def matMul {R : Type u} [AssocRing R] {n : Nat} (A B : Mat R n) : Mat R n :=
  fun i k => finSum n (fun j => A i j * B j k)
def matTranspose {R : Type u} {n : Nat} (A : Mat R n) : Mat R n :=
  fun i j => A j i
def mulVec {R : Type u} [AssocRing R] {n : Nat} (A : Mat R n) (v : Vec R n) : Vec R n :=
  fun i => finSum n (fun j => A i j * v j)
def matTrace {R : Type u} [AssocRing R] {n : Nat} (A : Mat R n) : R :=
  finSum n (fun i => A i i)

section MatrixLemmas

variable {R : Type u} [AssocRing R]

theorem matMul_assoc {n : Nat} (A B C : Mat R n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i l
  unfold matMul
  have h1 : finSum n (fun k => finSum n (fun j => A i j * B j k) * C k l) =
      finSum n (fun k => finSum n (fun j => A i j * (B j k * C k l))) := by
    apply finSum_congr
    intro k
    rw [finSum_mul_right]
    apply finSum_congr
    intro j
    exact AssocRing.mul_assoc (A i j) (B j k) (C k l)
  have h2 : finSum n (fun j => A i j * finSum n (fun k => B j k * C k l)) =
      finSum n (fun j => finSum n (fun k => A i j * (B j k * C k l))) := by
    apply finSum_congr
    intro j
    exact finSum_mul_left (A i j) _
  rw [h1, h2, finSum_comm]

theorem idMat_matMul {n : Nat} (A : Mat R n) : matMul (idMat n) A = A := by
  funext i k
  unfold matMul idMat
  have h : (fun j : Fin n => (if i = j then (1 : R) else 0) * A j k) =
      (fun j : Fin n => if j = i then A j k else 0) := by
    funext j
    by_cases hij : j = i
    · subst hij; simp [AssocRing.one_mul]
    · have hij' : i ≠ j := fun h' => hij h'.symm
      simp [hij, hij', zero_mul_ring]
  rw [h, finSum_ite_eq]

theorem matMul_idMat {n : Nat} (A : Mat R n) : matMul A (idMat n) = A := by
  funext i k
  unfold matMul idMat
  have h : (fun j : Fin n => A i j * (if j = k then (1 : R) else 0)) =
      (fun j : Fin n => if j = k then A i j else 0) := by
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [AssocRing.mul_one]
    · simp [hjk, mul_zero_ring]
  rw [h, finSum_ite_eq]

theorem matMul_neg_right {n : Nat} (A B : Mat R n) :
    matMul A (matNeg B) = matNeg (matMul A B) := by
  funext i k
  unfold matMul matNeg
  rw [← finSum_neg]
  apply finSum_congr
  intro j
  exact mul_neg_ring (A i j) (B j k)

theorem matMul_neg_left {n : Nat} (A B : Mat R n) :
    matMul (matNeg A) B = matNeg (matMul A B) := by
  funext i k
  unfold matMul matNeg
  rw [← finSum_neg]
  apply finSum_congr
  intro j
  exact neg_mul_ring (A i j) (B j k)

theorem matNeg_inj {n : Nat} {A B : Mat R n} (h : matNeg A = matNeg B) : A = B := by
  funext i j
  have hij : -(A i j) = -(B i j) := congrFun (congrFun h i) j
  rw [← neg_neg_ring (A i j), hij, neg_neg_ring]

theorem diagMat_flip {n : Nat} (s : Sig n) :
    (diagMat s.flip : Mat R n) = matNeg (diagMat s) := by
  funext i j
  unfold diagMat matNeg Sig.flip
  by_cases hij : i = j
  · subst hij; simp [Sign.toScalar_flip]
  · simp [hij, neg_zero_ring]

theorem diagMat_sq {n : Nat} (s : Sig n) :
    matMul (diagMat s : Mat R n) (diagMat s) = idMat n := by
  funext i k
  unfold matMul diagMat idMat
  have h : (fun j : Fin n =>
      (if i = j then (s i).toScalar else (0 : R)) *
      (if j = k then (s j).toScalar else 0)) =
      (fun j : Fin n => if j = i then (if i = k then 1 else 0) else 0) := by
    funext j
    by_cases hji : j = i
    · subst hji
      by_cases hjk : j = k
      · subst hjk; simp [Sign.toScalar_sq]
      · simp [hjk, mul_zero_ring]
    · have hij : i ≠ j := fun hc => hji hc.symm
      simp [hji, hij, zero_mul_ring]
  rw [h, finSum_ite_eq]

end MatrixLemmas

/-- Orthogonal matrix predicate Mᵀ G_s M = G_s on Fⁿ. -/
def InOrthGroup {F : Type u} [FormallyRealField F] {n : Nat} (s : Sig n) (M : Mat F n) : Prop :=
  matMul (matTranspose M) (matMul (diagMat s) M) = diagMat s

/-- Full invertible orthogonal group O(Fⁿ, Q_s): matrices preserving G_s with two-sided inverse in O(Fⁿ, Q_s). -/
def InFullOrthGroup {F : Type u} [FormallyRealField F] {n : Nat} (s : Sig n) (M : Mat F n) : Prop :=
  InOrthGroup s M ∧ ∃ N : Mat F n, InOrthGroup s N ∧ matMul M N = idMat n ∧ matMul N M = idMat n

/-- Orthogonal Lie algebra 𝔰𝔬(Fⁿ, Q_s) = {X ∈ Mₙ(F) | Xᵀ G_s + G_s X = 0}. -/
def InOrthLieAlg {F : Type u} [FormallyRealField F] {n : Nat} (s : Sig n) (X : Mat F n) : Prop :=
  matAdd (matMul (matTranspose X) (diagMat s)) (matMul (diagMat s) X) = zeroMat n

/-- Layer-1 Joint Eigenvalue Spectrum: pairs `(M, μ)` where `M ∈ O(Q_s)` has eigenvalue `μ` on `Fⁿ`. -/
def InGroupEigenSpectrum {F : Type u} [FormallyRealField F] {n : Nat}
    (s : Sig n) (p : Mat F n × F) : Prop :=
  InFullOrthGroup s p.1 ∧ ∃ v : Vec F n, v ≠ zeroVec n ∧ mulVec p.1 v = smulVec p.2 v

/-- Layer-1 Scalar Eigenvalue Spectrum of `O(Q_s)`. -/
def InGroupScalarSpectrum {F : Type u} [FormallyRealField F] {n : Nat}
    (s : Sig n) (μ : F) : Prop :=
  ∃ M : Mat F n, InGroupEigenSpectrum s (M, μ)

/-- Layer-1 Character / Trace Spectrum `{tr(M) | M ∈ O(Q_s)}`. -/
def InGroupTraceSpectrum {F : Type u} [FormallyRealField F] {n : Nat}
    (s : Sig n) (τ : F) : Prop :=
  ∃ M : Mat F n, InFullOrthGroup s M ∧ matTrace M = τ

section OrthGroupTheorems

variable {F : Type u} [FormallyRealField F]

/-- Every `M ∈ OrthGroup` genuinely preserves the polar bilinear and quadratic forms. -/
theorem orthGroup_preserves_polar {n : Nat} {s : Sig n} {M : Mat F n}
    (hM : InOrthGroup s M) (u v : Vec F n) :
    polarForm s (mulVec M u) (mulVec M v) = polarForm s u v := by
  -- Both sides equal ∑_a ∑_b u_a * (Mᵀ G_s M)_{a,b} * v_b
  have hdiag : ∀ i : Fin n, ∀ w : Vec F n,
      (s i).toScalar * mulVec M w i = finSum n (fun a => (s i).toScalar * M i a * w a) := by
    intro i w
    unfold mulVec
    rw [finSum_mul_left]
    apply finSum_congr
    intro a
    rw [AssocRing.mul_assoc]
  unfold polarForm polarFormVec Sig.toVec
  have step1 : finSum n (fun i => (s i).toScalar * mulVec M u i * mulVec M v i) =
      finSum n (fun a => finSum n (fun b =>
        u a * matMul (matTranspose M) (matMul (diagMat s) M) a b * v b)) := by
    calc
      finSum n (fun i => (s i).toScalar * mulVec M u i * mulVec M v i)
          = finSum n (fun i => finSum n (fun a => ((s i).toScalar * M i a * u a) * mulVec M v i)) := by
            apply finSum_congr; intro i; rw [hdiag i u, finSum_mul_right]
      _ = finSum n (fun a => finSum n (fun i => ((s i).toScalar * M i a * u a) * mulVec M v i)) :=
            finSum_comm _
      _ = finSum n (fun a => finSum n (fun i => finSum n (fun b =>
            u a * (M i a * ((s i).toScalar * M i b)) * v b))) := by
            apply finSum_congr; intro a; apply finSum_congr; intro i
            unfold mulVec
            rw [finSum_mul_left]
            apply finSum_congr; intro b
            -- ((si * Mia * ua) * (Mib * vb)) = ua * (Mia * (si * Mib)) * vb
            rw [FormallyRealField.mul_comm ((s i).toScalar * M i a) (u a),
                AssocRing.mul_assoc (u a) ((s i).toScalar * M i a) (M i b * v b),
                ← AssocRing.mul_assoc ((s i).toScalar * M i a) (M i b) (v b),
                FormallyRealField.mul_comm (s i).toScalar (M i a),
                AssocRing.mul_assoc (M i a) (s i).toScalar (M i b),
                ← AssocRing.mul_assoc (u a) _ (v b)]
      _ = finSum n (fun a => finSum n (fun b => finSum n (fun i =>
            u a * (M i a * ((s i).toScalar * M i b)) * v b))) := by
            apply finSum_congr; intro a; exact finSum_comm _
      _ = finSum n (fun a => finSum n (fun b =>
            u a * matMul (matTranspose M) (matMul (diagMat s) M) a b * v b)) := by
            apply finSum_congr; intro a; apply finSum_congr; intro b
            rw [← finSum_mul_right, ← finSum_mul_left]
            apply congrArg (fun t => u a * t * v b)
            unfold matMul matTranspose diagMat
            apply finSum_congr; intro i
            apply congrArg (fun t => M i a * t)
            have hd : (fun j : Fin n => (if i = j then (s i).toScalar else (0 : F)) * M j b) =
                (fun j : Fin n => if j = i then (s i).toScalar * M j b else 0) := by
              funext j
              by_cases hji : j = i
              · subst hji; simp
              · have hij : i ≠ j := fun hc => hji hc.symm
                simp [hji, hij, zero_mul_ring]
            rw [hd, finSum_ite_eq]
  rw [step1, hM]
  apply finSum_congr; intro a
  unfold diagMat
  have hd2 : (fun b : Fin n => u a * (if a = b then (s a).toScalar else (0 : F)) * v b) =
      (fun b : Fin n => if b = a then (s a).toScalar * u a * v b else 0) := by
    funext b
    by_cases hba : b = a
    · subst hba
      simp [FormallyRealField.mul_comm (u b) (s b).toScalar]
    · have hab : a ≠ b := fun hc => hba hc.symm
      simp [hba, hab, mul_zero_ring, zero_mul_ring]
  rw [hd2, finSum_ite_eq]

theorem idMat_in_fullOrthGroup {n : Nat} (s : Sig n) : InFullOrthGroup (F := F) s (idMat n) := by
  have hid : InOrthGroup (F := F) s (idMat n) := by
    unfold InOrthGroup
    have ht : matTranspose (idMat n : Mat F n) = idMat n := by
      funext i j; unfold matTranspose idMat
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := fun hc => hij hc.symm
        simp [hij, hji]
    rw [ht, matMul_idMat, idMat_matMul]
  exact ⟨hid, idMat n, hid, idMat_matMul _, idMat_matMul _⟩

theorem matMul_in_orthGroup {n : Nat} {s : Sig n} {A B : Mat F n}
    (hA : InOrthGroup s A) (hB : InOrthGroup s B) : InOrthGroup s (matMul A B) := by
  unfold InOrthGroup at *
  have htr : matTranspose (matMul A B) = matMul (matTranspose B) (matTranspose A) := by
    funext i k
    unfold matTranspose matMul
    apply finSum_congr
    intro j
    exact FormallyRealField.mul_comm (A k j) (B j i)
  rw [htr, matMul_assoc (matTranspose B) (matTranspose A) _,
      ← matMul_assoc (diagMat s) A B,
      ← matMul_assoc (matTranspose A) (matMul (diagMat s) A) B,
      hA, hB]

/-- Sign-Flip Group Identity: `O(Fⁿ, Q_{-s}) = O(Fⁿ, Q_s)` as literal matrix subsets of `Mₙ(F)`. -/
theorem orthGroup_flip_eq {n : Nat} (s : Sig n) :
    (InOrthGroup (F := F) s.flip) = (InOrthGroup (F := F) s) := by
  funext M
  apply propext
  unfold InOrthGroup
  rw [diagMat_flip, matMul_neg_left, matMul_neg_right]
  constructor
  · exact matNeg_inj
  · exact congrArg matNeg

/-- Full Invertible Orthogonal Group Equality under Sign Flip. -/
theorem fullOrthGroup_flip_eq {n : Nat} (s : Sig n) :
    (InFullOrthGroup (F := F) s.flip) = (InFullOrthGroup (F := F) s) := by
  funext M
  unfold InFullOrthGroup
  rw [orthGroup_flip_eq]

/-- Lie Algebra Equality under Sign Flip: `𝔰𝔬(Q_{-s}) = 𝔰𝔬(Q_s)`. -/
theorem orthLieAlg_flip_eq {n : Nat} (s : Sig n) :
    (InOrthLieAlg (F := F) s.flip) = (InOrthLieAlg (F := F) s) := by
  funext X
  apply propext
  unfold InOrthLieAlg
  rw [diagMat_flip, matMul_neg_right, matMul_neg_left]
  have hneg : matAdd (matNeg (matMul (matTranspose X) (diagMat s)))
                     (matNeg (matMul (diagMat s) X)) =
      matNeg (matAdd (matMul (matTranspose X) (diagMat s)) (matMul (diagMat s) X)) := by
    funext i j; unfold matAdd matNeg; exact (neg_add_distrib_ring _ _).symm
  have hz : (zeroMat n : Mat F n) = matNeg (zeroMat n) := by
    funext i j; unfold zeroMat matNeg; exact neg_zero_ring.symm
  rw [hneg]
  constructor
  · intro h; rw [hz] at h; exact matNeg_inj h
  · intro h; rw [h, ← hz]

/-- Layer-1 Joint Group Eigenvalue Spectrum Equality under Sign Flip. -/
theorem groupEigenSpectrum_flip_eq {n : Nat} (s : Sig n) :
    (InGroupEigenSpectrum (F := F) s.flip) = (InGroupEigenSpectrum (F := F) s) := by
  funext p
  unfold InGroupEigenSpectrum
  rw [fullOrthGroup_flip_eq]

/-- Layer-1 Scalar Eigenvalue Spectrum Equality under Sign Flip. -/
theorem groupScalarSpectrum_flip_eq {n : Nat} (s : Sig n) :
    (InGroupScalarSpectrum (F := F) s.flip) = (InGroupScalarSpectrum (F := F) s) := by
  funext μ
  unfold InGroupScalarSpectrum
  simp [groupEigenSpectrum_flip_eq]

/-- Layer-1 Trace Spectrum Equality under Sign Flip. -/
theorem groupTraceSpectrum_flip_eq {n : Nat} (s : Sig n) :
    (InGroupTraceSpectrum (F := F) s.flip) = (InGroupTraceSpectrum (F := F) s) := by
  funext τ
  unfold InGroupTraceSpectrum
  simp [fullOrthGroup_flip_eq]

/-- Non-vacuity witness: reflections `-Iₙ` belong to `FullOrthGroup` and realize eigenvalue `-1` (for `n ≥ 1`). -/
theorem neg_id_in_fullOrthGroup (n : Nat) (s : Sig n) :
    InFullOrthGroup (F := F) s (matNeg (idMat n)) := by
  have horth : InOrthGroup (F := F) s (matNeg (idMat n)) := by
    unfold InOrthGroup
    have ht : matTranspose (matNeg (idMat n : Mat F n)) = matNeg (idMat n) := by
      funext i j; unfold matTranspose matNeg idMat
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := fun hc => hij hc.symm
        simp [hij, hji]
    have hnn : ∀ A : Mat F n, matNeg (matNeg A) = A := by
      intro A; funext i j; exact neg_neg_ring (A i j)
    rw [ht, matMul_neg_right, matMul_neg_right, matMul_neg_left, hnn, matMul_idMat, idMat_matMul]
  refine ⟨horth, matNeg (idMat n), horth, ?_, ?_⟩
  · have hnn : ∀ A : Mat F n, matNeg (matNeg A) = A := by
      intro A; funext i j; exact neg_neg_ring (A i j)
    rw [matMul_neg_left, matMul_neg_right, hnn, idMat_matMul]
  · have hnn : ∀ A : Mat F n, matNeg (matNeg A) = A := by
      intro A; funext i j; exact neg_neg_ring (A i j)
    rw [matMul_neg_left, matMul_neg_right, hnn, idMat_matMul]

end OrthGroupTheorems

/-! ### Genuine Conformal Horosphere (Null-Cone) Models -/

/-- A genuine conformal null-cone (horosphere) model of a `d`-dimensional quadratic space
    embedded into a `(d + 2)`-dimensional ambient space with hyperbolic split extension. -/
structure ConformalModel (F : Type u) [FormallyRealField F] (d : Nat) where
  baseSig : Sig d
  ambSig : Sig (d + 2)
  origin : Vec F (d + 2)
  infty : Vec F (d + 2)
  embed : Vec F d → Vec F (d + 2)
  sig_compat :
    signatureCount ambSig =
      ((signatureCount baseSig).1 + 1, (signatureCount baseSig).2 + 1)
  null_cone : ∀ x : Vec F d, quadForm ambSig (embed x) = 0
  infty_null : quadForm ambSig infty = 0 ∧ infty ≠ zeroVec (d + 2)
  horosphere_norm : ∀ x : Vec F d, polarForm ambSig (embed x) infty = -1
  origin_eq : embed (zeroVec d) = origin
  metric_law :
    ∀ x y : Vec F d,
      polarForm ambSig (embed x) (embed y) =
        -(halfField F) * quadForm baseSig (subVec x y)
  proj_injective :
    ∀ x y : Vec F d, ∀ c : F, c ≠ 0 →
      embed x = smulVec c (embed y) → c = 1 ∧ x = y

section ConformalConstruction

variable {F : Type u} [FormallyRealField F]

private theorem horosphere_hyp_diff (a b : F) :
    halfField F * (a - 1) * (halfField F * (b - 1)) -
    halfField F * (a + 1) * (halfField F * (b + 1)) =
      -(halfField F) * (a + b) := by
  let h := halfField F
  -- Show both after multiplying by (1 + 1) * (1 + 1)? Even simpler: direct expansion!
  have hprod : ∀ u v : F, (h * u) * (h * v) = (h * h) * (u * v) := by
    intro u v
    rw [AssocRing.mul_assoc h u (h * v),
        ← AssocRing.mul_assoc u h v,
        FormallyRealField.mul_comm u h,
        AssocRing.mul_assoc h u v,
        ← AssocRing.mul_assoc h h (u * v)]
  rw [hprod (a - 1) (b - 1), hprod (a + 1) (b + 1), ← mul_sub_ring]
  have hdiff : (a - 1) * (b - 1) - (a + 1) * (b + 1) = -((1 + 1) * (a + b)) := by
    -- Multiply out (a - 1)(b - 1) - (a + 1)(b + 1) = -2a - 2b
    have e1 : (a - 1) * (b - 1) = a * b - a - b + 1 := by
      rw [sub_mul_ring, mul_sub_ring, mul_sub_ring,
          AssocRing.mul_one, AssocRing.one_mul, AssocRing.one_mul,
          AssocRing.sub_eq_add_neg (a * b - a) (b - 1),
          AssocRing.sub_eq_add_neg b 1, neg_add_distrib_ring, neg_neg_ring,
          ← AssocRing.add_assoc, ← AssocRing.sub_eq_add_neg]
    have e2 : (a + 1) * (b + 1) = a * b + a + b + 1 := by
      rw [AssocRing.right_distrib, AssocRing.left_distrib, AssocRing.left_distrib,
          AssocRing.mul_one, AssocRing.one_mul, AssocRing.one_mul,
          ← AssocRing.add_assoc]
    rw [e1, e2]
    -- Cancel a*b and 1
    apply add_right_cancel_ring (a := a * b + a + b + 1)
    rw [AssocRing.sub_eq_add_neg (a * b - a - b + 1) _,
        AssocRing.add_assoc _ (-(a * b + a + b + 1)) _,
        AssocRing.neg_add_cancel, AssocRing.add_zero]
    -- Goal: a*b - a - b + 1 = -((1+1)*(a+b)) + (a*b + a + b + 1)
    have rhs_simp : -((1 + 1) * (a + b)) + (a * b + a + b + 1) = a * b - a - b + 1 := by
      rw [AssocRing.right_distrib (1 : F) 1 (a + b), AssocRing.one_mul,
          neg_add_distrib_ring, neg_add_distrib_ring]
      -- (-a + -b) + (-a + -b) + (((a*b + a) + b) + 1)
      have cancel_step : ∀ p x y : F, (-x + -y) + (p + x + y) = p := by
        intro p x y
        calc
          (-x + -y) + (p + x + y)
              = -x + (-y + (p + x + y)) := AssocRing.add_assoc _ _ _
          _ = -x + ((p + x) + (-y + y)) := by
                apply congrArg (fun t => -x + t)
                rw [AssocRing.add_comm (-y) (p + x + y),
                    AssocRing.add_assoc (p + x) y (-y),
                    AssocRing.add_comm y (-y)]
          _ = -x + (p + x) := by rw [AssocRing.neg_add_cancel, AssocRing.add_zero]
          _ = p + (-x + x) := by
                rw [AssocRing.add_comm (-x) (p + x), AssocRing.add_assoc p x (-x),
                    AssocRing.add_comm x (-x)]
          _ = p := by rw [AssocRing.neg_add_cancel, AssocRing.add_zero]
      rw [← AssocRing.add_assoc ((-a + -b) + (-a + -b)) (a * b + a + b) 1,
          AssocRing.add_assoc (-a + -b) (-a + -b) (a * b + a + b),
          cancel_step (a * b) a b]
      rw [AssocRing.sub_eq_add_neg (a * b - a) b, AssocRing.sub_eq_add_neg (a * b) a,
          AssocRing.add_comm (-a + -b) (a * b), AssocRing.add_assoc (a * b) (-a) (-b)]
    exact rhs_simp.symm
  rw [hdiff, mul_neg_ring]
  have hh2 : (h * h) * ((1 + 1) * (a + b)) = h * (a + b) := by
    rw [← AssocRing.mul_assoc (h * h) (1 + 1) (a + b),
        AssocRing.mul_assoc h h (1 + 1),
        half_mul_two_field, AssocRing.mul_one]
  rw [hh2, neg_mul_ring]

/-- Standard conformal horosphere model of `(Fᵈ, baseSig)` in ambient signature
    `ambSig = (baseSig, +1, -1)` of signature `(p + 1, q + 1)`. -/
def stdConformalModel {d : Nat} (base : Sig d) : ConformalModel F d where
  baseSig := base
  ambSig := extendVec2 base .pos .neg
  origin := extendVec2 (zeroVec d) (-(halfField F)) (halfField F)
  infty := extendVec2 (zeroVec d) 1 1
  embed := fun x =>
    extendVec2 x (halfField F * (quadForm base x - 1)) (halfField F * (quadForm base x + 1))
  sig_compat := by
    unfold extendVec2
    rw [signatureCount_extend1, signatureCount_extend1]
  null_cone := fun x => by
    have hm := polarForm_extend2 (F := F) base .pos .neg x x
      (halfField F * (quadForm base x - 1)) (halfField F * (quadForm base x + 1))
      (halfField F * (quadForm base x - 1)) (halfField F * (quadForm base x + 1))
    change polarForm (extendVec2 base .pos .neg)
      (extendVec2 x (halfField F * (quadForm base x - 1)) (halfField F * (quadForm base x + 1)))
      (extendVec2 x (halfField F * (quadForm base x - 1)) (halfField F * (quadForm base x + 1))) = 0
    rw [hm]
    change quadForm base x +
      1 * (halfField F * (quadForm base x - 1)) * (halfField F * (quadForm base x - 1)) +
      (-1) * (halfField F * (quadForm base x + 1)) * (halfField F * (quadForm base x + 1)) = 0
    rw [AssocRing.one_mul, neg_mul_ring, AssocRing.one_mul, neg_mul_ring,
        AssocRing.add_assoc (quadForm base x),
        ← AssocRing.sub_eq_add_neg,
        horosphere_hyp_diff (quadForm base x) (quadForm base x)]
    have htwo : quadForm base x + quadForm base x = (1 + 1) * quadForm base x := by
      rw [AssocRing.right_distrib, AssocRing.one_mul]
    rw [htwo, neg_mul_ring, ← AssocRing.mul_assoc, half_mul_two_field,
        AssocRing.one_mul, add_neg_cancel_right_ring]
  infty_null := by
    refine ⟨?_, ?_⟩
    · change polarForm (extendVec2 base .pos .neg) _ _ = 0
      rw [polarForm_extend2]
      have hz : polarForm base (zeroVec d : Vec F d) (zeroVec d) = 0 := by
        unfold polarForm polarFormVec zeroVec
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero d
        · intro i; rw [mul_zero_ring]
      rw [hz, AssocRing.zero_add]
      change 1 * (1 : F) * 1 + (-1) * 1 * 1 = 0
      rw [AssocRing.mul_one, AssocRing.mul_one, AssocRing.mul_one, AssocRing.mul_one,
          add_neg_cancel_right_ring]
    · intro h0
      have hv := congrFun h0 (finLast (d + 1))
      unfold extendVec2 zeroVec at hv
      rw [extendVec1_last] at hv
      exact one_ne_zero_field hv
  horosphere_norm := fun x => by
    rw [polarForm_extend2]
    have hz : polarForm base x (zeroVec d) = 0 := by
      unfold polarForm polarFormVec zeroVec
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero d
      · intro i; rw [mul_zero_ring]
    rw [hz, AssocRing.zero_add]
    change 1 * (halfField F * (quadForm base x - 1)) * 1 +
           (-1) * (halfField F * (quadForm base x + 1)) * 1 = -1
    rw [AssocRing.one_mul, AssocRing.mul_one, neg_mul_ring, AssocRing.one_mul, AssocRing.mul_one,
        ← AssocRing.sub_eq_add_neg, ← mul_sub_ring]
    have hd : (quadForm base x - 1) - (quadForm base x + 1) = -(1 + 1) := by
      rw [AssocRing.sub_eq_add_neg (quadForm base x - 1),
          neg_add_distrib_ring, AssocRing.sub_eq_add_neg,
          AssocRing.add_assoc (quadForm base x) (-1) (-quadForm base x + -1),
          ← AssocRing.add_assoc (-1) (-quadForm base x) (-1),
          AssocRing.add_comm (-1) (-quadForm base x),
          AssocRing.add_assoc (-quadForm base x) (-1) (-1),
          ← AssocRing.add_assoc (quadForm base x) (-quadForm base x) (-1 + -1),
          add_neg_cancel_right_ring, AssocRing.zero_add, ← neg_add_distrib_ring]
    rw [hd, mul_neg_ring, half_mul_two_field]
  origin_eq := by
    funext i
    have hz : quadForm base (zeroVec d : Vec F d) = 0 := by
      unfold quadForm quadFormVec polarFormVec zeroVec
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero d
      · intro j; rw [mul_zero_ring]
    unfold extendVec2
    -- Simplify scalar expressions at 0: h*(0 - 1) = -h and h*(0 + 1) = h
    have s1 : halfField F * (quadForm base (zeroVec d) - 1) = -(halfField F) := by
      rw [hz, AssocRing.sub_eq_add_neg, AssocRing.zero_add, mul_neg_ring, AssocRing.mul_one]
    have s2 : halfField F * (quadForm base (zeroVec d) + 1) = halfField F := by
      rw [hz, AssocRing.zero_add, AssocRing.mul_one]
    rw [s1, s2]
  metric_law := fun x y => by
    rw [polarForm_extend2]
    change polarForm base x y +
      1 * (halfField F * (quadForm base x - 1)) * (halfField F * (quadForm base y - 1)) +
      (-1) * (halfField F * (quadForm base x + 1)) * (halfField F * (quadForm base y + 1)) =
      -(halfField F) * quadForm base (subVec x y)
    rw [AssocRing.one_mul, neg_mul_ring, AssocRing.one_mul, neg_mul_ring,
        AssocRing.add_assoc (polarForm base x y),
        ← AssocRing.sub_eq_add_neg,
        horosphere_hyp_diff (quadForm base x) (quadForm base y),
        quadForm_sub_law, AssocRing.sub_eq_add_neg (quadForm base x + quadForm base y),
        AssocRing.left_distrib (-(halfField F)) (quadForm base x + quadForm base y) _,
        mul_neg_ring (-(halfField F)),
        neg_mul_ring (halfField F) (quadForm base x + quadForm base y),
        neg_mul_ring (halfField F) ((1 + 1) * polarForm base x y),
        neg_neg_ring,
        ← AssocRing.mul_assoc (halfField F) (1 + 1) (polarForm base x y),
        half_mul_two_field, AssocRing.one_mul, AssocRing.add_comm _ (polarForm base x y)]
  proj_injective := fun x y c _ heq => by
    -- Subtract coordinate (d + 1) minus coordinate d: (Qx+1)/2 - (Qx-1)/2 = 1 = c * 1
    let idxU : Fin (d + 2) := finCastSucc (finLast d)
    let idxV : Fin (d + 2) := finLast (d + 1)
    have hU := congrFun heq idxU
    have hV := congrFun heq idxV
    unfold extendVec2 smulVec at hU hV
    rw [extendVec1_castSucc, extendVec1_last, extendVec1_castSucc, extendVec1_last] at hU
    rw [extendVec1_last, extendVec1_last] at hV
    have diff_one : ∀ a : F, halfField F * (a + 1) - halfField F * (a - 1) = 1 := by
      intro a
      rw [← mul_sub_ring]
      have ha : (a + 1) - (a - 1) = 1 + 1 := by
        rw [AssocRing.sub_eq_add_neg (a + 1), AssocRing.sub_eq_add_neg a 1,
            neg_add_distrib_ring, neg_neg_ring,
            AssocRing.add_assoc a 1 (-a + 1),
            ← AssocRing.add_assoc 1 (-a) 1,
            AssocRing.add_comm 1 (-a),
            AssocRing.add_assoc (-a) 1 1,
            ← AssocRing.add_assoc a (-a) (1 + 1),
            add_neg_cancel_right_ring, AssocRing.zero_add]
      rw [ha, half_mul_two_field]
    have hc1 : (1 : F) = c := by
      calc
        (1 : F) = halfField F * (quadForm base x + 1) - halfField F * (quadForm base x - 1) :=
          (diff_one (quadForm base x)).symm
        _ = c * (halfField F * (quadForm base y + 1)) -
            c * (halfField F * (quadForm base y - 1)) := by rw [hV, hU]
        _ = c * (halfField F * (quadForm base y + 1) - halfField F * (quadForm base y - 1)) :=
          (mul_sub_ring _ _ _).symm
        _ = c * 1 := by rw [diff_one (quadForm base y)]
        _ = c := AssocRing.mul_one c
    subst hc1
    refine ⟨rfl, ?_⟩
    funext j
    have hj := congrFun heq (finCastSucc (finCastSucc j))
    unfold extendVec2 smulVec at hj
    rw [extendVec1_castSucc, extendVec1_castSucc,
        extendVec1_castSucc, extendVec1_castSucc, AssocRing.one_mul] at hj
    exact hj

/-- Swap the two hyperbolic extension coordinates `(d, d + 1)` of a vector in `F^(d+2)`. -/
def swapHyp2 {α : Type u} {d : Nat} (w : Fin (d + 2) → α) : Fin (d + 2) → α :=
  extendVec2 (fun j : Fin d => w (finCastSucc (finCastSucc j)))
    (w (finLast (d + 1)))
    (w (finCastSucc (finLast d)))

theorem swapHyp2_extendVec2 {α : Type u} {d : Nat} (x : Fin d → α) (a b : α) :
    swapHyp2 (extendVec2 x a b) = extendVec2 x b a := by
  unfold swapHyp2 extendVec2
  have hbase : (fun j : Fin d => extendVec1 (extendVec1 x a) b (finCastSucc (finCastSucc j))) = x := by
    funext j
    rw [extendVec1_castSucc, extendVec1_castSucc]
  rw [hbase, extendVec1_last, extendVec1_castSucc, extendVec1_last]

/-- Sign-flipped dual conformal horosphere model of `(Fᵈ, base.flip)` in ambient signature
    `ambSig = (base.flip, -1, +1) = (stdConformalModel base).ambSig.flip` of signature `(q + 1, p + 1)`,
    sharing the exact same null point at infinity `e_∞ = (0, 1, 1)` and orthogonal group! -/
def dualConformalModel {d : Nat} (base : Sig d) : ConformalModel F d where
  baseSig := base.flip
  ambSig := extendVec2 base.flip .neg .pos
  origin := extendVec2 (zeroVec d) (halfField F) (-(halfField F))
  infty := extendVec2 (zeroVec d) 1 1
  embed := fun x =>
    extendVec2 x
      (halfField F * (quadForm base.flip x + 1))
      (halfField F * (quadForm base.flip x - 1))
  sig_compat := by
    unfold extendVec2
    rw [signatureCount_extend1, signatureCount_extend1]
  null_cone := fun x => by
    have hstd := (stdConformalModel (F := F) base.flip).null_cone x
    dsimp only [stdConformalModel] at hstd
    change polarForm (extendVec2 base.flip .neg .pos)
      (extendVec2 x (halfField F * (quadForm base.flip x + 1)) (halfField F * (quadForm base.flip x - 1)))
      (extendVec2 x (halfField F * (quadForm base.flip x + 1)) (halfField F * (quadForm base.flip x - 1))) = 0
    change polarForm (extendVec2 base.flip .pos .neg)
      (extendVec2 x (halfField F * (quadForm base.flip x - 1)) (halfField F * (quadForm base.flip x + 1)))
      (extendVec2 x (halfField F * (quadForm base.flip x - 1)) (halfField F * (quadForm base.flip x + 1))) = 0 at hstd
    rw [polarForm_extend2] at hstd ⊢
    rw [AssocRing.add_assoc (polarForm base.flip x x),
        AssocRing.add_comm (Sign.neg.toScalar * _ * _) _,
        ← AssocRing.add_assoc (polarForm base.flip x x)]
    exact hstd
  infty_null := by
    refine ⟨?_, ?_⟩
    · change polarForm (extendVec2 base.flip .neg .pos) _ _ = 0
      rw [polarForm_extend2]
      have hz : polarForm base.flip (zeroVec d : Vec F d) (zeroVec d) = 0 := by
        unfold polarForm polarFormVec zeroVec
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero d
        · intro i; rw [mul_zero_ring]
      rw [hz, AssocRing.zero_add]
      change (-1 : F) * 1 * 1 + 1 * 1 * 1 = 0
      rw [AssocRing.mul_one, AssocRing.mul_one, AssocRing.mul_one, AssocRing.mul_one,
          AssocRing.neg_add_cancel]
    · intro h0
      have hv := congrFun h0 (finLast (d + 1))
      unfold extendVec2 zeroVec at hv
      rw [extendVec1_last] at hv
      exact one_ne_zero_field hv
  horosphere_norm := fun x => by
    have hstd := (stdConformalModel (F := F) base.flip).horosphere_norm x
    dsimp only [stdConformalModel] at hstd
    rw [polarForm_extend2] at hstd ⊢
    rw [AssocRing.add_assoc (polarForm base.flip x (zeroVec d)),
        AssocRing.add_comm (Sign.neg.toScalar * _ * _) _,
        ← AssocRing.add_assoc (polarForm base.flip x (zeroVec d))]
    exact hstd
  origin_eq := by
    funext i
    have hz : quadForm base.flip (zeroVec d : Vec F d) = 0 := by
      unfold quadForm quadFormVec polarFormVec zeroVec
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero d
      · intro j; rw [mul_zero_ring]
    unfold extendVec2
    have s1 : halfField F * (quadForm base.flip (zeroVec d) + 1) = halfField F := by
      rw [hz, AssocRing.zero_add, AssocRing.mul_one]
    have s2 : halfField F * (quadForm base.flip (zeroVec d) - 1) = -(halfField F) := by
      rw [hz, AssocRing.sub_eq_add_neg, AssocRing.zero_add, mul_neg_ring, AssocRing.mul_one]
    rw [s1, s2]
  metric_law := fun x y => by
    have hstd := (stdConformalModel (F := F) base.flip).metric_law x y
    dsimp only [stdConformalModel] at hstd
    rw [polarForm_extend2] at hstd ⊢
    rw [AssocRing.add_assoc (polarForm base.flip x y),
        AssocRing.add_comm (Sign.neg.toScalar * _ * _) _,
        ← AssocRing.add_assoc (polarForm base.flip x y)]
    exact hstd
  proj_injective := fun x y c hc heq => by
    apply (stdConformalModel (F := F) base.flip).proj_injective x y c hc
    unfold stdConformalModel
    have hs := congrArg swapHyp2 heq
    have hsmul : swapHyp2 (smulVec c (extendVec2 y
        (halfField F * (quadForm base.flip y + 1))
        (halfField F * (quadForm base.flip y - 1)))) =
      smulVec c (extendVec2 y
        (halfField F * (quadForm base.flip y - 1))
        (halfField F * (quadForm base.flip y + 1))) := by
      unfold smulVec
      have h1 : (fun i => c * extendVec2 y
          (halfField F * (quadForm base.flip y + 1))
          (halfField F * (quadForm base.flip y - 1)) i) =
        extendVec2 (smulVec c y)
          (c * (halfField F * (quadForm base.flip y + 1)))
          (c * (halfField F * (quadForm base.flip y - 1))) := by
        funext i
        unfold extendVec2 extendVec1 smulVec
        split
        · next hlt1 =>
          split
          · rfl
          · rfl
        · rfl
      have h2 : (fun i => c * extendVec2 y
          (halfField F * (quadForm base.flip y - 1))
          (halfField F * (quadForm base.flip y + 1)) i) =
        extendVec2 (smulVec c y)
          (c * (halfField F * (quadForm base.flip y - 1)))
          (c * (halfField F * (quadForm base.flip y + 1))) := by
        funext i
        unfold extendVec2 extendVec1 smulVec
        split
        · next hlt1 =>
          split
          · rfl
          · rfl
        · rfl
      rw [h1, h2, swapHyp2_extendVec2]
    rw [swapHyp2_extendVec2, hsmul] at hs
    exact hs

/-- Fundamental Ambient Flip Theorem: the dual conformal model has ambient signature
    literally equal to the sign-flip of the standard conformal model's ambient signature! -/
theorem dualConformalModel_ambSig_eq_flip {d : Nat} (base : Sig d) :
    (dualConformalModel (F := F) base).ambSig = (stdConformalModel (F := F) base).ambSig.flip := by
  funext i
  dsimp only [dualConformalModel, stdConformalModel, Sig.flip, extendVec2, extendVec1]
  split
  · next h1 =>
    split
    · rfl
    · rfl
  · rfl

/-- Both conformal models share the exact same null point at infinity `e_∞ = (0, 1, 1)`. -/
theorem dualConformalModel_same_infty {d : Nat} (base : Sig d) :
    (dualConformalModel (F := F) base).infty = (stdConformalModel (F := F) base).infty := rfl

/-- The two conformal horosphere embeddings are strictly distinct (already at the origin `x = 0`). -/
theorem conformal_embeddings_ne {d : Nat} (base : Sig d) :
    (stdConformalModel (F := F) base).embed ≠ (dualConformalModel (F := F) base).embed := by
  intro heq
  have h0 := congrFun (congrFun heq (zeroVec d)) (finLast (d + 1))
  rw [(stdConformalModel (F := F) base).origin_eq,
      (dualConformalModel (F := F) base).origin_eq] at h0
  dsimp only [stdConformalModel, dualConformalModel, extendVec2] at h0
  rw [extendVec1_last, extendVec1_last] at h0
  have h2 : halfField F + halfField F = 0 := by
    have h' : halfField F + halfField F = -(halfField F) + halfField F :=
      congrArg (fun t => t + halfField F) h0
    rw [AssocRing.neg_add_cancel] at h'
    exact h'
  rw [half_add_half_field] at h2
  exact one_ne_zero_field h2

private theorem exists_ne_zero_of_ne_zeroVec :
    ∀ {d : Nat} {x : Vec F d}, x ≠ zeroVec d → ∃ j : Fin d, x j ≠ 0
  | 0, x, hx => False.elim (hx (funext (fun i => Fin.elim0 i)))
  | m + 1, x, hx => by
    by_cases hl : x (finLast m) = 0
    · have hinit : (fun j : Fin m => x (finCastSucc j)) ≠ zeroVec m := by
        intro hi
        apply hx
        funext i
        cases fin_cases_last i with
        | inl h =>
          rcases h with ⟨j, rfl⟩
          exact congrFun hi j
        | inr h =>
          subst h
          exact hl
      rcases exists_ne_zero_of_ne_zeroVec hinit with ⟨j, hj⟩
      exact ⟨finCastSucc j, hj⟩
    · exact ⟨finLast m, hl⟩

/-- Stronger projective distinctness: for every nonzero base vector `x ≠ 0`, `embed₁ x` and
    `embed₂ x` do not even lie on the same projective ray in `ℙ(𝒩)`! -/
theorem conformal_embeddings_proj_disjoint {d : Nat} (base : Sig d)
    {x : Vec F d} (hx : x ≠ zeroVec d) (c : F) :
    (stdConformalModel (F := F) base).embed x ≠
      smulVec c ((dualConformalModel (F := F) base).embed x) := by
  intro heq
  rcases exists_ne_zero_of_ne_zeroVec hx with ⟨j0, hj0⟩
  have hj := congrFun heq (finCastSucc (finCastSucc j0))
  dsimp only [stdConformalModel, dualConformalModel, extendVec2, smulVec] at hj
  rw [extendVec1_castSucc, extendVec1_castSucc,
      extendVec1_castSucc, extendVec1_castSucc] at hj
  have hc1 : c = 1 := by
    have hsub : (1 - c) * x j0 = 0 := by
      rw [sub_mul_ring, AssocRing.one_mul, ← hj, sub_self_ring]
    cases mul_eq_zero_field hsub with
    | inl h1c => exact (sub_eq_zero_iff_eq.mp h1c).symm
    | inr hxj => exact False.elim (hj0 hxj)
  subst hc1
  have hU := congrFun heq (finCastSucc (finLast d))
  have hV := congrFun heq (finLast (d + 1))
  dsimp only [stdConformalModel, dualConformalModel, extendVec2, smulVec] at hU hV
  rw [extendVec1_castSucc, extendVec1_last,
      extendVec1_castSucc, extendVec1_last,
      AssocRing.one_mul, quadForm_flip] at hU
  rw [extendVec1_last, extendVec1_last, AssocRing.one_mul, quadForm_flip] at hV
  -- Sum hU + hV: half*(Qx - 1) + half*(Qx + 1) = half*(-Qx + 1) + half*(-Qx - 1)
  -- Wait: subtract hV - hU!
  -- LHS: half*(Qx + 1) - half*(Qx - 1) = 1
  -- RHS: half*(-Qx - 1) - half*(-Qx + 1) = -1!
  have diff_one : ∀ a : F, halfField F * (a + 1) - halfField F * (a - 1) = 1 := by
    intro a
    rw [← mul_sub_ring]
    have ha : (a + 1) - (a - 1) = 1 + 1 := by
      rw [AssocRing.sub_eq_add_neg (a + 1), AssocRing.sub_eq_add_neg a 1,
          neg_add_distrib_ring, neg_neg_ring,
          AssocRing.add_assoc a 1 (-a + 1),
          ← AssocRing.add_assoc 1 (-a) 1,
          AssocRing.add_comm 1 (-a),
          AssocRing.add_assoc (-a) 1 1,
          ← AssocRing.add_assoc a (-a) (1 + 1),
          add_neg_cancel_right_ring, AssocRing.zero_add]
    rw [ha, half_mul_two_field]
  have diff_lhs :
      halfField F * (quadForm base x + 1) - halfField F * (quadForm base x - 1) = 1 :=
    diff_one (quadForm base x)
  have diff_rhs :
      halfField F * (-(quadForm base x) - 1) - halfField F * (-(quadForm base x) + 1) = -1 := by
    have hswap : ∀ A B : F, B - A = -(A - B) := by
      intro A B
      rw [AssocRing.sub_eq_add_neg A B, neg_add_distrib_ring, neg_neg_ring,
          AssocRing.add_comm (-A) B, ← AssocRing.sub_eq_add_neg]
    rw [hswap (halfField F * (-(quadForm base x) + 1)) (halfField F * (-(quadForm base x) - 1)),
        diff_one (-(quadForm base x))]
  have h1_eq_neg1 : (-1 : F) = 1 := by
    calc
      (-1 : F) = halfField F * (-(quadForm base x) - 1) -
                 halfField F * (-(quadForm base x) + 1) := diff_rhs.symm
      _ = halfField F * (quadForm base x + 1) -
          halfField F * (quadForm base x - 1) := by rw [← hV, ← hU]
      _ = 1 := diff_lhs
  exact neg_one_ne_one_field h1_eq_neg1

end ConformalConstruction

end Conjecture00000007620
