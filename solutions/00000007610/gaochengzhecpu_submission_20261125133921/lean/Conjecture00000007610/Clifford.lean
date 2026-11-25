/-
  Conjecture 00000007610 — Genuine 2^n-Dimensional Clifford Algebra Cl(K^n, d)
  Constructed from scratch via Z/2Z-graded Chevalley recursion over any field K,
  with full K-algebra axioms, exact K-dimension 2^n, fundamental Clifford relation
  iota(v)^2 = Q(v) • 1, and the Universal Property of Clifford Algebras.
-/

import Conjecture00000007610.Algebra

namespace Conjecture00000007610

universe u v

/-- Initial n coordinates of a tuple of length n + 1. -/
def finInit {α : Type u} {n : Nat} (f : Fin (n + 1) → α) : Fin n → α :=
  fun i => f ⟨i.val, by omega⟩

/-- Final coordinate (at index n) of a tuple of length n + 1. -/
def finLast {α : Type u} {n : Nat} (f : Fin (n + 1) → α) : α :=
  f ⟨n, by omega⟩

/-- Append one element at index n to a tuple of length n. -/
def finSnoc {α : Type u} {n : Nat} (f : Fin n → α) (x : α) : Fin (n + 1) → α :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else x

theorem finInit_snoc {α : Type u} {n : Nat} (f : Fin n → α) (x : α) :
    finInit (finSnoc f x) = f := by
  funext i
  unfold finInit finSnoc
  dsimp
  split
  · rfl
  · next h =>
    exfalso
    exact h i.isLt

theorem finLast_snoc {α : Type u} {n : Nat} (f : Fin n → α) (x : α) :
    finLast (finSnoc f x) = x := by
  unfold finLast finSnoc
  dsimp
  have h : ¬ (n < n) := by omega
  rw [dif_neg h]

theorem finSnoc_init_last {α : Type u} {n : Nat} (g : Fin (n + 1) → α) :
    finSnoc (finInit g) (finLast g) = g := by
  funext i
  unfold finSnoc finInit finLast
  split
  · rfl
  · next h =>
    have hi : i = ⟨n, by omega⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hi]

/-- Diagonal quadratic form Q_d(v) = ∑_{k=0}^{n-1} d_k * v_k^2. -/
def quadForm {K : Type u} [FieldStructure K] : {n : Nat} → (Fin n → K) → (Fin n → K) → K
  | 0, _, _ => 0
  | _ + 1, d, v => quadForm (finInit d) (finInit v) + finLast d * (finLast v * finLast v)

theorem quadForm_zero {K : Type u} [FieldStructure K] :
    ∀ {n : Nat} (d : Fin n → K), quadForm d (0 : Fin n → K) = 0
  | 0, _ => rfl
  | n + 1, d => by
    change quadForm (finInit d) (finInit (0 : Fin (n + 1) → K)) +
      finLast d * (finLast (0 : Fin (n + 1) → K) * finLast (0 : Fin (n + 1) → K)) = 0
    have hinit : finInit (0 : Fin (n + 1) → K) = (0 : Fin n → K) := rfl
    have hlast : finLast (0 : Fin (n + 1) → K) = (0 : K) := rfl
    rw [hinit, hlast, quadForm_zero (finInit d), zero_mul_ring, mul_zero_ring, add_zero_grp]

/-- Underlying 2^n-dimensional carrier of Cl(K^n, d). -/
@[reducible] def CliffordRaw (K : Type u) : Nat → Type u
  | 0 => K
  | n + 1 => CliffordRaw K n × CliffordRaw K n

section RawOps

variable {K : Type u} [FieldStructure K]

def clZero : (n : Nat) → CliffordRaw K n
  | 0 => 0
  | n + 1 => (clZero n, clZero n)

def clOne : (n : Nat) → CliffordRaw K n
  | 0 => 1
  | n + 1 => (clOne n, clZero n)

def clAdd : (n : Nat) → CliffordRaw K n → CliffordRaw K n → CliffordRaw K n
  | 0, x, y => x + y
  | n + 1, x, y => (clAdd n x.1 y.1, clAdd n x.2 y.2)

def clNeg : (n : Nat) → CliffordRaw K n → CliffordRaw K n
  | 0, x => -x
  | n + 1, x => (clNeg n x.1, clNeg n x.2)

def clSmul : (n : Nat) → K → CliffordRaw K n → CliffordRaw K n
  | 0, c, x => c * x
  | n + 1, c, x => (clSmul n c x.1, clSmul n c x.2)

/-- Grade involution α(a + b e_n) = α(a) - α(b) e_n. -/
def clInvolution : (n : Nat) → CliffordRaw K n → CliffordRaw K n
  | 0, x => x
  | n + 1, x => (clInvolution n x.1, clNeg n (clInvolution n x.2))

/-- Chevalley Z/2Z-graded Clifford multiplication:
    (a1 + b1 e_n)(a2 + b2 e_n) = (a1 a2 + d_n b1 α(b2)) + (a1 b2 + b1 α(a2)) e_n. -/
def clMul : (n : Nat) → (Fin n → K) → CliffordRaw K n → CliffordRaw K n → CliffordRaw K n
  | 0, _, x, y => x * y
  | n + 1, d, x, y =>
    let d' := finInit d
    let dn := finLast d
    (clAdd n (clMul n d' x.1 y.1) (clSmul n dn (clMul n d' x.2 (clInvolution n y.2))),
     clAdd n (clMul n d' x.1 y.2) (clMul n d' x.2 (clInvolution n y.1)))

theorem clAdd_assoc : ∀ (n : Nat) (x y z : CliffordRaw K n),
    clAdd n (clAdd n x y) z = clAdd n x (clAdd n y z)
  | 0, x, y, z => AddCommGrp.add_assoc x y z
  | n + 1, x, y, z => Prod.ext (clAdd_assoc n x.1 y.1 z.1) (clAdd_assoc n x.2 y.2 z.2)

theorem clAdd_comm : ∀ (n : Nat) (x y : CliffordRaw K n), clAdd n x y = clAdd n y x
  | 0, x, y => AddCommGrp.add_comm x y
  | n + 1, x, y => Prod.ext (clAdd_comm n x.1 y.1) (clAdd_comm n x.2 y.2)

theorem clZero_add : ∀ (n : Nat) (x : CliffordRaw K n), clAdd n (clZero n) x = x
  | 0, x => AddCommGrp.zero_add x
  | n + 1, x => Prod.ext (clZero_add n x.1) (clZero_add n x.2)

theorem clAdd_zero (n : Nat) (x : CliffordRaw K n) : clAdd n x (clZero n) = x := by
  rw [clAdd_comm, clZero_add]

theorem clNeg_add_cancel : ∀ (n : Nat) (x : CliffordRaw K n), clAdd n (clNeg n x) x = clZero n
  | 0, x => AddCommGrp.neg_add_cancel x
  | n + 1, x => Prod.ext (clNeg_add_cancel n x.1) (clNeg_add_cancel n x.2)

theorem clAdd_neg_cancel (n : Nat) (x : CliffordRaw K n) : clAdd n x (clNeg n x) = clZero n := by
  rw [clAdd_comm, clNeg_add_cancel]

theorem clNeg_zero : ∀ (n : Nat), clNeg n (clZero n : CliffordRaw K n) = clZero n
  | 0 => neg_zero_grp
  | n + 1 => Prod.ext (clNeg_zero n) (clNeg_zero n)

theorem clNeg_neg : ∀ (n : Nat) (x : CliffordRaw K n), clNeg n (clNeg n x) = x
  | 0, x => neg_neg_grp x
  | n + 1, x => Prod.ext (clNeg_neg n x.1) (clNeg_neg n x.2)

theorem clNeg_add : ∀ (n : Nat) (x y : CliffordRaw K n),
    clNeg n (clAdd n x y) = clAdd n (clNeg n x) (clNeg n y)
  | 0, x, y => neg_add_grp x y
  | n + 1, x, y => Prod.ext (clNeg_add n x.1 y.1) (clNeg_add n x.2 y.2)

theorem clOne_smul : ∀ (n : Nat) (x : CliffordRaw K n), clSmul n 1 x = x
  | 0, x => UnitalRing.one_mul x
  | n + 1, x => Prod.ext (clOne_smul n x.1) (clOne_smul n x.2)

theorem clMul_smul : ∀ (n : Nat) (a b : K) (x : CliffordRaw K n),
    clSmul n (a * b) x = clSmul n a (clSmul n b x)
  | 0, a, b, x => UnitalRing.mul_assoc a b x
  | n + 1, a, b, x => Prod.ext (clMul_smul n a b x.1) (clMul_smul n a b x.2)

theorem clSmul_zero : ∀ (n : Nat) (a : K), clSmul n a (clZero n) = clZero n
  | 0, a => mul_zero_ring a
  | n + 1, a => Prod.ext (clSmul_zero n a) (clSmul_zero n a)

theorem clSmul_add : ∀ (n : Nat) (a : K) (x y : CliffordRaw K n),
    clSmul n a (clAdd n x y) = clAdd n (clSmul n a x) (clSmul n a y)
  | 0, a, x, y => UnitalRing.left_distrib a x y
  | n + 1, a, x, y => Prod.ext (clSmul_add n a x.1 y.1) (clSmul_add n a x.2 y.2)

theorem clAdd_smul : ∀ (n : Nat) (a b : K) (x : CliffordRaw K n),
    clSmul n (a + b) x = clAdd n (clSmul n a x) (clSmul n b x)
  | 0, a, b, x => UnitalRing.right_distrib a b x
  | n + 1, a, b, x => Prod.ext (clAdd_smul n a b x.1) (clAdd_smul n a b x.2)

theorem clZero_smul : ∀ (n : Nat) (x : CliffordRaw K n), clSmul n 0 x = clZero n
  | 0, x => zero_mul_ring x
  | n + 1, x => Prod.ext (clZero_smul n x.1) (clZero_smul n x.2)

theorem clSmul_neg : ∀ (n : Nat) (a : K) (x : CliffordRaw K n),
    clSmul n a (clNeg n x) = clNeg n (clSmul n a x)
  | 0, a, x => mul_neg_ring a x
  | n + 1, a, x => Prod.ext (clSmul_neg n a x.1) (clSmul_neg n a x.2)

theorem clInvolution_zero : ∀ (n : Nat), clInvolution n (clZero n : CliffordRaw K n) = clZero n
  | 0 => rfl
  | n + 1 => Prod.ext (clInvolution_zero n)
      (by dsimp [clInvolution, clZero]; rw [clInvolution_zero n, clNeg_zero n])

theorem clInvolution_one : ∀ (n : Nat), clInvolution n (clOne n : CliffordRaw K n) = clOne n
  | 0 => rfl
  | n + 1 => Prod.ext (clInvolution_one n)
      (by dsimp [clInvolution, clOne]; rw [clInvolution_zero n, clNeg_zero n])

theorem clInvolution_add : ∀ (n : Nat) (x y : CliffordRaw K n),
    clInvolution n (clAdd n x y) = clAdd n (clInvolution n x) (clInvolution n y)
  | 0, _, _ => rfl
  | n + 1, x, y => Prod.ext (clInvolution_add n x.1 y.1)
      (by dsimp [clInvolution, clAdd]; rw [clInvolution_add n x.2 y.2, clNeg_add n])

theorem clInvolution_neg : ∀ (n : Nat) (x : CliffordRaw K n),
    clInvolution n (clNeg n x) = clNeg n (clInvolution n x)
  | 0, _ => rfl
  | n + 1, x => Prod.ext (clInvolution_neg n x.1)
      (by dsimp [clInvolution, clNeg]; rw [clInvolution_neg n x.2])

theorem clInvolution_smul : ∀ (n : Nat) (c : K) (x : CliffordRaw K n),
    clInvolution n (clSmul n c x) = clSmul n c (clInvolution n x)
  | 0, _, _ => rfl
  | n + 1, c, x => Prod.ext (clInvolution_smul n c x.1)
      (by dsimp [clInvolution, clSmul]; rw [clInvolution_smul n c x.2, clSmul_neg n])

theorem clInvolution_idem : ∀ (n : Nat) (x : CliffordRaw K n),
    clInvolution n (clInvolution n x) = x
  | 0, _ => rfl
  | n + 1, x => Prod.ext (clInvolution_idem n x.1)
      (by dsimp [clInvolution]; rw [clInvolution_neg n, clNeg_neg n, clInvolution_idem n])

theorem clMul_zero : ∀ (n : Nat) (d : Fin n → K) (x : CliffordRaw K n),
    clMul n d x (clZero n) = clZero n
  | 0, _, x => mul_zero_ring x
  | n + 1, d, x => by
    dsimp [clMul, clZero]
    rw [clInvolution_zero n, clMul_zero n, clMul_zero n, clSmul_zero n, clAdd_zero n]

theorem clZero_mul : ∀ (n : Nat) (d : Fin n → K) (x : CliffordRaw K n),
    clMul n d (clZero n) x = clZero n
  | 0, _, x => zero_mul_ring x
  | n + 1, d, x => by
    dsimp [clMul, clZero]
    rw [clZero_mul n, clZero_mul n, clZero_mul n, clZero_mul n, clSmul_zero n, clAdd_zero n]

theorem clOne_mul : ∀ (n : Nat) (d : Fin n → K) (x : CliffordRaw K n),
    clMul n d (clOne n) x = x
  | 0, _, x => UnitalRing.one_mul x
  | n + 1, d, x => by
    cases x with
    | mk a b =>
      dsimp [clMul, clOne]
      rw [clOne_mul n, clOne_mul n, clZero_mul n, clZero_mul n, clSmul_zero n,
          clAdd_zero n, clAdd_zero n]

theorem clMul_one : ∀ (n : Nat) (d : Fin n → K) (x : CliffordRaw K n),
    clMul n d x (clOne n) = x
  | 0, _, x => UnitalRing.mul_one x
  | n + 1, d, x => by
    cases x with
    | mk a b =>
      dsimp [clMul, clOne]
      rw [clInvolution_zero n, clInvolution_one n, clMul_one n, clMul_zero n, clMul_zero n,
          clMul_one n, clSmul_zero n, clAdd_zero n, clZero_add n]

private theorem clAdd_four (n : Nat) (a b c d : CliffordRaw K n) :
    clAdd n (clAdd n a b) (clAdd n c d) = clAdd n (clAdd n a c) (clAdd n b d) := by
  rw [clAdd_assoc n a b, ← clAdd_assoc n b c d, clAdd_comm n b c,
      clAdd_assoc n c b d, ← clAdd_assoc n a c]

theorem clLeft_distrib : ∀ (n : Nat) (d : Fin n → K) (x y z : CliffordRaw K n),
    clMul n d x (clAdd n y z) = clAdd n (clMul n d x y) (clMul n d x z)
  | 0, _, x, y, z => UnitalRing.left_distrib x y z
  | n + 1, d, x, y, z => by
    dsimp [clMul, clAdd]
    rw [clInvolution_add n, clInvolution_add n]
    rw [clLeft_distrib n, clLeft_distrib n, clLeft_distrib n, clLeft_distrib n, clSmul_add n]
    exact Prod.ext (clAdd_four n _ _ _ _) (clAdd_four n _ _ _ _)

theorem clRight_distrib : ∀ (n : Nat) (d : Fin n → K) (x y z : CliffordRaw K n),
    clMul n d (clAdd n x y) z = clAdd n (clMul n d x z) (clMul n d y z)
  | 0, _, x, y, z => UnitalRing.right_distrib x y z
  | n + 1, d, x, y, z => by
    dsimp [clMul, clAdd]
    rw [clRight_distrib n, clRight_distrib n, clRight_distrib n, clRight_distrib n, clSmul_add n]
    exact Prod.ext (clAdd_four n _ _ _ _) (clAdd_four n _ _ _ _)

theorem clSmul_mul_assoc : ∀ (n : Nat) (d : Fin n → K) (c : K) (x y : CliffordRaw K n),
    clMul n d (clSmul n c x) y = clSmul n c (clMul n d x y)
  | 0, _, c, x, y => UnitalRing.mul_assoc c x y
  | n + 1, d, c, x, y => by
    dsimp [clMul, clSmul]
    rw [clSmul_mul_assoc n, clSmul_mul_assoc n, clSmul_mul_assoc n, clSmul_mul_assoc n]
    apply Prod.ext
    · dsimp
      rw [clSmul_add n, ← clMul_smul n (finLast d) c, FieldStructure.mul_comm (finLast d) c,
          clMul_smul n c (finLast d)]
    · dsimp
      rw [clSmul_add n]

theorem clMul_smul_comm : ∀ (n : Nat) (d : Fin n → K) (c : K) (x y : CliffordRaw K n),
    clMul n d x (clSmul n c y) = clSmul n c (clMul n d x y)
  | 0, _, c, x, y => by
    calc
      x * (c * y) = (x * c) * y := (UnitalRing.mul_assoc x c y).symm
      _ = (c * x) * y := by rw [FieldStructure.mul_comm x c]
      _ = c * (x * y) := UnitalRing.mul_assoc c x y
  | n + 1, d, c, x, y => by
    dsimp [clMul, clSmul]
    rw [clInvolution_smul n, clInvolution_smul n]
    rw [clMul_smul_comm n, clMul_smul_comm n, clMul_smul_comm n, clMul_smul_comm n]
    apply Prod.ext
    · dsimp
      rw [clSmul_add n, ← clMul_smul n (finLast d) c, FieldStructure.mul_comm (finLast d) c,
          clMul_smul n c (finLast d)]
    · dsimp
      rw [clSmul_add n]

theorem clMul_neg : ∀ (n : Nat) (d : Fin n → K) (x y : CliffordRaw K n),
    clMul n d x (clNeg n y) = clNeg n (clMul n d x y)
  | 0, _, x, y => mul_neg_ring x y
  | n + 1, d, x, y => by
    dsimp [clMul, clNeg]
    rw [clInvolution_neg n, clInvolution_neg n, clMul_neg n, clMul_neg n, clMul_neg n, clMul_neg n,
        clSmul_neg n, ← clNeg_add n, ← clNeg_add n]

theorem clNeg_mul : ∀ (n : Nat) (d : Fin n → K) (x y : CliffordRaw K n),
    clMul n d (clNeg n x) y = clNeg n (clMul n d x y)
  | 0, _, x, y => neg_mul_ring x y
  | n + 1, d, x, y => by
    dsimp [clMul, clNeg]
    rw [clNeg_mul n, clNeg_mul n, clNeg_mul n, clNeg_mul n, clSmul_neg n,
        ← clNeg_add n, ← clNeg_add n]

theorem clInvolution_mul : ∀ (n : Nat) (d : Fin n → K) (x y : CliffordRaw K n),
    clInvolution n (clMul n d x y) = clMul n d (clInvolution n x) (clInvolution n y)
  | 0, _, _, _ => rfl
  | n + 1, d, x, y => by
    dsimp [clMul, clInvolution]
    apply Prod.ext
    · dsimp
      rw [clInvolution_add n, clInvolution_smul n, clInvolution_mul n, clInvolution_mul n,
          clInvolution_neg n, clNeg_mul n, clMul_neg n, clNeg_neg n]
    · dsimp
      rw [clInvolution_add n, clNeg_add n, clInvolution_mul n, clInvolution_mul n,
          clMul_neg n, clNeg_mul n]

theorem clMul_assoc : ∀ (n : Nat) (d : Fin n → K) (x y z : CliffordRaw K n),
    clMul n d (clMul n d x y) z = clMul n d x (clMul n d y z)
  | 0, _, x, y, z => UnitalRing.mul_assoc x y z
  | n + 1, d, x, y, z => by
    dsimp [clMul]
    let d' := finInit d
    let dn := finLast d
    apply Prod.ext
    · dsimp
      rw [clRight_distrib n, clRight_distrib n, clSmul_add n,
          clLeft_distrib n, clInvolution_add n, clLeft_distrib n, clSmul_add n]
      rw [clSmul_mul_assoc n, clInvolution_mul n, clInvolution_mul n,
          clInvolution_idem n, clMul_smul_comm n]
      rw [clMul_assoc n, clMul_assoc n, clMul_assoc n, clMul_assoc n]
      rw [clAdd_assoc n (clMul n d' x.1 (clMul n d' y.1 z.1)),
          clAdd_assoc n (clMul n d' x.1 (clMul n d' y.1 z.1))]
      congr 1
      rw [← clAdd_assoc n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.1))),
          clAdd_comm n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.1)))
                       (clSmul n dn (clMul n d' x.1 (clMul n d' y.2 (clInvolution n z.2)))),
          clAdd_assoc n,
          clAdd_comm n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.1)))]
    · dsimp
      rw [clRight_distrib n, clRight_distrib n,
          clLeft_distrib n, clInvolution_add n, clLeft_distrib n]
      rw [clSmul_mul_assoc n, clInvolution_smul n, clMul_smul_comm n,
          clInvolution_mul n, clInvolution_mul n, clInvolution_idem n]
      rw [clMul_assoc n, clMul_assoc n, clMul_assoc n, clMul_assoc n]
      rw [clAdd_assoc n (clMul n d' x.1 (clMul n d' y.1 z.2)),
          clAdd_assoc n (clMul n d' x.1 (clMul n d' y.1 z.2))]
      congr 1
      rw [← clAdd_assoc n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.2))),
          clAdd_comm n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.2)))
                       (clMul n d' x.1 (clMul n d' y.2 (clInvolution n z.1))),
          clAdd_assoc n,
          clAdd_comm n (clSmul n dn (clMul n d' x.2 (clMul n d' (clInvolution n y.2) z.2)))]

end RawOps

/-- Genuine 2^n-dimensional Clifford algebra Cl(K^n, d). -/
structure Clifford (K : Type u) [FieldStructure K] (n : Nat) (d : Fin n → K) where
  raw : CliffordRaw K n

theorem Clifford.ext {K : Type u} [FieldStructure K] {n : Nat} {d : Fin n → K}
    {x y : Clifford K n d} (h : x.raw = y.raw) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance cliffordKAlgebra (K : Type u) [FieldStructure K] (n : Nat) (d : Fin n → K) :
    KAlgebra K (Clifford K n d) where
  zero := ⟨clZero n⟩
  one := ⟨clOne n⟩
  add x y := ⟨clAdd n x.raw y.raw⟩
  neg x := ⟨clNeg n x.raw⟩
  mul x y := ⟨clMul n d x.raw y.raw⟩
  smul c x := ⟨clSmul n c x.raw⟩
  add_assoc x y z := Clifford.ext (clAdd_assoc n x.raw y.raw z.raw)
  add_comm x y := Clifford.ext (clAdd_comm n x.raw y.raw)
  zero_add x := Clifford.ext (clZero_add n x.raw)
  neg_add_cancel x := Clifford.ext (clNeg_add_cancel n x.raw)
  mul_assoc x y z := Clifford.ext (clMul_assoc n d x.raw y.raw z.raw)
  one_mul x := Clifford.ext (clOne_mul n d x.raw)
  mul_one x := Clifford.ext (clMul_one n d x.raw)
  left_distrib x y z := Clifford.ext (clLeft_distrib n d x.raw y.raw z.raw)
  right_distrib x y z := Clifford.ext (clRight_distrib n d x.raw y.raw z.raw)
  one_smul x := Clifford.ext (clOne_smul n x.raw)
  mul_smul a b x := Clifford.ext (clMul_smul n a b x.raw)
  smul_zero a := Clifford.ext (clSmul_zero n a)
  smul_add a x y := Clifford.ext (clSmul_add n a x.raw y.raw)
  add_smul a b x := Clifford.ext (clAdd_smul n a b x.raw)
  zero_smul x := Clifford.ext (clZero_smul n x.raw)
  smul_mul_assoc a x y := Clifford.ext (clSmul_mul_assoc n d a x.raw y.raw)
  mul_smul_comm a x y := Clifford.ext (clMul_smul_comm n d a x.raw y.raw)

/-! ### Exact K-Dimension 2^n of `Clifford K n d` -/

section Dimension

variable {K : Type u} [FieldStructure K]

private theorem pow2_step (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  rw [Nat.pow_succ]
  omega

def rawFromCoords : (n : Nat) → (Fin (2 ^ n) → K) → CliffordRaw K n
  | 0, f => f ⟨0, by omega⟩
  | n + 1, f =>
    have hstep := pow2_step n
    (rawFromCoords n (fun i => f ⟨i.val, by omega⟩),
     rawFromCoords n (fun i => f ⟨2 ^ n + i.val, by omega⟩))

def rawToCoords : (n : Nat) → CliffordRaw K n → (Fin (2 ^ n) → K)
  | 0, x => fun _ => x
  | n + 1, x => fun k =>
    if h : k.val < 2 ^ n then
      rawToCoords n x.1 ⟨k.val, h⟩
    else
      have hstep := pow2_step n
      rawToCoords n x.2 ⟨k.val - 2 ^ n, by omega⟩

omit [FieldStructure K] in
theorem rawTo_from : ∀ (n : Nat) (f : Fin (2 ^ n) → K),
    rawToCoords n (rawFromCoords n f) = f
  | 0, f => by
    funext k
    have hk : k = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hk]
    rfl
  | n + 1, f => by
    funext k
    unfold rawToCoords rawFromCoords
    dsimp
    split
    · next h =>
      rw [rawTo_from n]
    · next h =>
      rw [rawTo_from n]
      congr 1
      apply Fin.ext
      dsimp
      omega

omit [FieldStructure K] in
theorem rawFrom_to : ∀ (n : Nat) (x : CliffordRaw K n),
    rawFromCoords n (rawToCoords n x) = x
  | 0, _ => rfl
  | n + 1, x => by
    cases x with
    | mk a b =>
      unfold rawFromCoords rawToCoords
      dsimp
      apply Prod.ext
      · have h1 : (fun i : Fin (2 ^ n) =>
            if h : i.val < 2 ^ n then rawToCoords n a ⟨i.val, h⟩
            else rawToCoords n b ⟨i.val - 2 ^ n, by have := pow2_step n; omega⟩) =
            rawToCoords n a := by
          funext i
          rw [dif_pos i.isLt]
        rw [h1, rawFrom_to n]
      · have h2 : (fun i : Fin (2 ^ n) =>
            if h : 2 ^ n + i.val < 2 ^ n then rawToCoords n a ⟨2 ^ n + i.val, h⟩
            else rawToCoords n b ⟨2 ^ n + i.val - 2 ^ n, by have := pow2_step n; omega⟩) =
            rawToCoords n b := by
          funext i
          have hnlt : ¬ (2 ^ n + i.val < 2 ^ n) := by omega
          rw [dif_neg hnlt]
          congr 1
          apply Fin.ext
          dsimp
          omega
        rw [h2, rawFrom_to n]

theorem rawFromCoords_add : ∀ (n : Nat) (f g : Fin (2 ^ n) → K),
    rawFromCoords n (f + g) = clAdd n (rawFromCoords n f) (rawFromCoords n g)
  | 0, _, _ => rfl
  | n + 1, f, g => Prod.ext
      (rawFromCoords_add n (fun i => f ⟨i.val, by have := pow2_step n; omega⟩)
                           (fun i => g ⟨i.val, by have := pow2_step n; omega⟩))
      (rawFromCoords_add n (fun i => f ⟨2 ^ n + i.val, by have := pow2_step n; omega⟩)
                           (fun i => g ⟨2 ^ n + i.val, by have := pow2_step n; omega⟩))

theorem rawFromCoords_smul : ∀ (n : Nat) (c : K) (f : Fin (2 ^ n) → K),
    rawFromCoords n (KSMul.smul c f) = clSmul n c (rawFromCoords n f)
  | 0, _, _ => rfl
  | n + 1, c, f => Prod.ext
      (rawFromCoords_smul n c (fun i => f ⟨i.val, by have := pow2_step n; omega⟩))
      (rawFromCoords_smul n c (fun i => f ⟨2 ^ n + i.val, by have := pow2_step n; omega⟩))

/-- Canonical K-linear isomorphism `(Fin (2^n) → K) ≃ₗ[K] Clifford K n d`. -/
def cliffordCoordIso (K : Type u) [FieldStructure K] (n : Nat) (d : Fin n → K) :
    KLinearIso K (Fin (2 ^ n) → K) (Clifford K n d) where
  toFun f := ⟨rawFromCoords n f⟩
  invFun x := rawToCoords n x.raw
  map_add f g := Clifford.ext (rawFromCoords_add n f g)
  map_smul c f := Clifford.ext (rawFromCoords_smul n c f)
  left_inv f := rawTo_from n f
  right_inv x := Clifford.ext (rawFrom_to n x.raw)

theorem clifford_hasKDim (K : Type u) [FieldStructure K] (n : Nat) (d : Fin n → K) :
    HasKDim K (Clifford K n d) (2 ^ n) :=
  ⟨cliffordCoordIso K n d⟩

end Dimension

/-! ### Canonical Vector Embedding `iota`, Clifford Identity, and Universal Property -/

section UniversalProperty

variable {K : Type u} [FieldStructure K]

def clIota : (n : Nat) → (Fin n → K) → CliffordRaw K n
  | 0, _ => clZero 0
  | n + 1, v => (clIota n (finInit v), clSmul n (finLast v) (clOne n))

/-- Canonical K-linear embedding ι : (Fin n → K) → Cl(K^n, d). -/
def Clifford.iota {n : Nat} (d : Fin n → K) (v : Fin n → K) : Clifford K n d :=
  ⟨clIota n v⟩

/-- Orthogonal basis generator e_k = ι(δ_k) ∈ Cl(K^n, d). -/
def Clifford.gen {n : Nat} (d : Fin n → K) (k : Fin n) : Clifford K n d :=
  Clifford.iota d (fun i => if i = k then 1 else 0)

theorem clIota_add : ∀ (n : Nat) (u v : Fin n → K),
    clIota n (u + v) = clAdd n (clIota n u) (clIota n v)
  | 0, _, _ => (AddCommGrp.zero_add 0).symm
  | n + 1, u, v => Prod.ext
      (clIota_add n (finInit u) (finInit v))
      (clAdd_smul n (finLast u) (finLast v) (clOne n))

theorem clIota_smul : ∀ (n : Nat) (c : K) (v : Fin n → K),
    clIota n (KSMul.smul c v) = clSmul n c (clIota n v)
  | 0, c, _ => (mul_zero_ring c).symm
  | n + 1, c, v => Prod.ext
      (clIota_smul n c (finInit v))
      (clMul_smul n c (finLast v) (clOne n))

theorem clInvolution_iota : ∀ (n : Nat) (v : Fin n → K),
    clInvolution n (clIota n v) = clNeg n (clIota n v)
  | 0, _ => neg_zero_grp.symm
  | n + 1, v => Prod.ext
      (clInvolution_iota n (finInit v))
      (by dsimp [clInvolution, clIota, clNeg]; rw [clInvolution_smul n, clInvolution_one n])

theorem clIota_sq : ∀ (n : Nat) (d : Fin n → K) (v : Fin n → K),
    clMul n d (clIota n v) (clIota n v) = clSmul n (quadForm d v) (clOne n)
  | 0, _, _ => by
    dsimp [clMul, clIota, quadForm, clSmul, clOne, clZero]
    rw [zero_mul_ring, zero_mul_ring]
  | n + 1, d, v => by
    dsimp [clMul, clIota, quadForm, clSmul, clOne]
    rw [clIota_sq n (finInit d) (finInit v)]
    rw [clInvolution_smul n, clInvolution_one n, clInvolution_iota n]
    apply Prod.ext
    · dsimp
      rw [clSmul_mul_assoc n, clMul_smul_comm n, clOne_mul n,
          ← clMul_smul n (finLast v) (finLast v), ← clMul_smul n (finLast d),
          ← clAdd_smul n]
    · dsimp
      rw [clMul_smul_comm n, clMul_one n, clSmul_mul_assoc n, clOne_mul n,
          clSmul_neg n, clAdd_neg_cancel n, clSmul_zero n]

/-- Fundamental Clifford Identity: ι(v) * ι(v) = Q_d(v) • 1 for ALL n and ALL v ∈ K^n. -/
theorem Clifford.iota_sq {n : Nat} (d : Fin n → K) (v : Fin n → K) :
    Clifford.iota d v * Clifford.iota d v = algebraMap K (quadForm d v) :=
  Clifford.ext (clIota_sq n d v)

theorem Clifford.iota_add {n : Nat} (d : Fin n → K) (u v : Fin n → K) :
    Clifford.iota d (u + v) = Clifford.iota d u + Clifford.iota d v :=
  Clifford.ext (clIota_add n u v)

theorem Clifford.iota_smul {n : Nat} (d : Fin n → K) (c : K) (v : Fin n → K) :
    Clifford.iota d (KSMul.smul c v) = KSMul.smul c (Clifford.iota d v) :=
  Clifford.ext (clIota_smul n c v)

/-! ### Universal Property of `Clifford K n d` -/

/-- Predicate that a map f : (Fin n → K) → B is a K-linear Clifford map for Q_d. -/
structure IsCliffordMap {n : Nat} (d : Fin n → K) {B : Type v} [KAlgebra K B]
    (f : (Fin n → K) → B) : Prop where
  map_add : ∀ u w : Fin n → K, f (u + w) = f u + f w
  map_smul : ∀ c : K, ∀ u : Fin n → K, f (KSMul.smul c u) = KSMul.smul c (f u)
  map_sq : ∀ v : Fin n → K, f v * f v = algebraMap K (quadForm d v)

private theorem quadForm_snoc_zero {n : Nat} (d : Fin (n + 1) → K) (v' : Fin n → K) :
    quadForm d (finSnoc v' 0) = quadForm (finInit d) v' := by
  change quadForm (finInit d) (finInit (finSnoc v' 0)) +
    finLast d * (finLast (finSnoc v' 0) * finLast (finSnoc v' 0)) = quadForm (finInit d) v'
  rw [finInit_snoc, finLast_snoc, zero_mul_ring, mul_zero_ring, add_zero_grp]

private theorem quadForm_zero_snoc {n : Nat} (d : Fin (n + 1) → K) (c : K) :
    quadForm d (finSnoc (0 : Fin n → K) c) = finLast d * (c * c) := by
  change quadForm (finInit d) (finInit (finSnoc (0 : Fin n → K) c)) +
    finLast d * (finLast (finSnoc (0 : Fin n → K) c) * finLast (finSnoc (0 : Fin n → K) c)) =
    finLast d * (c * c)
  rw [finInit_snoc, finLast_snoc, quadForm_zero (finInit d), AddCommGrp.zero_add]

private theorem isCliffordMap_init {n : Nat} {d : Fin (n + 1) → K} {B : Type v} [KAlgebra K B]
    {f : (Fin (n + 1) → K) → B} (hf : IsCliffordMap d f) :
    IsCliffordMap (finInit d) (fun v' => f (finSnoc v' 0)) where
  map_add u w := by
    have hsnoc : finSnoc (u + w) (0 : K) = finSnoc u 0 + finSnoc w 0 := by
      funext i
      change (if h : i.val < n then u ⟨i.val, h⟩ + w ⟨i.val, h⟩ else 0) =
        (if h : i.val < n then u ⟨i.val, h⟩ else 0) + (if h : i.val < n then w ⟨i.val, h⟩ else 0)
      split
      · rfl
      · exact (AddCommGrp.zero_add 0).symm
    rw [hsnoc, hf.map_add]
  map_smul c u := by
    have hsnoc : finSnoc (KSMul.smul c u) (0 : K) = KSMul.smul c (finSnoc u 0) := by
      funext i
      change (if h : i.val < n then c * u ⟨i.val, h⟩ else 0) =
        c * (if h : i.val < n then u ⟨i.val, h⟩ else 0)
      split
      · rfl
      · exact (mul_zero_ring c).symm
    rw [hsnoc, hf.map_smul]
  map_sq v' := by
    rw [hf.map_sq, quadForm_snoc_zero]

private theorem cliffordMap_anticomm_last {n : Nat} {d : Fin (n + 1) → K}
    {B : Type v} [KAlgebra K B] {f : (Fin (n + 1) → K) → B} (hf : IsCliffordMap d f)
    (v' : Fin n → K) :
    let u := finSnoc v' (0 : K)
    let en := finSnoc (0 : Fin n → K) (1 : K)
    f en * f u = -(f u * f en) := by
  intro u en
  have hsum_q : quadForm d (u + en) = quadForm d u + quadForm d en := by
    have huv : u + en = finSnoc v' 1 := by
      funext i
      change (if h : i.val < n then v' ⟨i.val, h⟩ else 0) +
        (if h : i.val < n then (0 : K) else 1) =
        (if h : i.val < n then v' ⟨i.val, h⟩ else 1)
      split
      · exact add_zero_grp _
      · exact AddCommGrp.zero_add 1
    rw [huv, quadForm_snoc_zero, quadForm_zero_snoc]
    change quadForm (finInit d) (finInit (finSnoc v' 1)) +
      finLast d * (finLast (finSnoc v' 1) * finLast (finSnoc v' 1)) =
      quadForm (finInit d) v' + finLast d * (1 * 1)
    rw [finInit_snoc, finLast_snoc]
  have hsq_sum : (f u + f en) * (f u + f en) = f u * f u + f en * f en := by
    calc
      (f u + f en) * (f u + f en) = f (u + en) * f (u + en) := by rw [← hf.map_add]
      _ = algebraMap K (quadForm d (u + en)) := hf.map_sq (u + en)
      _ = algebraMap K (quadForm d u + quadForm d en) := by rw [hsum_q]
      _ = algebraMap K (quadForm d u) + algebraMap K (quadForm d en) :=
          KAlgebra.add_smul _ _ 1
      _ = f u * f u + f en * f en := by rw [← hf.map_sq u, ← hf.map_sq en]
  have hexp : (f u + f en) * (f u + f en) =
      f u * f u + (f u * f en + f en * f u) + f en * f en := by
    rw [UnitalRing.right_distrib, UnitalRing.left_distrib, UnitalRing.left_distrib]
    rw [AddCommGrp.add_assoc (f u * f u), AddCommGrp.add_assoc (f u * f u),
        AddCommGrp.add_assoc (f u * f en)]
  rw [hexp] at hsq_sum
  have hmid : f u * f en + f en * f u = 0 := by
    have h1 : f u * f u + (f u * f en + f en * f u) = f u * f u :=
      add_right_cancel_grp hsq_sum
    apply add_left_cancel_grp (a := f u * f u)
    rw [add_zero_grp]
    exact h1
  symm
  exact neg_eq_of_add_eq_zero hmid

def clLiftRaw {B : Type v} [KAlgebra K B] :
    (n : Nat) → ((Fin n → K) → B) → CliffordRaw K n → B
  | 0, _, x => algebraMap K x
  | n + 1, f, x =>
    let f' : (Fin n → K) → B := fun v' => f (finSnoc v' 0)
    let en : Fin (n + 1) → K := finSnoc (0 : Fin n → K) 1
    clLiftRaw n f' x.1 + clLiftRaw n f' x.2 * f en

private theorem clLiftRaw_zero {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (f : (Fin n → K) → B), clLiftRaw n f (clZero n) = (0 : B)
  | 0, _ => KAlgebra.zero_smul 1
  | n + 1, f => by
    unfold clLiftRaw clZero
    dsimp
    rw [clLiftRaw_zero n, zero_mul_ring, AddCommGrp.zero_add]

private theorem clLiftRaw_one {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (f : (Fin n → K) → B), clLiftRaw n f (clOne n) = (1 : B)
  | 0, _ => KAlgebra.one_smul 1
  | n + 1, f => by
    unfold clLiftRaw clOne
    dsimp
    rw [clLiftRaw_one n, clLiftRaw_zero n, zero_mul_ring, add_zero_grp]

private theorem clLiftRaw_add {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (f : (Fin n → K) → B) (x y : CliffordRaw K n),
      clLiftRaw n f (clAdd n x y) = clLiftRaw n f x + clLiftRaw n f y
  | 0, _, x, y => KAlgebra.add_smul x y 1
  | n + 1, f, x, y => by
    unfold clLiftRaw clAdd
    dsimp
    rw [clLiftRaw_add n, clLiftRaw_add n, UnitalRing.right_distrib]
    rw [AddCommGrp.add_assoc (clLiftRaw n _ x.1),
        ← AddCommGrp.add_assoc (clLiftRaw n _ y.1),
        AddCommGrp.add_comm (clLiftRaw n _ y.1),
        AddCommGrp.add_assoc, ← AddCommGrp.add_assoc]

private theorem clLiftRaw_smul {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (f : (Fin n → K) → B) (c : K) (x : CliffordRaw K n),
      clLiftRaw n f (clSmul n c x) = KSMul.smul c (clLiftRaw n f x)
  | 0, _, c, x => KAlgebra.mul_smul c x 1
  | n + 1, f, c, x => by
    unfold clLiftRaw clSmul
    dsimp
    rw [clLiftRaw_smul n, clLiftRaw_smul n, KAlgebra.smul_mul_assoc, KAlgebra.smul_add]

private theorem clNeg_eq_neg_one_smul :
    ∀ (m : Nat) (y : CliffordRaw K m), clNeg m y = clSmul m (-1 : K) y
  | 0, y => by
    change -y = (-1 : K) * y
    rw [neg_mul_ring, UnitalRing.one_mul]
  | m + 1, y => Prod.ext (clNeg_eq_neg_one_smul m y.1) (clNeg_eq_neg_one_smul m y.2)

private theorem clLiftRaw_neg {B : Type v} [KAlgebra K B] (n : Nat)
    (f : (Fin n → K) → B) (x : CliffordRaw K n) :
    clLiftRaw n f (clNeg n x) = -(clLiftRaw n f x) := by
  rw [clNeg_eq_neg_one_smul n x, clLiftRaw_smul, neg_smul_vs, KVectorSpace.one_smul]

/-- Key intertwining lemma: any w ∈ B anticommuting with all f(v) satisfies
    w * Φ(x) = Φ(α(x)) * w. -/
private theorem clLiftRaw_intertwine {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (f : (Fin n → K) → B) (w : B),
      (∀ v : Fin n → K, w * f v = -(f v * w)) →
      ∀ (x : CliffordRaw K n),
      w * clLiftRaw n f x = clLiftRaw n f (clInvolution n x) * w
  | 0, _, w, _, x => by
    dsimp [clLiftRaw, clInvolution]
    exact (algebraMap_commutes K x w).symm
  | n + 1, f, w, hw, x => by
    dsimp [clLiftRaw, clInvolution]
    let f' : (Fin n → K) → B := fun v' => f (finSnoc v' 0)
    let en : Fin (n + 1) → K := finSnoc (0 : Fin n → K) 1
    have hw' : ∀ v' : Fin n → K, w * f' v' = -(f' v' * w) := fun v' => hw (finSnoc v' 0)
    have hwen : w * f en = -(f en * w) := hw en
    rw [UnitalRing.left_distrib, clLiftRaw_intertwine n f' w hw' x.1]
    rw [← UnitalRing.mul_assoc w (clLiftRaw n f' x.2) (f en),
        clLiftRaw_intertwine n f' w hw' x.2,
        UnitalRing.mul_assoc (clLiftRaw n f' (clInvolution n x.2)) w (f en),
        hwen, mul_neg_ring, clLiftRaw_neg n f', ← neg_mul_ring,
        ← UnitalRing.mul_assoc, ← UnitalRing.right_distrib]

private theorem clLiftRaw_mul {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (d : Fin n → K)
      (f : (Fin n → K) → B), IsCliffordMap d f → ∀ (x y : CliffordRaw K n),
      clLiftRaw n f (clMul n d x y) = clLiftRaw n f x * clLiftRaw n f y
  | 0, _, _, _, x, y => by
    dsimp [clLiftRaw, clMul]
    unfold algebraMap
    rw [KAlgebra.mul_smul, KAlgebra.smul_mul_assoc, UnitalRing.one_mul]
  | n + 1, d, f, hf, x, y => by
    dsimp [clLiftRaw, clMul]
    let f' : (Fin n → K) → B := fun v' => f (finSnoc v' 0)
    let en : Fin (n + 1) → K := finSnoc (0 : Fin n → K) 1
    have hf' : IsCliffordMap (finInit d) f' := isCliffordMap_init hf
    have hen_anti : ∀ v' : Fin n → K, f en * f' v' = -(f' v' * f en) :=
      cliffordMap_anticomm_last hf
    have hen_sq : f en * f en = algebraMap K (finLast d) := by
      rw [hf.map_sq en, quadForm_zero_snoc, UnitalRing.mul_one, UnitalRing.mul_one]
    rw [clLiftRaw_add n, clLiftRaw_smul n, clLiftRaw_add n]
    rw [clLiftRaw_mul n (finInit d) f' hf', clLiftRaw_mul n (finInit d) f' hf',
        clLiftRaw_mul n (finInit d) f' hf', clLiftRaw_mul n (finInit d) f' hf']
    let A1 := clLiftRaw n f' x.1
    let B1 := clLiftRaw n f' x.2
    let A2 := clLiftRaw n f' y.1
    let B2 := clLiftRaw n f' y.2
    have hinter_y1 : f en * A2 = clLiftRaw n f' (clInvolution n y.1) * f en :=
      clLiftRaw_intertwine n f' (f en) hen_anti y.1
    have hinter_y2 : f en * B2 = clLiftRaw n f' (clInvolution n y.2) * f en :=
      clLiftRaw_intertwine n f' (f en) hen_anti y.2
    have hterm_b1b2 : (B1 * f en) * (B2 * f en) =
        KSMul.smul (finLast d) (B1 * clLiftRaw n f' (clInvolution n y.2)) := by
      calc
        (B1 * f en) * (B2 * f en) = B1 * ((f en * B2) * f en) := by
          rw [UnitalRing.mul_assoc B1 (f en), ← UnitalRing.mul_assoc (f en) B2 (f en)]
        _ = B1 * ((clLiftRaw n f' (clInvolution n y.2) * f en) * f en) := by rw [hinter_y2]
        _ = (B1 * clLiftRaw n f' (clInvolution n y.2)) * (f en * f en) := by
          rw [UnitalRing.mul_assoc (clLiftRaw n f' (clInvolution n y.2)) (f en) (f en),
              ← UnitalRing.mul_assoc B1]
        _ = (B1 * clLiftRaw n f' (clInvolution n y.2)) * KSMul.smul (finLast d) 1 := by
          rw [hen_sq]; rfl
        _ = KSMul.smul (finLast d) ((B1 * clLiftRaw n f' (clInvolution n y.2)) * 1) :=
          KAlgebra.mul_smul_comm _ _ _
        _ = KSMul.smul (finLast d) (B1 * clLiftRaw n f' (clInvolution n y.2)) := by
          rw [UnitalRing.mul_one]
    have hterm_b1a2 : (B1 * f en) * A2 =
        (B1 * clLiftRaw n f' (clInvolution n y.1)) * f en := by
      rw [UnitalRing.mul_assoc B1 (f en) A2, hinter_y1, ← UnitalRing.mul_assoc]
    change A1 * A2 + KSMul.smul (finLast d) (B1 * clLiftRaw n f' (clInvolution n y.2)) +
        (A1 * B2 + B1 * clLiftRaw n f' (clInvolution n y.1)) * f en =
      (A1 + B1 * f en) * (A2 + B2 * f en)
    rw [UnitalRing.left_distrib (A1 + B1 * f en),
        UnitalRing.right_distrib A1 (B1 * f en) A2,
        UnitalRing.right_distrib A1 (B1 * f en) (B2 * f en)]
    rw [hterm_b1b2, hterm_b1a2, UnitalRing.right_distrib, ← UnitalRing.mul_assoc A1 B2 (f en)]
    rw [AddCommGrp.add_assoc (A1 * A2), AddCommGrp.add_assoc (A1 * A2)]
    congr 1
    rw [← AddCommGrp.add_assoc (KSMul.smul (finLast d) _),
        AddCommGrp.add_comm (KSMul.smul (finLast d) _),
        AddCommGrp.add_comm]

private theorem clLiftRaw_iota {B : Type v} [KAlgebra K B] :
    ∀ (n : Nat) (d : Fin n → K)
      (f : (Fin n → K) → B), IsCliffordMap d f → ∀ (v : Fin n → K),
      clLiftRaw n f (clIota n v) = f v
  | 0, _, f, hf, v => by
    unfold clLiftRaw clIota clZero
    have hv0 : v = (0 : Fin 0 → K) := funext fun i => Fin.elim0 i
    have hf0 : f 0 = 0 := by
      calc
        f 0 = f (KSMul.smul (0 : K) 0) := by rw [KVectorSpace.zero_smul]
        _ = KSMul.smul (0 : K) (f 0) := hf.map_smul 0 0
        _ = 0 := KAlgebra.zero_smul _
    rw [hv0, hf0]
    exact KAlgebra.zero_smul (1 : B)
  | n + 1, d, f, hf, v => by
    unfold clLiftRaw clIota
    dsimp
    let f' : (Fin n → K) → B := fun v' => f (finSnoc v' 0)
    let en : Fin (n + 1) → K := finSnoc (0 : Fin n → K) 1
    have hf' : IsCliffordMap (finInit d) f' := isCliffordMap_init hf
    rw [clLiftRaw_iota n (finInit d) f' hf' (finInit v)]
    rw [clLiftRaw_smul n, clLiftRaw_one n, KAlgebra.smul_mul_assoc, UnitalRing.one_mul]
    rw [← hf.map_smul (finLast v) en, ← hf.map_add]
    congr 1
    funext i
    change (if h : i.val < n then finInit v ⟨i.val, h⟩ else 0) +
      finLast v * (if h : i.val < n then 0 else 1) = v i
    split
    · next h =>
      rw [mul_zero_ring, add_zero_grp]
      rfl
    · next h =>
      rw [UnitalRing.mul_one, AddCommGrp.zero_add]
      have hi : i = ⟨n, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [hi]
      rfl

/-- Universal Property (Existence): Every K-linear Clifford map f : K^n → B lifts to a
    K-algebra homomorphism `Clifford.lift d f hf : AlgHom K (Clifford K n d) B`. -/
def Clifford.lift {n : Nat} (d : Fin n → K) {B : Type v} [KAlgebra K B]
    (f : (Fin n → K) → B) (hf : IsCliffordMap d f) : AlgHom K (Clifford K n d) B where
  toFun x := clLiftRaw n f x.raw
  map_zero := clLiftRaw_zero n f
  map_one := clLiftRaw_one n f
  map_add x y := clLiftRaw_add n f x.raw y.raw
  map_mul x y := clLiftRaw_mul n d f hf x.raw y.raw
  map_smul c x := clLiftRaw_smul n f c x.raw

theorem Clifford.lift_iota {n : Nat} (d : Fin n → K) {B : Type v} [KAlgebra K B]
    (f : (Fin n → K) → B) (hf : IsCliffordMap d f) (v : Fin n → K) :
    (Clifford.lift d f hf).toFun (Clifford.iota d v) = f v :=
  clLiftRaw_iota n d f hf v

/-- Embedding of `Clifford K n (finInit d)` as the even-part subalgebra `(a, 0)` of `Clifford K (n+1) d`. -/
def Clifford.inl {n : Nat} (d : Fin (n + 1) → K) :
    AlgHom K (Clifford K n (finInit d)) (Clifford K (n + 1) d) where
  toFun a := ⟨(a.raw, clZero n)⟩
  map_zero := rfl
  map_one := rfl
  map_add a1 a2 := Clifford.ext (Prod.ext rfl (clAdd_zero n (clZero n)).symm)
  map_mul a1 a2 := Clifford.ext (by
    change (clMul n (finInit d) a1.raw a2.raw, clZero n) =
      clMul (n + 1) d (a1.raw, clZero n) (a2.raw, clZero n)
    symm
    dsimp [clMul]
    rw [clInvolution_zero n, clMul_zero n, clZero_mul n, clMul_zero n,
        clSmul_zero n, clAdd_zero n, clAdd_zero n])
  map_smul c a := Clifford.ext (Prod.ext rfl (clSmul_zero n c).symm)

/-- Universal Property (Uniqueness): Any K-algebra homomorphism Ψ agreeing with f on ι(K^n)
    equals `Clifford.lift d f hf`. -/
theorem Clifford.lift_unique {B : Type v} [KAlgebra K B] :
    ∀ {n : Nat} (d : Fin n → K)
      (f : (Fin n → K) → B) (hf : IsCliffordMap d f)
      (Ψ : AlgHom K (Clifford K n d) B),
      (∀ v : Fin n → K, Ψ.toFun (Clifford.iota d v) = f v) →
      ∀ (x : Clifford K n d),
      Ψ.toFun x = (Clifford.lift d f hf).toFun x
  | 0, d, f, hf, Ψ, _, x => by
    let c : K := x.raw
    have hx : x = KSMul.smul c (1 : Clifford K 0 d) := by
      apply Clifford.ext
      change x.raw = c * 1
      exact (UnitalRing.mul_one x.raw).symm
    calc
      Ψ.toFun x = Ψ.toFun (KSMul.smul c (1 : Clifford K 0 d)) := congrArg Ψ.toFun hx
      _ = KSMul.smul c (Ψ.toFun 1) := Ψ.map_smul c 1
      _ = KSMul.smul c (1 : B) := by rw [Ψ.map_one]
      _ = (Clifford.lift d f hf).toFun x := rfl
  | n + 1, d, f, hf, Ψ, hΨ, x => by
    let f' : (Fin n → K) → B := fun v' => f (finSnoc v' 0)
    have hf' : IsCliffordMap (finInit d) f' := isCliffordMap_init hf
    let Ψ' : AlgHom K (Clifford K n (finInit d)) B := {
      toFun := fun a => Ψ.toFun ((Clifford.inl d).toFun a)
      map_zero := by rw [(Clifford.inl d).map_zero, Ψ.map_zero]
      map_one := by rw [(Clifford.inl d).map_one, Ψ.map_one]
      map_add := fun a1 a2 => by rw [(Clifford.inl d).map_add, Ψ.map_add]
      map_mul := fun a1 a2 => by rw [(Clifford.inl d).map_mul, Ψ.map_mul]
      map_smul := fun c a => by rw [(Clifford.inl d).map_smul, Ψ.map_smul]
    }
    have hΨ' : ∀ v' : Fin n → K, Ψ'.toFun (Clifford.iota (finInit d) v') = f' v' := by
      intro v'
      have hinl : (Clifford.inl d).toFun (Clifford.iota (finInit d) v') =
          Clifford.iota d (finSnoc v' 0) := by
        apply Clifford.ext
        change (clIota n v', clZero n) =
          (clIota n (finInit (finSnoc v' 0)), clSmul n (finLast (finSnoc v' 0)) (clOne n))
        rw [finInit_snoc, finLast_snoc, clZero_smul n]
      change Ψ.toFun ((Clifford.inl d).toFun (Clifford.iota (finInit d) v')) = f' v'
      rw [hinl, hΨ]
    let en : Fin (n + 1) → K := finSnoc (0 : Fin n → K) 1
    have hen_raw : (Clifford.iota d en).raw = (clZero n, clOne n) := by
      change (clIota n (finInit en), clSmul n (finLast en) (clOne n)) = (clZero n, clOne n)
      have hinit0 : clIota n (finInit en) = clZero n := by
        rw [finInit_snoc]
        have h0 : clIota n (0 : Fin n → K) = clZero n := by
          have := clIota_smul n (0 : K) (0 : Fin n → K)
          rw [KVectorSpace.zero_smul, clZero_smul n] at this
          exact this
        exact h0
      rw [hinit0, finLast_snoc, clOne_smul n]
    have hdecomp : x = (Clifford.inl d).toFun ⟨x.raw.1⟩ +
        (Clifford.inl d).toFun ⟨x.raw.2⟩ * Clifford.iota d en := by
      apply Clifford.ext
      change x.raw = clAdd (n + 1) (x.raw.1, clZero n)
        (clMul (n + 1) d (x.raw.2, clZero n) (Clifford.iota d en).raw)
      rw [hen_raw]
      dsimp [clMul, clAdd]
      rw [clInvolution_one n, clInvolution_zero n, clMul_zero n, clZero_mul n,
          clSmul_zero n, clAdd_zero n, clMul_one n, clZero_mul n,
          clAdd_zero n, clZero_add n, clAdd_zero n]
    calc
      Ψ.toFun x
        = Ψ.toFun ((Clifford.inl d).toFun ⟨x.raw.1⟩) +
            Ψ.toFun ((Clifford.inl d).toFun ⟨x.raw.2⟩) * Ψ.toFun (Clifford.iota d en) := by
          conv => lhs; rw [hdecomp]
          rw [Ψ.map_add, Ψ.map_mul]
      _ = Ψ'.toFun ⟨x.raw.1⟩ + Ψ'.toFun ⟨x.raw.2⟩ * f en := by
          rw [hΨ en]
      _ = (Clifford.lift (finInit d) f' hf').toFun ⟨x.raw.1⟩ +
            (Clifford.lift (finInit d) f' hf').toFun ⟨x.raw.2⟩ * f en := by
          rw [Clifford.lift_unique (finInit d) f' hf' Ψ' hΨ' ⟨x.raw.1⟩,
              Clifford.lift_unique (finInit d) f' hf' Ψ' hΨ' ⟨x.raw.2⟩]
      _ = (Clifford.lift d f hf).toFun x := rfl

end UniversalProperty

end Conjecture00000007610
