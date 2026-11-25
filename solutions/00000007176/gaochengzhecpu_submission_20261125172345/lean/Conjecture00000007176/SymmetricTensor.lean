/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Order-`m`, dimension-`n` symmetric tensors, coordinate permutations, contractions,
homogeneous polynomial forms, standard extremal tensor families (`allOnesTensor`,
`rankOneTensor`, `monomialTensor`, `binomialEntryTensor`), and Qi/Lim spectral
definitions (`IsHEigenpair`, `IsZEigenpair`, `IsEEigenpair`) in Core Lean 4.19.0.
-/
import Conjecture00000007176.SumsInequalities

namespace Conjecture00000007176

/-! ### Enumeration of `Fin n` and Summation `sumFin` -/

/-- Canonical list `[0, 1, ..., n - 1]` of all elements of `Fin n`. -/
def finList : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finList n).map Fin.succ

@[simp] theorem length_finList : ∀ n : Nat, (finList n).length = n
  | 0 => rfl
  | n + 1 => by simp [finList, length_finList n]

theorem mem_finList : ∀ {n : Nat} (i : Fin n), i ∈ finList n
  | 0, ⟨_, h⟩ => by omega
  | n + 1, ⟨0, _⟩ => List.mem_cons_self
  | n + 1, ⟨k + 1, h⟩ => by
    simp only [finList]
    apply List.mem_cons_of_mem
    have hmem := mem_finList (n := n) ⟨k, by omega⟩
    exact List.mem_map.mpr ⟨⟨k, by omega⟩, hmem, rfl⟩

theorem finList_ne_nil {n : Nat} (hn : n ≥ 1) : finList n ≠ [] := by
  intro h
  have hlen : (finList n).length = 0 := by rw [h]; rfl
  rw [length_finList] at hlen
  omega

/-- Sum of `f : Fin n → S` over `i = 0, ..., n - 1`. -/
def sumFin {S : Type v} [CommRing S] {n : Nat} (f : Fin n → S) : S :=
  sumList (finList n) f

theorem sumFin_congr {S : Type v} [CommRing S] {n : Nat} {f g : Fin n → S}
    (h : ∀ i : Fin n, f i = g i) : sumFin f = sumFin g :=
  sumList_congr (fun i _ => h i)

theorem sumFin_const {S : Type v} [CommRing S] (n : Nat) (c : S) :
    sumFin (n := n) (fun _ => c) = natCastR n * c := by
  unfold sumFin
  rw [sumList_const, length_finList]

theorem sumFin_add {S : Type v} [CommRing S] {n : Nat} (f g : Fin n → S) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g :=
  sumList_add (finList n) f g

theorem sumFin_mul_left {S : Type v} [CommRing S] {n : Nat} (c : S) (f : Fin n → S) :
    sumFin (fun i => c * f i) = c * sumFin f :=
  sumList_mul_left (finList n) c f

theorem sumFin_mul_right {S : Type v} [CommRing S] {n : Nat} (f : Fin n → S) (c : S) :
    sumFin (fun i => f i * c) = sumFin f * c :=
  sumList_mul_right (finList n) f c

theorem sumFin_two {S : Type v} [CommRing S] (f : Fin 2 → S) :
    sumFin f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  change f ⟨0, by omega⟩ + (f ⟨1, by omega⟩ + 0) = f ⟨0, by omega⟩ + f ⟨1, by omega⟩
  rw [add_zero_eq]

/-! ### Order-`m` Multi-Indices `Idx n m` and Iterated Summation `sumIdx` -/

/-- Length-`m` coordinate index tuple `(i_1, ..., i_m) ∈ {0, ..., n - 1}^m`. -/
inductive Idx (n : Nat) : Nat → Type where
  | nil : Idx n 0
  | cons : Fin n → Idx n m → Idx n (m + 1)
  deriving DecidableEq

/-- Cartesian cons helper building `[cons i t | i ∈ is, t ∈ ts]`. -/
def consAll {n m : Nat} : List (Fin n) → List (Idx n m) → List (Idx n (m + 1))
  | [], _ => []
  | i :: is, ts => ts.map (Idx.cons i) ++ consAll is ts

theorem length_consAll {n m : Nat} : ∀ (is : List (Fin n)) (ts : List (Idx n m)),
    (consAll is ts).length = is.length * ts.length
  | [], _ => by simp [consAll]
  | i :: is, ts => by
    simp only [consAll, List.length_append, List.length_map, List.length_cons,
               length_consAll is ts]
    rw [Nat.succ_mul, Nat.add_comm]

theorem mem_consAll_of_mem {n m : Nat} {i : Fin n} {t : Idx n m} :
    ∀ {is : List (Fin n)} {ts : List (Idx n m)},
      i ∈ is → t ∈ ts → Idx.cons i t ∈ consAll is ts
  | [], _, hi, _ => by cases hi
  | j :: js, ts, hi, ht => by
    simp only [consAll]
    cases List.mem_cons.mp hi with
    | inl hij =>
      subst hij
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩))
    | inr hjs =>
      exact List.mem_append.mpr (Or.inr (mem_consAll_of_mem hjs ht))

theorem sumList_consAll {S : Type v} [CommRing S] {n m : Nat}
    (is : List (Fin n)) (ts : List (Idx n m)) (F : Idx n (m + 1) → S) :
    sumList (consAll is ts) F =
      sumList is (fun i => sumList ts (fun t => F (Idx.cons i t))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [consAll, sumList_cons]
    rw [sumList_append, sumList_map, ih]

/-- Canonical list of all `n^m` multi-indices of order `m` in dimension `n`. -/
def idxList (n : Nat) : (m : Nat) → List (Idx n m)
  | 0 => [Idx.nil]
  | m + 1 => consAll (finList n) (idxList n m)

@[simp] theorem length_idxList (n : Nat) : ∀ m : Nat, (idxList n m).length = n ^ m
  | 0 => rfl
  | m + 1 => by
    simp only [idxList, length_consAll, length_finList, length_idxList n m]
    rw [Nat.pow_succ, Nat.mul_comm]

theorem mem_idxList {n : Nat} : ∀ {m : Nat} (α : Idx n m), α ∈ idxList n m
  | 0, .nil => List.mem_cons_self
  | _ + 1, .cons i t => mem_consAll_of_mem (mem_finList i) (mem_idxList t)

/-- Sum of `F : Idx n m → S` over all `n^m` multi-indices. -/
def sumIdx {S : Type v} [CommRing S] {n m : Nat} (F : Idx n m → S) : S :=
  sumList (idxList n m) F

@[simp] theorem sumIdx_zero_ord {S : Type v} [CommRing S] {n : Nat} (F : Idx n 0 → S) :
    sumIdx F = F Idx.nil := by
  unfold sumIdx idxList
  simp only [sumList_cons, sumList_nil]
  exact add_zero_eq _

theorem sumIdx_succ_ord {S : Type v} [CommRing S] {n m : Nat} (F : Idx n (m + 1) → S) :
    sumIdx F = sumFin (fun i => sumIdx (fun t => F (Idx.cons i t))) := by
  change sumList (consAll (finList n) (idxList n m)) F =
         sumList (finList n) (fun i => sumList (idxList n m) (fun t => F (Idx.cons i t)))
  exact sumList_consAll (finList n) (idxList n m) F

theorem sumIdx_const {S : Type v} [CommRing S] (n m : Nat) (c : S) :
    sumIdx (n := n) (m := m) (fun _ => c) = rpow (natCastR n) m * c := by
  unfold sumIdx
  rw [sumList_const, length_idxList, natCastR_pow]

theorem sumIdx_congr {S : Type v} [CommRing S] {n m : Nat} {F G : Idx n m → S}
    (h : ∀ α : Idx n m, F α = G α) : sumIdx F = sumIdx G :=
  sumList_congr (fun α _ => h α)

/-- Constant multi-index `(j, j, ..., j)` of length `m`. -/
def constIdx {n : Nat} (j : Fin n) : (m : Nat) → Idx n m
  | 0 => Idx.nil
  | m + 1 => Idx.cons j (constIdx j m)

/-- Count how many entries of `α : Idx n m` equal `k`. -/
def countVal {n : Nat} (k : Fin n) : {m : Nat} → Idx n m → Nat
  | 0, .nil => 0
  | _ + 1, .cons i t => (if i = k then 1 else 0) + countVal k t

@[simp] theorem countVal_nil {n : Nat} (k : Fin n) : countVal k Idx.nil = 0 := rfl

@[simp] theorem countVal_cons {n m : Nat} (k i : Fin n) (t : Idx n m) :
    countVal k (Idx.cons i t) = (if i = k then 1 else 0) + countVal k t := rfl

theorem countVal_le_ord {n : Nat} (k : Fin n) : ∀ {m : Nat} (α : Idx n m), countVal k α ≤ m
  | 0, .nil => by simp
  | _ + 1, .cons i t => by
    simp only [countVal_cons]
    have ih := countVal_le_ord k t
    by_cases h : i = k <;> simp [h] <;> omega

/-! ### Coordinate Permutations & Symmetric Tensors -/

/-- Coordinate permutation relation on `Idx n m` generated by adjacent transpositions
    (generating the full symmetric group `S_m`). -/
inductive PermIdx {n : Nat} : {m : Nat} → Idx n m → Idx n m → Prop where
  | nil : PermIdx Idx.nil Idx.nil
  | cons (i : Fin n) {t₁ t₂ : Idx n m} : PermIdx t₁ t₂ → PermIdx (Idx.cons i t₁) (Idx.cons i t₂)
  | swap (i j : Fin n) (t : Idx n m) :
      PermIdx (Idx.cons i (Idx.cons j t)) (Idx.cons j (Idx.cons i t))
  | trans {u v w : Idx n m} : PermIdx u v → PermIdx v w → PermIdx u w

/-- A tensor `A : Idx n m → α` is symmetric (`supersymmetric` in Qi 2005) if it is
    invariant under all coordinate permutations of `{1, ..., m}`. -/
def IsSymmetric {n m : Nat} {α : Type u} (A : Idx n m → α) : Prop :=
  ∀ u v : Idx n m, PermIdx u v → A u = A v

theorem permIdx_countVal {n m : Nat} (k : Fin n) {u v : Idx n m} (hp : PermIdx u v) :
    countVal k u = countVal k v := by
  induction hp with
  | nil => rfl
  | cons i _ ih =>
    simp only [countVal_cons, ih]
  | swap i j t =>
    simp only [countVal_cons]
    omega
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

theorem isSymmetric_of_countVal {n m : Nat} {α : Type u} (k : Fin n) (g : Nat → α) :
    IsSymmetric (fun u : Idx n m => g (countVal k u)) := by
  intro u v hp
  dsimp only
  rw [permIdx_countVal k hp]

theorem isSymmetric_scale {S : Type v} [CommRing S] {n m : Nat} (c : S)
    {A : Idx n m → S} (hA : IsSymmetric A) :
    IsSymmetric (fun α => c * A α) := by
  intro u v hp
  dsimp only
  rw [hA u v hp]

/-! ### Index Products, Contraction `A x^{m-1}`, and Homogeneous Form `A x^m` -/

/-- Monomial product `x_{i_1} * ... * x_{i_m}` along `α : Idx n m`. -/
def idxProd {S : Type v} [CommRing S] {n : Nat} (x : Fin n → S) : {m : Nat} → Idx n m → S
  | 0, .nil => 1
  | _ + 1, .cons i t => x i * idxProd x t

@[simp] theorem idxProd_nil {S : Type v} [CommRing S] {n : Nat} (x : Fin n → S) :
    idxProd x Idx.nil = 1 := rfl

@[simp] theorem idxProd_cons {S : Type v} [CommRing S] {n m : Nat}
    (x : Fin n → S) (i : Fin n) (t : Idx n m) :
    idxProd x (Idx.cons i t) = x i * idxProd x t := rfl

theorem idxProd_ones {S : Type v} [CommRing S] {n : Nat} :
    ∀ {m : Nat} (α : Idx n m), idxProd (fun _ : Fin n => (1 : S)) α = 1
  | 0, .nil => rfl
  | _ + 1, .cons _ t => by rw [idxProd_cons, one_mul_eq, idxProd_ones t]

theorem idxProd_constIdx {S : Type v} [CommRing S] {n : Nat} (x : Fin n → S) (j : Fin n) :
    ∀ m : Nat, idxProd x (constIdx j m) = rpow (x j) m
  | 0 => rfl
  | m + 1 => by
    unfold constIdx
    rw [idxProd_cons, idxProd_constIdx x j m, CommRing.mul_comm, ← rpow_succ]

theorem idxProd_mul_vec {S : Type v} [CommRing S] {n : Nat} (x y : Fin n → S) :
    ∀ {m : Nat} (α : Idx n m), idxProd (fun i => x i * y i) α = idxProd x α * idxProd y α
  | 0, .nil => (mul_one_eq 1).symm
  | _ + 1, .cons i t => by
    rw [idxProd_cons, idxProd_cons, idxProd_cons, idxProd_mul_vec x y t]
    calc
      (x i * y i) * (idxProd x t * idxProd y t) =
          x i * (y i * (idxProd x t * idxProd y t)) := CommRing.mul_assoc _ _ _
      _ = x i * (idxProd x t * (y i * idxProd y t)) := by
        rw [mul_left_comm_eq (y i) (idxProd x t)]
      _ = (x i * idxProd x t) * (y i * idxProd y t) := (CommRing.mul_assoc _ _ _).symm

theorem permIdx_idxProd {S : Type v} [CommRing S] {n m : Nat} (x : Fin n → S)
    {u v : Idx n m} (hp : PermIdx u v) : idxProd x u = idxProd x v := by
  induction hp with
  | nil => rfl
  | cons i _ ih =>
    rw [idxProd_cons, idxProd_cons, ih]
  | swap i j t =>
    rw [idxProd_cons, idxProd_cons, idxProd_cons, idxProd_cons,
        mul_left_comm_eq (x i) (x j)]
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

theorem ofReal_idxProd {R : Type v} [CommRing R] {n : Nat} (x : Fin n → R) :
    ∀ {m : Nat} (α : Idx n m),
      ComplexOver.ofReal (idxProd x α) = idxProd (fun i => ComplexOver.ofReal (x i)) α
  | 0, .nil => rfl
  | _ + 1, .cons i t => by
    rw [idxProd_cons, idxProd_cons, ComplexOver.ofReal_mul, ofReal_idxProd x t]

theorem conj_idxProd {R : Type v} [CommRing R] {n : Nat} (z : Fin n → ComplexOver R) :
    ∀ {m : Nat} (α : Idx n m),
      ComplexOver.conj (idxProd z α) = idxProd (fun i => ComplexOver.conj (z i)) α
  | 0, .nil => by
    apply ComplexOver.ext
    · rfl
    · exact neg_zero_eq
  | _ + 1, .cons i t => by
    rw [idxProd_cons, idxProd_cons, ComplexOver.conj_mul, conj_idxProd z t]

theorem normSq_idxProd {R : Type v} [CommRing R] {n : Nat} (z : Fin n → ComplexOver R) :
    ∀ {m : Nat} (α : Idx n m),
      ComplexOver.normSq (idxProd z α) = idxProd (fun i => ComplexOver.normSq (z i)) α
  | 0, .nil => by
    unfold ComplexOver.normSq idxProd
    change 1 * 1 + 0 * 0 = 1
    rw [mul_one_eq, mul_zero_eq, add_zero_eq]
  | _ + 1, .cons i t => by
    rw [idxProd_cons, idxProd_cons, ComplexOver.normSq_mul, normSq_idxProd z t]

theorem absR_idxProd {R : Type v} [OrderedDomain R] {n : Nat} (x : Fin n → R) :
    ∀ {m : Nat} (α : Idx n m), absR (idxProd x α) = idxProd (fun i => absR (x i)) α
  | 0, .nil => absR_of_nonneg zero_ltR_one.1
  | _ + 1, .cons i t => by
    rw [idxProd_cons, idxProd_cons, absR_mul, absR_idxProd x t]

theorem idxProd_nonneg {R : Type v} [OrderedDomain R] {n : Nat} {x : Fin n → R}
    (hx : ∀ i : Fin n, leR 0 (x i)) :
    ∀ {m : Nat} (α : Idx n m), leR 0 (idxProd x α)
  | 0, .nil => zero_ltR_one.1
  | _ + 1, .cons i t => mul_nonneg_leR (hx i) (idxProd_nonneg hx t)

theorem idxProd_leR_rpow_of_leR {R : Type v} [OrderedDomain R] {n : Nat}
    {x : Fin n → R} {M : R} (hx0 : ∀ i : Fin n, leR 0 (x i)) (hxM : ∀ i : Fin n, leR (x i) M) :
    ∀ {m : Nat} (α : Idx n m), leR (idxProd x α) (rpow M m)
  | 0, .nil => leR_refl 1
  | m + 1, .cons i t => by
    rw [idxProd_cons, rpow_succ, CommRing.mul_comm (rpow M m) M]
    exact mul_leR_mul_nonneg (hx0 i) (idxProd_nonneg hx0 t) (hxM i)
      (idxProd_leR_rpow_of_leR hx0 hxM t)

/-- Multinomial expansion identity: `∑_{α ∈ Idx n m} x_{α_1} ⋯ x_{α_m} = (∑_i x_i)^m`. -/
theorem sumIdx_idxProd {S : Type v} [CommRing S] {n : Nat} (x : Fin n → S) :
    ∀ m : Nat, sumIdx (fun α : Idx n m => idxProd x α) = rpow (sumFin x) m
  | 0 => sumIdx_zero_ord _
  | m + 1 => by
    rw [sumIdx_succ_ord]
    simp only [idxProd_cons]
    have hpull : sumFin (fun i => sumIdx (fun t : Idx n m => x i * idxProd x t)) =
        sumFin (fun i => x i * rpow (sumFin x) m) := by
      apply sumFin_congr
      intro i
      unfold sumIdx
      rw [sumList_mul_left, ← sumIdx, sumIdx_idxProd x m]
    rw [hpull, sumFin_mul_right, CommRing.mul_comm, ← rpow_succ]

/-- `(A x^d)_i = ∑_{t ∈ Idx n d} A(i, t) * x_{t_1} ⋯ x_{t_d}` for an order-`(d+1)` tensor `A`. -/
def contract {S : Type v} [CommRing S] {n d : Nat}
    (A : Idx n (d + 1) → S) (x : Fin n → S) (i : Fin n) : S :=
  sumIdx (fun t : Idx n d => A (Idx.cons i t) * idxProd x t)

/-- Homogeneous polynomial form `A x^m = ∑_{α ∈ Idx n m} A(α) * x_{α_1} ⋯ x_{α_m}`. -/
def homForm {S : Type v} [CommRing S] {n m : Nat}
    (A : Idx n m → S) (x : Fin n → S) : S :=
  sumIdx (fun α : Idx n m => A α * idxProd x α)

/-- Euler contraction identity: `A x^{d+1} = ∑_{i=1}^n x_i * (A x^d)_i`. -/
theorem homForm_eq_sumFin_contract {S : Type v} [CommRing S] {n d : Nat}
    (A : Idx n (d + 1) → S) (x : Fin n → S) :
    homForm A x = sumFin (fun i => x i * contract A x i) := by
  unfold homForm contract
  rw [sumIdx_succ_ord]
  apply sumFin_congr
  intro i
  unfold sumIdx
  rw [← sumList_mul_left]
  apply sumList_congr
  intro t _
  rw [idxProd_cons, mul_left_comm_eq (x i) (A (Idx.cons i t))]

theorem ofReal_contract {R : Type v} [CommRing R] {n d : Nat}
    (A : Idx n (d + 1) → R) (x : Fin n → R) (i : Fin n) :
    ComplexOver.ofReal (contract A x i) =
      contract (fun α => ComplexOver.ofReal (A α)) (fun j => ComplexOver.ofReal (x j)) i := by
  unfold contract sumIdx
  rw [ofReal_sumList]
  apply sumList_congr
  intro t _
  rw [ComplexOver.ofReal_mul, ofReal_idxProd]

/-! ### Standard Symmetric Tensor Constructions -/

/-- Symmetric rank-`1` tensor `c * u^{⊗ m}` with entries `c * u_{α_1} ⋯ u_{α_m}`. -/
def rankOneTensor {S : Type v} [CommRing S] {n m : Nat} (c : S) (u : Fin n → S) : Idx n m → S :=
  fun α => c * idxProd u α

theorem isSymmetric_rankOneTensor {S : Type v} [CommRing S] {n m : Nat} (c : S) (u : Fin n → S) :
    IsSymmetric (rankOneTensor (m := m) c u) := by
  intro α β hp
  unfold rankOneTensor
  rw [permIdx_idxProd u hp]

theorem contract_rankOneTensor {S : Type v} [CommRing S] {n d : Nat}
    (c : S) (u x : Fin n → S) (i : Fin n) :
    contract (rankOneTensor (m := d + 1) c u) x i =
      (c * u i) * rpow (sumFin (fun j => u j * x j)) d := by
  unfold contract rankOneTensor
  have hcongr : sumIdx (fun t : Idx n d => (c * (u i * idxProd u t)) * idxProd x t) =
      (c * u i) * sumIdx (fun t : Idx n d => idxProd (fun j => u j * x j) t) := by
    unfold sumIdx
    rw [← sumList_mul_left]
    apply sumList_congr
    intro t _
    rw [idxProd_mul_vec, ← CommRing.mul_assoc c (u i), CommRing.mul_assoc (c * u i)]
  change sumIdx (fun t : Idx n d => (c * (u i * idxProd u t)) * idxProd x t) = _
  rw [hcongr, sumIdx_idxProd]

/-- All-ones uniform symmetric tensor `J_{m, n}` (`a_{i_1...i_m} = 1`), whose homogeneous
    polynomial is `(x_1 + ... + x_n)^m`. -/
def allOnesTensor {S : Type v} [CommRing S] (n m : Nat) : Idx n m → S :=
  fun _ => 1

theorem isSymmetric_allOnesTensor {S : Type v} [CommRing S] (n m : Nat) :
    IsSymmetric (allOnesTensor n m : Idx n m → S) :=
  fun _ _ _ => rfl

theorem contract_allOnesTensor {S : Type v} [CommRing S] {n d : Nat}
    (x : Fin n → S) (i : Fin n) :
    contract (allOnesTensor n (d + 1)) x i = rpow (sumFin x) d := by
  unfold contract allOnesTensor
  have hc : sumIdx (fun t : Idx n d => (1 : S) * idxProd x t) =
      sumIdx (fun t : Idx n d => idxProd x t) := by
    apply sumIdx_congr; intro t; exact one_mul_eq _
  rw [hc, sumIdx_idxProd]

/-- Coordinate monomial tensor `e_k^{⊗ m}` (`F(x) = x_k^m`, single nonzero entry `a_{k...k} = 1`). -/
def stdBasisVec {S : Type v} [CommRing S] {n : Nat} (k : Fin n) : Fin n → S :=
  fun j => if j = k then 1 else 0

def monomialTensor {S : Type v} [CommRing S] {n : Nat} (m : Nat) (k : Fin n) : Idx n m → S :=
  rankOneTensor 1 (stdBasisVec k)

theorem isSymmetric_monomialTensor {S : Type v} [CommRing S] {n : Nat} (m : Nat) (k : Fin n) :
    IsSymmetric (monomialTensor m k : Idx n m → S) :=
  isSymmetric_rankOneTensor 1 (stdBasisVec k)

theorem sumFin_stdBasis_mul {S : Type v} [CommRing S] {n : Nat} (k : Fin n) (x : Fin n → S) :
    sumFin (fun j => stdBasisVec (S := S) k j * x j) = x k := by
  suffices ∀ (m : Nat) (k' : Fin m) (y : Fin m → S),
      sumList (finList m) (fun j => (if j = k' then (1 : S) else 0) * y j) = y k' from
    this n k x
  intro m
  induction m with
  | zero => intro ⟨_, h⟩ _; omega
  | succ m ih =>
    intro ⟨v, hv⟩ y
    cases v with
    | zero =>
      simp only [finList, sumList_cons]
      rw [sumList_map]
      have htail : sumList (finList m)
          (fun a : Fin m => (if Fin.succ a = ⟨0, hv⟩ then (1 : S) else 0) * y (Fin.succ a)) = 0 := by
        calc
          _ = sumList (finList m) (fun _ => (0 : S)) := by
            apply sumList_congr; intro a _
            have hne : Fin.succ a ≠ ⟨0, hv⟩ := by
              intro heq
              have hval : a.val + 1 = 0 := congrArg Fin.val heq
              omega
            rw [if_neg hne, zero_mul_eq]
          _ = 0 := sumList_zero _
      rw [ite_true, one_mul_eq, htail, add_zero_eq]
    | succ v' =>
      simp only [finList, sumList_cons]
      rw [sumList_map]
      have hne0 : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ ⟨v' + 1, hv⟩ := by
        intro heq
        have hval : 0 = v' + 1 := congrArg Fin.val heq
        omega
      have hcongr : sumList (finList m)
          (fun a : Fin m => (if Fin.succ a = ⟨v' + 1, hv⟩ then (1 : S) else 0) * y (Fin.succ a)) =
          sumList (finList m)
          (fun a : Fin m => (if a = ⟨v', by omega⟩ then (1 : S) else 0) * y (Fin.succ a)) := by
        apply sumList_congr; intro a _
        by_cases ha : a = ⟨v', by omega⟩
        · subst ha
          have hseq : Fin.succ (⟨v', by omega⟩ : Fin m) = ⟨v' + 1, hv⟩ := rfl
          rw [if_pos hseq, if_pos rfl]
        · have hne : Fin.succ a ≠ ⟨v' + 1, hv⟩ := by
            intro heq
            have hval : a.val + 1 = v' + 1 := congrArg Fin.val heq
            have ha_eq : a = ⟨v', by omega⟩ := Fin.ext (by change a.val = v'; omega)
            exact ha ha_eq
          rw [if_neg hne, if_neg ha]
      rw [if_neg hne0, zero_mul_eq, zero_add_eq, hcongr,
          ih ⟨v', by omega⟩ (fun a => y (Fin.succ a))]
      rfl

theorem contract_monomialTensor {S : Type v} [CommRing S] {n d : Nat}
    (k : Fin n) (x : Fin n → S) (i : Fin n) :
    contract (monomialTensor (d + 1) k) x i =
      (if i = k then (1 : S) else 0) * rpow (x k) d := by
  unfold monomialTensor
  rw [contract_rankOneTensor, one_mul_eq, sumFin_stdBasis_mul]
  rfl

/-- Literal binary "binomial-entry" symmetric tensor `B_{m, 2}` on `Fin 2`, where
    `a_{i_1...i_m} = C(m, #{r : i_r = 1})`. -/
def binomialEntryTensor {S : Type v} [CommRing S] (m : Nat) : Idx 2 m → S :=
  fun α => natCastR (binom m (countVal ⟨1, by omega⟩ α))

theorem isSymmetric_binomialEntryTensor {S : Type v} [CommRing S] (m : Nat) :
    IsSymmetric (binomialEntryTensor m : Idx 2 m → S) :=
  isSymmetric_of_countVal ⟨1, by omega⟩ (fun k => natCastR (binom m k))

/-- Orbit-grouped summation identity on `Idx 2 d`: for any `g : Nat → Nat`,
    `∑_{t ∈ Idx 2 d} natCastR (g (countVal 1 t)) = natCastR (∑_{k=0}^d C(d, k) * g(k))`. -/
theorem sumIdx_fin2_countVal {S : Type v} [CommRing S] :
    ∀ (d : Nat) (g : Nat → Nat),
      sumIdx (n := 2) (m := d) (fun t => (natCastR (g (countVal ⟨1, by omega⟩ t)) : S)) =
        natCastR (natSumRange (d + 1) (fun k => binom d k * g k))
  | 0, g => by
    rw [sumIdx_zero_ord, countVal_nil]
    change natCastR (g 0) = natCastR (0 + binom 0 0 * g 0)
    rw [Nat.zero_add, binom_zero_zero, Nat.one_mul]
  | d + 1, g => by
    rw [sumIdx_succ_ord, sumFin_two]
    have h0 : sumIdx (n := 2) (m := d)
        (fun t => (natCastR (g (countVal ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ t))) : S)) =
        natCastR (natSumRange (d + 1) (fun k => binom d k * g k)) := by
      have hc : (fun t : Idx 2 d => (natCastR (g (countVal ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ t))) : S)) =
          (fun t : Idx 2 d => (natCastR (g (countVal ⟨1, by omega⟩ t)) : S)) := by
        funext t
        rw [countVal_cons]
        have hne : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := by decide
        rw [if_neg hne, Nat.zero_add]
      rw [hc, sumIdx_fin2_countVal d g]
    have h1 : sumIdx (n := 2) (m := d)
        (fun t => (natCastR (g (countVal ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ t))) : S)) =
        natCastR (natSumRange (d + 1) (fun k => binom d k * g (k + 1))) := by
      have hc : (fun t : Idx 2 d => (natCastR (g (countVal ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ t))) : S)) =
          (fun t : Idx 2 d => (natCastR (g (countVal ⟨1, by omega⟩ t + 1)) : S)) := by
        funext t
        rw [countVal_cons, if_pos rfl, Nat.add_comm]
      rw [hc, sumIdx_fin2_countVal d (fun k => g (k + 1))]
    rw [h0, h1, ← natCastR_add]
    congr 1
    rw [natSumRange_succ_shift (d + 1)]
    simp only [binom_succ_zero, Nat.one_mul, binom_succ_succ, Nat.right_distrib]
    rw [natSumRange_add]
    have htop : natSumRange (d + 1) (fun k => binom d k * g k) =
        g 0 + natSumRange d (fun j => binom d (j + 1) * g (j + 1)) := by
      have hs := natSumRange_succ_shift d (fun k => binom d k * g k)
      rw [binom_zero_right, Nat.one_mul] at hs
      exact hs
    have hlast : natSumRange (d + 1) (fun j => binom d (j + 1) * g (j + 1)) =
        natSumRange d (fun j => binom d (j + 1) * g (j + 1)) := by
      change natSumRange d (fun j => binom d (j + 1) * g (j + 1)) +
             binom d (d + 1) * g (d + 1) = _
      rw [binom_eq_zero_of_lt (by omega), Nat.zero_mul, Nat.add_zero]
    rw [hlast, htop]
    omega

/-- Exact contraction of the binomial-entry tensor `B_{d+1, 2}` at `x = (1, 1)`:
    both coordinates equal the Vandermonde central binomial `C(2d + 1, d) = C(2m - 1, m - 1)`. -/
theorem contract_binomialEntryTensor_ones {S : Type v} [CommRing S] (d : Nat) (i : Fin 2) :
    contract (binomialEntryTensor (S := S) (d + 1)) (fun _ => 1) i =
      natCastR (binom (2 * d + 1) d) := by
  unfold contract binomialEntryTensor
  have hc : sumIdx (fun t : Idx 2 d =>
      (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons i t))) : S) *
      idxProd (fun _ => (1 : S)) t) =
      sumIdx (fun t : Idx 2 d =>
        (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons i t))) : S)) := by
    apply sumIdx_congr; intro t
    rw [idxProd_ones, mul_one_eq]
  rw [hc]
  match i with
  | ⟨0, _⟩ =>
    have h0 : (fun t : Idx 2 d =>
        (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ t))) : S)) =
        (fun t : Idx 2 d => (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ t)) : S)) := by
      funext t
      rw [countVal_cons]
      have hne : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, by omega⟩ := by decide
      rw [if_neg hne, Nat.zero_add]
    change sumIdx (fun t : Idx 2 d =>
      (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons ⟨0, by omega⟩ t))) : S)) = _
    rw [h0, sumIdx_fin2_countVal d (fun k => binom (d + 1) k), vandermonde_binom_row1]
  | ⟨1, _⟩ =>
    have h1 : (fun t : Idx 2 d =>
        (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ t))) : S)) =
        (fun t : Idx 2 d => (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ t + 1)) : S)) := by
      funext t
      rw [countVal_cons, if_pos rfl, Nat.add_comm 1 (countVal ⟨1, by omega⟩ t)]
    change sumIdx (fun t : Idx 2 d =>
      (natCastR (binom (d + 1) (countVal ⟨1, by omega⟩ (Idx.cons ⟨1, by omega⟩ t))) : S)) = _
    rw [h1, sumIdx_fin2_countVal d (fun k => binom (d + 1) (k + 1)), vandermonde_binom_row2]
  | ⟨_ + 2, hk⟩ => omega

/-! ### Eigenpair Predicates & Tensor Norms (Qi 2005, Lim 2005, Banach 1938) -/

/-- `x` has at least one nonzero coordinate. -/
def IsNonzeroVec {S : Type v} [CommRing S] {n : Nat} (x : Fin n → S) : Prop :=
  ∃ i : Fin n, x i ≠ 0

/-- Qi's (2005) `H`-eigenpair (over `R`) / complex eigenpair (over `ComplexOver R`):
    `x ≠ 0` and `(A x^{m-1})_i = λ x_i^{m-1}` for all `i = 1, ..., n` (`m = d + 1`). -/
def IsHEigenpair {S : Type v} [CommRing S] {n d : Nat}
    (A : Idx n (d + 1) → S) (x : Fin n → S) (lam : S) : Prop :=
  IsNonzeroVec x ∧ ∀ i : Fin n, contract A x i = lam * rpow (x i) d

/-- Qi's (2005) `Z`-eigenpair (when `S = R`, `∑ x_i^2 = 1`) and `E`-eigenpair
    (when `S = ComplexOver R`, `x^T x = ∑ x_i^2 = 1` in `R[i]`):
    `∑_{i=1}^n x_i^2 = 1` and `(A x^{m-1})_i = λ x_i` for all `i = 1, ..., n`. -/
def IsZEigenpair {S : Type v} [CommRing S] {n d : Nat}
    (A : Idx n (d + 1) → S) (x : Fin n → S) (lam : S) : Prop :=
  sumFin (fun i => x i * x i) = 1 ∧ ∀ i : Fin n, contract A x i = lam * x i

/-- Complex `E`-eigenpair of a real/rational tensor `A : Idx n (d + 1) → R`:
    `x : Fin n → ComplexOver R` satisfies `∑ x_i^2 = 1` in `R[i]` and `A x^{m-1} = λ x`. -/
def IsComplexEEigenpair {R : Type v} [CommRing R] {n d : Nat}
    (A : Idx n (d + 1) → R) (x : Fin n → ComplexOver R) (lam : ComplexOver R) : Prop :=
  IsZEigenpair (fun α => ComplexOver.ofReal (A α)) x lam

/-- Entrywise absolute bound `|A(α)| ≤ B` for real/ordered-domain tensors. -/
def EntryBoundedAbs {R : Type v} [OrderedDomain R] {n m : Nat}
    (A : Idx n m → R) (B : R) : Prop :=
  ∀ α : Idx n m, leR (absR (A α)) B

/-- Entrywise modulus-squared bound `|A(α)|^2 ≤ B^2` for complex tensors. -/
def EntryBoundedNormSq {R : Type v} [OrderedDomain R] {n m : Nat}
    (A : Idx n m → ComplexOver R) (B : R) : Prop :=
  ∀ α : Idx n m, leR (ComplexOver.normSq (A α)) (B * B)

/-- Squared Frobenius (Hilbert-Schmidt) norm `‖A‖_F^2 = ∑_α A(α)^2`. -/
def frobNormSq {R : Type v} [CommRing R] {n m : Nat} (A : Idx n m → R) : R :=
  sumIdx (fun α => A α * A α)

/-- Entrywise `ℓ_1` norm `‖A‖_1 = ∑_α |A(α)|`. -/
noncomputable def l1Norm {R : Type v} [OrderedDomain R] {n m : Nat} (A : Idx n m → R) : R :=
  sumIdx (fun α => absR (A α))

theorem zEigenpair_homForm_eq {S : Type v} [CommRing S] {n d : Nat}
    {A : Idx n (d + 1) → S} {x : Fin n → S} {lam : S}
    (hz : IsZEigenpair A x lam) : homForm A x = lam := by
  rw [homForm_eq_sumFin_contract]
  have hc : sumFin (fun i => x i * contract A x i) =
      lam * sumFin (fun i => x i * x i) := by
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro i
    rw [hz.2 i, mul_left_comm_eq (x i) lam (x i)]
  rw [hc, hz.1, mul_one_eq]

end Conjecture00000007176
