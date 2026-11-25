/-
  Conjecture 00000008552 — Complete Formal Disproof in Core Lean 4.19.0
  =====================================================================

  Official statement (`SOURCE.md`):
    English:
      Definition: Order polynomials count order-preserving maps.
      Conjecture: The number of order-preserving maps of a chain product lattice is
      an explicit product of multinomial coefficients; the product is of MacMahon type.
      (order-preserving map counting)
    Chinese:
      定义：有序多项式指保序映射的计数。
      猜想：链积格的保序映射个数为显式多项式系数积；该积为 MacMahon 型。（保序映射计数）

  Summary of formal results established in this file (Core Lean 4, zero external
  dependencies, zero `sorry`, zero `native_decide`, zero custom axioms):
    1. Posets, lattices, finite chains `C_m`, general chain product lattices
       `chainProdLattice dims = C_{a_1} × ⋯ × C_{a_d}`, order-preserving maps `OrderHom`,
       bijection-based exact cardinality `HasCard`, cardinality uniqueness `HasCard.unique`,
       universal product decomposition `orderHomProdEquiv`, and chain-codomain swap
       duality `orderHomChainSwapEquiv`.
    2. Binomial/multinomial coefficients (`multinomial_spec : multinomial ks * prodFact ks
       = fact (listSum ks)`) and the nested hierarchy of MacMahon / multinomial polynomial
       formulas:
         `IsPureMultinomialPolyProd`
           ⊆ `IsMacMahonMultinomialQuotient`
           ⊆ `IsRationalLinearRatio`.
    3. Positive Non-Vacuity Witnesses (1-chain and 2-chain MacMahon theorems):
       - `C_2`: `omegaChain2 m = binom (m + 1) 2` satisfies `IsPureMultinomialPolyProd`.
       - `C_2 × C_2`: `HasCard (OrderHom (C_2 × C_2) C_m) (omegaSq m)` for all `m`,
         with `12 * omegaSq m = m * (m + 1)^2 * (m + 2)` and MacMahon's identity
         `omegaSq m * (binom 2 2 * binom 3 2) = binom (m + 1) 2 * binom (m + 2) 2`,
         satisfying `IsMacMahonMultinomialQuotient` and `IsRationalLinearRatio`.
    4. Exact Order Polynomial of the 3-Chain Cube Lattice `C_2 × C_2 × C_2` for ALL `m`:
       - `HasCard (OrderHom (C_2 × C_2 × C_2) C_m) (omegaCube m)` for every `m : Nat`,
         where `1680 * omegaCube m = m(m+1)(m+2)(m+3)(2m^4 + 12m^3 + 25m^2 + 21m + 10)`.
       - Sum-of-squares positivity of the homogenized quartic factor:
         `8 * Q_hom(g, z) = (4z^2 + 12gz + 7g^2)^2 + 31g^4 ≥ 31 > 0` for all `g ≠ 0`.
       - Universal polynomial disproof (`conjecture_00000008552_order_polynomial_disproved`):
         `omegaCube` (and any function counting `OrderHom (C_2 × C_2 × C_2) C_m`) fails
         `IsRationalLinearRatio`, `IsMacMahonMultinomialQuotient`, and
         `IsPureMultinomialPolyProd`.
    5. Pointwise Prime-Factor, Naive-Box, and Endomorphism Disproofs:
       - `|OrderHom (C_2 × C_2 × C_2) C_4| = 887` is prime (`isPrime_887`), hence is
         neither a nontrivial integer product, nor any finite product of genuine
         (non-edge) multinomial coefficients (`no_genuine_multinomial_prod_eq_887`),
         nor any quotient of multinomial products with top entries `< 887`.
       - The naive d-dimensional MacMahon rank-box formula fails already on `C_2^3` at
         `m = 3` and on `C_2^4` at `m = 2` (`500 / 3 ≠ 168`).
       - `|OrderHom (C_2 × C_2 × C_3) (C_2 × C_2 × C_3)| = 2,217,500 = 2^2 · 5^4 · 887`
         (`orderEnd_223_card`), refuting bounded multinomial / MacMahon products for
         order-preserving endomorphisms of a 12-element chain product lattice.
-/

namespace Conjecture00000008552

/-! ## Section 1: Constructive Equivalences and Exact Finite Cardinalities -/

/-- Constructive bijection between two types. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun     : α → β
  invFun    : β → α
  left_inv  : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace Equiv

def refl (α : Type u) : Equiv α α where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

def symm {α : Type u} {β : Type v} (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

def trans {α : Type u} {β : Type v} {γ : Type w}
    (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]

def prodCongr {α₁ β₁ α₂ β₂ : Type} (e₁ : Equiv α₁ β₁) (e₂ : Equiv α₂ β₂) :
    Equiv (α₁ × α₂) (β₁ × β₂) where
  toFun p := (e₁.toFun p.1, e₂.toFun p.2)
  invFun q := (e₁.invFun q.1, e₂.invFun q.2)
  left_inv p := by cases p; simp [e₁.left_inv, e₂.left_inv]
  right_inv q := by cases q; simp [e₁.right_inv, e₂.right_inv]

def finCast {a b : Nat} (h : a = b) : Equiv (Fin a) (Fin b) where
  toFun k := ⟨k.val, h ▸ k.isLt⟩
  invFun k := ⟨k.val, h.symm ▸ k.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv

/-- `HasCard α n` asserts that `α` is in constructive bijection with `Fin n`. -/
def HasCard (α : Type) (n : Nat) : Prop := Nonempty (Equiv α (Fin n))

/-- Helper shifting an injection `Fin (m + 1) → Fin (n' + 1)` to `Fin m → Fin n'`. -/
def restrictInj (m n' : Nat) (f : Fin (m + 1) → Fin (n' + 1))
    (hf : ∀ i j, f i = f j → i = j) (i : Fin m) : Fin n' :=
  let i' : Fin (m + 1) := ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩
  let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  if hlt : (f i').val < n' then
    ⟨(f i').val, hlt⟩
  else
    have hne : (f i').val ≠ (f top).val := fun hv => by
      have heq := hf i' top (Fin.ext hv)
      have hval : i'.val = top.val := congrArg Fin.val heq
      have hi_eq : i'.val = i.val := rfl
      have ht_eq : top.val = m := rfl
      have hilt := i.isLt
      omega
    have hfi_lt := (f i').isLt
    have hft_lt := (f top).isLt
    ⟨(f top).val, by omega⟩

theorem restrictInj_injective (m n' : Nat) (f : Fin (m + 1) → Fin (n' + 1))
    (hf : ∀ i j, f i = f j → i = j) :
    ∀ i j : Fin m, restrictInj m n' f hf i = restrictInj m n' f hf j → i = j := by
  intro i j hij
  let i' : Fin (m + 1) := ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩
  let j' : Fin (m + 1) := ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩
  let top : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hi_val : i'.val = i.val := rfl
  have hj_val : j'.val = j.val := rfl
  have ht_val : top.val = m := rfl
  have hij_val : (restrictInj m n' f hf i).val = (restrictInj m n' f hf j).val :=
    congrArg Fin.val hij
  dsimp only [restrictInj] at hij_val
  by_cases hi : (f i').val < n' <;> by_cases hj : (f j').val < n'
  · rw [dif_pos hi, dif_pos hj] at hij_val
    have heq := hf i' j' (Fin.ext hij_val)
    have hv : i'.val = j'.val := congrArg Fin.val heq
    exact Fin.ext (by omega)
  · rw [dif_pos hi, dif_neg hj] at hij_val
    have heq := hf i' top (Fin.ext hij_val)
    have hv : i'.val = top.val := congrArg Fin.val heq
    have := i.isLt
    omega
  · rw [dif_neg hi, dif_pos hj] at hij_val
    have heq := hf top j' (Fin.ext hij_val)
    have hv : top.val = j'.val := congrArg Fin.val heq
    have := j.isLt
    omega
  · have h1 := (f i').isLt
    have h2 := (f j').isLt
    have heq := hf i' j' (Fin.ext (by omega))
    have hv : i'.val = j'.val := congrArg Fin.val heq
    exact Fin.ext (by omega)

/-- Pigeonhole injection bound on `Fin`: an injection `Fin m → Fin n` forces `m ≤ n`. -/
theorem fin_inj_le : ∀ (m n : Nat) (f : Fin m → Fin n),
    (∀ i j, f i = f j → i = j) → m ≤ n
  | 0, _, _, _ => Nat.zero_le _
  | m + 1, 0, f, _ => Fin.elim0 (f ⟨m, Nat.lt_succ_self m⟩)
  | m + 1, n' + 1, f, hf =>
      Nat.succ_le_succ (fin_inj_le m n' (restrictInj m n' f hf) (restrictInj_injective m n' f hf))

/-- Exact cardinality is uniquely determined up to equality. -/
theorem HasCard.unique {α : Type} {m n : Nat} (hm : HasCard α m) (hn : HasCard α n) :
    m = n := by
  rcases hm with ⟨em⟩
  rcases hn with ⟨en⟩
  let e := em.symm.trans en
  have h1 : m ≤ n := fin_inj_le m n e.toFun (fun i j hij => by
    have := congrArg e.invFun hij
    simpa [e.left_inv] using this)
  have h2 : n ≤ m := fin_inj_le n m e.invFun (fun i j hij => by
    have := congrArg e.toFun hij
    simpa [e.right_inv] using this)
  omega

theorem HasCard.ofEquiv {α β : Type} {n : Nat} (e : Equiv α β) (h : HasCard β n) :
    HasCard α n := by
  rcases h with ⟨eb⟩
  exact ⟨e.trans eb⟩

/-- Disjoint union bijection `Fin a ⊕ Fin b ≃ Fin (a + b)`. -/
def finAddEquiv (a b : Nat) : Equiv (Sum (Fin a) (Fin b)) (Fin (a + b)) where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr j => ⟨a + j.val, by omega⟩
  invFun k :=
    if h : k.val < a then .inl ⟨k.val, h⟩
    else .inr ⟨k.val - a, by omega⟩
  left_inv x := by
    cases x with
    | inl i => simp [i.isLt]
    | inr j =>
      have h : ¬ (a + j.val < a) := by omega
      simp only [h, ↓reduceDIte]
      exact congrArg Sum.inr (Fin.ext (by dsimp only []; omega))
  right_inv k := by
    by_cases h : k.val < a
    · simp [h]
    · simp only [h, ↓reduceDIte]
      apply Fin.ext
      dsimp only []
      omega

/-- Sum of `f 0 + f 1 + ⋯ + f (n - 1)` on plain `Nat` indices. -/
def natSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => natSum n f + f n

/-- Splitting `(i : Fin (n + 1)) × Fin (w i.val)` into initial `n` fibers plus last fiber. -/
def sigmaSplitSucc (n : Nat) (w : Nat → Nat) :
    Equiv ((i : Fin (n + 1)) × Fin (w i.val))
          (Sum ((i : Fin n) × Fin (w i.val)) (Fin (w n))) where
  toFun := fun ⟨i, x⟩ =>
    if h : i.val < n then
      .inl ⟨⟨i.val, h⟩, x⟩
    else
      have hi : i.val = n := by omega
      .inr (Equiv.finCast (congrArg w hi) |>.toFun x)
  invFun := fun s =>
    match s with
    | .inl ⟨i, x⟩ => ⟨⟨i.val, by omega⟩, x⟩
    | .inr x => ⟨⟨n, by omega⟩, x⟩
  left_inv := fun ⟨⟨iv, ilt⟩, x⟩ => by
    by_cases h : iv < n
    · simp [h]
    · simp only [h, ↓reduceDIte]
      have hiv : n = iv := by omega
      cases hiv
      rfl
  right_inv := fun s => by
    cases s with
    | inl p =>
      rcases p with ⟨i, x⟩
      simp [i.isLt]
    | inr x =>
      simp [Nat.lt_irrefl, Equiv.finCast]

/-- Dependent sum bijection `(i : Fin n) × Fin (w i.val) ≃ Fin (natSum n w)`. -/
def sigmaNatFinEquiv : (n : Nat) → (w : Nat → Nat) →
    Equiv ((i : Fin n) × Fin (w i.val)) (Fin (natSum n w))
  | 0, _ =>
    { toFun := fun p => Fin.elim0 p.1
      invFun := fun k => Fin.elim0 k
      left_inv := fun p => Fin.elim0 p.1
      right_inv := fun k => Fin.elim0 k }
  | n + 1, w =>
    let ih := sigmaNatFinEquiv n w
    let sumStep : Equiv (Sum ((i : Fin n) × Fin (w i.val)) (Fin (w n)))
                        (Sum (Fin (natSum n w)) (Fin (w n))) :=
      { toFun := fun s => match s with | .inl p => .inl (ih.toFun p) | .inr x => .inr x
        invFun := fun s => match s with | .inl k => .inl (ih.invFun k) | .inr x => .inr x
        left_inv := fun s => by cases s <;> simp [ih.left_inv]
        right_inv := fun s => by cases s <;> simp [ih.right_inv] }
    (sigmaSplitSucc n w).trans (sumStep.trans (finAddEquiv (natSum n w) (w n)))

theorem natSum_const (a b : Nat) : natSum a (fun _ => b) = a * b := by
  induction a with
  | zero => simp [natSum]
  | succ a ih => simp [natSum, ih, Nat.succ_mul]

/-- Product bijection `Fin a × Fin b ≃ Fin (a * b)`. -/
def prodFinEquiv (a b : Nat) : Equiv (Fin a × Fin b) (Fin (a * b)) :=
  let e1 : Equiv (Fin a × Fin b) ((i : Fin a) × Fin ((fun _ => b) i.val)) :=
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.1, p.2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  e1.trans ((sigmaNatFinEquiv a (fun _ => b)).trans (Equiv.finCast (natSum_const a b)))

theorem HasCard.prod {α β : Type} {a b : Nat} (ha : HasCard α a) (hb : HasCard β b) :
    HasCard (α × β) (a * b) := by
  rcases ha with ⟨ea⟩
  rcases hb with ⟨eb⟩
  exact ⟨(Equiv.prodCongr ea eb).trans (prodFinEquiv a b)⟩

/-- Dependent pair witnessing `b = true` together with a value in `α`. -/
structure BoolFiber (b : Bool) (α : Type) where
  h   : b = true
  val : α

/-- Conditional fiber bijection `BoolFiber b α ≃ Fin (if b then k else 0)`. -/
def boolFiberEquiv (b : Bool) {α : Type} {k : Nat} (e : b = true → Equiv α (Fin k)) :
    Equiv (BoolFiber b α) (Fin (if b then k else 0)) :=
  match b with
  | true =>
    { toFun := fun x => (e rfl).toFun x.val
      invFun := fun y => ⟨rfl, (e rfl).invFun y⟩
      left_inv := fun ⟨_, v⟩ => by simp [(e rfl).left_inv]
      right_inv := fun y => (e rfl).right_inv y }
  | false =>
    { toFun := fun x => Bool.noConfusion x.h
      invFun := fun y => Fin.elim0 y
      left_inv := fun x => Bool.noConfusion x.h
      right_inv := fun y => Fin.elim0 y }

/-- Boolean implication `(!a) || b`. -/
def bImp (a b : Bool) : Bool := (!a) || b

theorem bImp_true {a b : Bool} (h : a = true → b = true) : bImp a b = true := by
  cases a <;> cases b <;> first | rfl | exact False.elim (Bool.noConfusion (h rfl))

theorem natCast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) :=
  Int.ofNat_add a b

theorem natCast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) :=
  Int.ofNat_mul a b

/-! ## Section 2: Posets, Chain Product Lattices, and Order-Preserving Maps -/

/-- Partially ordered set. -/
structure Poset where
  Carrier     : Type
  le          : Carrier → Carrier → Prop
  le_refl     : ∀ x, le x x
  le_trans    : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y

/-- Lattice as a poset equipped with greatest lower bounds (`inf`) and least upper bounds (`sup`). -/
structure LatticePoset extends Poset where
  inf          : Carrier → Carrier → Carrier
  sup          : Carrier → Carrier → Carrier
  inf_le_left  : ∀ x y, le (inf x y) x
  inf_le_right : ∀ x y, le (inf x y) y
  le_inf       : ∀ {z x y}, le z x → le z y → le z (inf x y)
  le_sup_left  : ∀ x y, le x (sup x y)
  le_sup_right : ∀ x y, le y (sup x y)
  sup_le       : ∀ {x y z}, le x z → le y z → le (sup x y) z

/-- The `m`-element chain lattice `C_m = {0 < 1 < ⋯ < m - 1}`. -/
def chainLattice (m : Nat) : LatticePoset where
  Carrier      := Fin m
  le x y       := x.val ≤ y.val
  le_refl _    := Nat.le_refl _
  le_trans h1 h2 := Nat.le_trans h1 h2
  le_antisymm h1 h2 := Fin.ext (Nat.le_antisymm h1 h2)
  inf x y      := if x.val ≤ y.val then x else y
  sup x y      := if x.val ≤ y.val then y else x
  inf_le_left x y := by by_cases h : x.val ≤ y.val <;> simp [h] <;> omega
  inf_le_right x y := by by_cases h : x.val ≤ y.val <;> simp [h]
  le_inf {z x y} h1 h2 := by by_cases h : x.val ≤ y.val <;> simp [h, h1, h2]
  le_sup_left x y := by by_cases h : x.val ≤ y.val <;> simp [h]
  le_sup_right x y := by by_cases h : x.val ≤ y.val <;> simp [h] <;> omega
  sup_le {x y z} h1 h2 := by by_cases h : x.val ≤ y.val <;> simp [h, h1, h2]

/-- Direct product of finite chains `C_{a_1} × ⋯ × C_{a_d}` indexed by `dims : List Nat`. -/
inductive ChainProd : List Nat → Type where
  | nil  : ChainProd []
  | cons : {a : Nat} → {as : List Nat} → Fin a → ChainProd as → ChainProd (a :: as)

namespace ChainProd

def le : {dims : List Nat} → ChainProd dims → ChainProd dims → Prop
  | [], .nil, .nil => True
  | _ :: _, .cons x xs, .cons y ys => x.val ≤ y.val ∧ le xs ys

def inf : {dims : List Nat} → ChainProd dims → ChainProd dims → ChainProd dims
  | [], .nil, .nil => .nil
  | _ :: _, .cons x xs, .cons y ys =>
      .cons (if x.val ≤ y.val then x else y) (inf xs ys)

def sup : {dims : List Nat} → ChainProd dims → ChainProd dims → ChainProd dims
  | [], .nil, .nil => .nil
  | _ :: _, .cons x xs, .cons y ys =>
      .cons (if x.val ≤ y.val then y else x) (sup xs ys)

theorem le_refl : {dims : List Nat} → (u : ChainProd dims) → le u u
  | [], .nil => trivial
  | _ :: _, .cons _ xs => ⟨Nat.le_refl _, le_refl xs⟩

theorem le_trans : {dims : List Nat} → {u v w : ChainProd dims} →
    le u v → le v w → le u w
  | [], .nil, .nil, .nil, _, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, .cons _ _, huv, hvw =>
      ⟨Nat.le_trans huv.1 hvw.1, le_trans huv.2 hvw.2⟩

theorem le_antisymm : {dims : List Nat} → {u v : ChainProd dims} →
    le u v → le v u → u = v
  | [], .nil, .nil, _, _ => rfl
  | _ :: _, .cons x xs, .cons y ys, huv, hvu => by
      have hx : x = y := Fin.ext (Nat.le_antisymm huv.1 hvu.1)
      have hxs : xs = ys := le_antisymm huv.2 hvu.2
      subst hx; subst hxs; rfl

theorem inf_le_left : {dims : List Nat} → (u v : ChainProd dims) → le (inf u v) u
  | [], .nil, .nil => trivial
  | _ :: _, .cons x xs, .cons y ys =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h] <;> omega, inf_le_left xs ys⟩

theorem inf_le_right : {dims : List Nat} → (u v : ChainProd dims) → le (inf u v) v
  | [], .nil, .nil => trivial
  | _ :: _, .cons x xs, .cons y ys =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h], inf_le_right xs ys⟩

theorem le_inf : {dims : List Nat} → {z u v : ChainProd dims} →
    le z u → le z v → le z (inf u v)
  | [], .nil, .nil, .nil, _, _ => trivial
  | _ :: _, .cons _ _, .cons x _, .cons y _, hzu, hzv =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h, hzu.1, hzv.1], le_inf hzu.2 hzv.2⟩

theorem le_sup_left : {dims : List Nat} → (u v : ChainProd dims) → le u (sup u v)
  | [], .nil, .nil => trivial
  | _ :: _, .cons x xs, .cons y ys =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h], le_sup_left xs ys⟩

theorem le_sup_right : {dims : List Nat} → (u v : ChainProd dims) → le v (sup u v)
  | [], .nil, .nil => trivial
  | _ :: _, .cons x xs, .cons y ys =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h] <;> omega, le_sup_right xs ys⟩

theorem sup_le : {dims : List Nat} → {u v z : ChainProd dims} →
    le u z → le v z → le (sup u v) z
  | [], .nil, .nil, .nil, _, _ => trivial
  | _ :: _, .cons x _, .cons y _, .cons _ _, huz, hvz =>
      ⟨by by_cases h : x.val ≤ y.val <;> simp [h, huz.1, hvz.1], sup_le huz.2 hvz.2⟩

end ChainProd

/-- Every chain product `C_{a_1} × ⋯ × C_{a_d}` forms a lattice under componentwise order. -/
def chainProdLattice (dims : List Nat) : LatticePoset where
  Carrier      := ChainProd dims
  le           := ChainProd.le
  le_refl      := ChainProd.le_refl
  le_trans     := ChainProd.le_trans
  le_antisymm  := ChainProd.le_antisymm
  inf          := ChainProd.inf
  sup          := ChainProd.sup
  inf_le_left  := ChainProd.inf_le_left
  inf_le_right := ChainProd.inf_le_right
  le_inf       := ChainProd.le_inf
  le_sup_left  := ChainProd.le_sup_left
  le_sup_right := ChainProd.le_sup_right
  sup_le       := ChainProd.sup_le

/-- A valid finite nonempty chain product lattice specification: non-empty list of positive chain sizes. -/
def ValidChainDims (dims : List Nat) : Prop :=
  dims ≠ [] ∧ ∀ a ∈ dims, 1 ≤ a

/-- Direct product of two posets. -/
def prodPoset (P Q : Poset) : Poset where
  Carrier := P.Carrier × Q.Carrier
  le u v := P.le u.1 v.1 ∧ Q.le u.2 v.2
  le_refl u := ⟨P.le_refl u.1, Q.le_refl u.2⟩
  le_trans h1 h2 := ⟨P.le_trans h1.1 h2.1, Q.le_trans h1.2 h2.2⟩
  le_antisymm h1 h2 := Prod.ext (P.le_antisymm h1.1 h2.1) (Q.le_antisymm h1.2 h2.2)

/-- Order-preserving map `f : P → Q` between posets. -/
structure OrderHom (P Q : Poset) where
  toFun : P.Carrier → Q.Carrier
  mono  : ∀ {u v : P.Carrier}, P.le u v → Q.le (toFun u) (toFun v)

theorem OrderHom.ext {P Q : Poset} {f g : OrderHom P Q}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with | mk tf _ =>
  cases g with | mk tg _ =>
  dsimp only [] at h
  have hfun : tf = tg := funext h
  subst hfun; rfl

/-- Universal property of poset products: `OrderHom P (Q₁ × Q₂) ≃ OrderHom P Q₁ × OrderHom P Q₂`. -/
def orderHomProdEquiv (P Q₁ Q₂ : Poset) :
    Equiv (OrderHom P (prodPoset Q₁ Q₂)) (OrderHom P Q₁ × OrderHom P Q₂) where
  toFun f :=
    ( { toFun := fun x => (f.toFun x).1, mono := fun h => (f.mono h).1 },
      { toFun := fun x => (f.toFun x).2, mono := fun h => (f.mono h).2 } )
  invFun p :=
    { toFun := fun x => (p.1.toFun x, p.2.toFun x)
      mono := fun h => ⟨p.1.mono h, p.2.mono h⟩ }
  left_inv _ := OrderHom.ext (fun _ => rfl)
  right_inv p := by cases p; rfl

/-- Unfolding `chainProdLattice (a :: as)` as `prodPoset (chainLattice a) (chainProdLattice as)`. -/
def orderHomConsCodomainEquiv (P : Poset) (a : Nat) (as : List Nat) :
    Equiv (OrderHom P (chainProdLattice (a :: as)).toPoset)
          (OrderHom P (chainLattice a).toPoset × OrderHom P (chainProdLattice as).toPoset) where
  toFun f :=
    ( { toFun := fun x => match f.toFun x with | .cons hd _ => hd
        mono := fun {u v} huv => by
          have hm := f.mono huv
          revert hm
          cases f.toFun u with | cons _ _ =>
          cases f.toFun v with | cons _ _ =>
          exact fun h => h.1 },
      { toFun := fun x => match f.toFun x with | .cons _ tl => tl
        mono := fun {u v} huv => by
          have hm := f.mono huv
          revert hm
          cases f.toFun u with | cons _ _ =>
          cases f.toFun v with | cons _ _ =>
          exact fun h => h.2 } )
  invFun p :=
    { toFun := fun x => .cons (p.1.toFun x) (p.2.toFun x)
      mono := fun huv => ⟨p.1.mono huv, p.2.mono huv⟩ }
  left_inv f := OrderHom.ext (fun x => by dsimp only []; cases f.toFun x; rfl)
  right_inv p := by cases p; rfl

/-- Counting elements of `Fin c` satisfying a Bool predicate. -/
def countFin : (c : Nat) → (Fin c → Bool) → Nat
  | 0, _ => 0
  | c + 1, p =>
      countFin c (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
      (if p ⟨c, Nat.lt_succ_self c⟩ then 1 else 0)

theorem countFin_le (c : Nat) (p : Fin c → Bool) : countFin c p ≤ c := by
  induction c with
  | zero => exact Nat.le_refl 0
  | succ c ih =>
    simp only [countFin]
    have h1 := ih (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    cases p ⟨c, Nat.lt_succ_self c⟩ <;> simp <;> omega

theorem countFin_mono {c : Nat} {p q : Fin c → Bool}
    (h : ∀ i : Fin c, p i = true → q i = true) :
    countFin c p ≤ countFin c q := by
  induction c with
  | zero => exact Nat.le_refl 0
  | succ c ih =>
    simp only [countFin]
    have h1 := ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 := h ⟨c, Nat.lt_succ_self c⟩
    cases hp : p ⟨c, Nat.lt_succ_self c⟩ <;> cases hq : q ⟨c, Nat.lt_succ_self c⟩
    · simp; exact h1
    · simp; omega
    · exfalso; rw [hp, hq] at h2; exact Bool.noConfusion (h2 rfl)
    · simp; omega

theorem countFin_ext {c : Nat} {p q : Fin c → Bool} (h : ∀ i, p i = q i) :
    countFin c p = countFin c q := by
  have hfun : p = q := funext h
  rw [hfun]

theorem countFin_const_false : (c : Nat) → countFin c (fun _ => false) = 0
  | 0 => rfl
  | c + 1 => by simp [countFin, countFin_const_false c]

/-- Number of `i : Fin c` with `k ≤ i.val` equals `c - k` when `k ≤ c`. -/
theorem countFin_ge (c k : Nat) (hk : k ≤ c) :
    countFin c (fun i => decide (k ≤ i.val)) = c - k := by
  induction c with
  | zero => simp [countFin]
  | succ c ih =>
    simp only [countFin]
    have hfun_eq : (fun i : Fin c => decide (k ≤ (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (c + 1)).val)) =
        (fun i : Fin c => decide (k ≤ i.val)) := rfl
    rw [hfun_eq]
    by_cases hkc : k ≤ c
    · have h1 := ih hkc
      have h2 : decide (k ≤ c) = true := decide_eq_true hkc
      rw [h1]
      change (c - k) + (if decide (k ≤ c) = true then 1 else 0) = c + 1 - k
      rw [h2]
      simp
      omega
    · have hkeq : k = c + 1 := by omega
      subst hkeq
      have hfalse : ∀ i : Fin c, decide (c + 1 ≤ i.val) = false :=
        fun i => decide_eq_false (by omega)
      rw [countFin_ext hfalse, countFin_const_false]
      change 0 + (if decide (c + 1 ≤ c) = true then 1 else 0) = c + 1 - (c + 1)
      rw [decide_eq_false (by omega)]
      simp

/-- 1D partition conjugation involution on monotone maps `Fin c → Fin (d + 1)`. -/
def conjMap (c d : Nat) (g : Fin c → Fin (d + 1)) (j : Fin d) : Fin (c + 1) :=
  ⟨countFin c (fun i => decide (d - j.val ≤ (g i).val)),
   Nat.lt_succ_of_le (countFin_le c _)⟩

theorem conjMap_mono (c d : Nat) (g : Fin c → Fin (d + 1))
    {j₁ j₂ : Fin d} (hj : j₁.val ≤ j₂.val) :
    (conjMap c d g j₁).val ≤ (conjMap c d g j₂).val := by
  apply countFin_mono
  intro i hi
  have hgi : d - j₁.val ≤ (g i).val := of_decide_eq_true hi
  exact decide_eq_true (by omega)

theorem conjMap_involution (c d : Nat) (g : Fin c → Fin (d + 1))
    (hg : ∀ i₁ i₂ : Fin c, i₁.val ≤ i₂.val → (g i₁).val ≤ (g i₂).val)
    (i₀ : Fin c) :
    conjMap d c (conjMap c d g) i₀ = g i₀ := by
  apply Fin.ext
  change countFin d (fun j : Fin d => decide (c - i₀.val ≤ (conjMap c d g j).val)) = (g i₀).val
  have hiff : ∀ j : Fin d,
      decide (c - i₀.val ≤ (conjMap c d g j).val) = decide (d - (g i₀).val ≤ j.val) := by
    intro j
    by_cases hge : d - (g i₀).val ≤ j.val
    · have hrhs : decide (d - (g i₀).val ≤ j.val) = true := decide_eq_true hge
      have hd : d - j.val ≤ (g i₀).val := by omega
      have hlow : countFin c (fun i : Fin c => decide (i₀.val ≤ i.val)) ≤
          (conjMap c d g j).val := by
        apply countFin_mono
        intro i hi
        have hi' : i₀.val ≤ i.val := of_decide_eq_true hi
        have hgi := hg i₀ i hi'
        exact decide_eq_true (by omega)
      rw [countFin_ge c i₀.val (by omega)] at hlow
      rw [hrhs, decide_eq_true hlow]
    · have hrhs : decide (d - (g i₀).val ≤ j.val) = false := decide_eq_false hge
      have hd : (g i₀).val < d - j.val := by omega
      have hupp : (conjMap c d g j).val ≤
          countFin c (fun i : Fin c => decide (i₀.val + 1 ≤ i.val)) := by
        apply countFin_mono
        intro i hi
        have hgi : d - j.val ≤ (g i).val := of_decide_eq_true hi
        by_cases hlt : i.val ≤ i₀.val
        · have hle := hg i i₀ hlt
          omega
        · exact decide_eq_true (by omega)
      rw [countFin_ge c (i₀.val + 1) (by omega)] at hupp
      rw [hrhs, decide_eq_false (by omega)]
  rw [countFin_ext hiff, countFin_ge d (d - (g i₀).val) (by omega)]
  have hlt := (g i₀).isLt
  omega

/-- Solid-partition box symmetry:
    `OrderHom (C_c × P) C_{d+1} ≃ OrderHom (C_d × P) C_{c+1}` for any chain product `P`. -/
def orderHomChainSwapEquiv (c d : Nat) (dims : List Nat) :
    Equiv (OrderHom (chainProdLattice (c :: dims)).toPoset (chainLattice (d + 1)).toPoset)
          (OrderHom (chainProdLattice (d :: dims)).toPoset (chainLattice (c + 1)).toPoset) where
  toFun f :=
    { toFun := fun u => match u with
        | .cons j xs => conjMap c d (fun i => f.toFun (.cons i xs)) j
      mono := fun {u v} huv => by
        cases u with | cons j₁ xs₁ =>
        cases v with | cons j₂ xs₂ =>
        rcases huv with ⟨hj, hxs⟩
        have step1 : (conjMap c d (fun i => f.toFun (.cons i xs₁)) j₁).val ≤
            (conjMap c d (fun i => f.toFun (.cons i xs₁)) j₂).val :=
          conjMap_mono c d _ hj
        have step2 : (conjMap c d (fun i => f.toFun (.cons i xs₁)) j₂).val ≤
            (conjMap c d (fun i => f.toFun (.cons i xs₂)) j₂).val := by
          apply countFin_mono
          intro i hi
          have h1 : d - j₂.val ≤ (f.toFun (.cons i xs₁)).val := of_decide_eq_true hi
          have h2 : (f.toFun (.cons i xs₁)).val ≤ (f.toFun (.cons i xs₂)).val :=
            f.mono ⟨Nat.le_refl _, hxs⟩
          exact decide_eq_true (Nat.le_trans h1 h2)
        exact Nat.le_trans step1 step2 }
  invFun h :=
    { toFun := fun u => match u with
        | .cons i xs => conjMap d c (fun j => h.toFun (.cons j xs)) i
      mono := fun {u v} huv => by
        cases u with | cons i₁ xs₁ =>
        cases v with | cons i₂ xs₂ =>
        rcases huv with ⟨hi, hxs⟩
        have step1 : (conjMap d c (fun j => h.toFun (.cons j xs₁)) i₁).val ≤
            (conjMap d c (fun j => h.toFun (.cons j xs₁)) i₂).val :=
          conjMap_mono d c _ hi
        have step2 : (conjMap d c (fun j => h.toFun (.cons j xs₁)) i₂).val ≤
            (conjMap d c (fun j => h.toFun (.cons j xs₂)) i₂).val := by
          apply countFin_mono
          intro j hj
          have h1 : c - i₂.val ≤ (h.toFun (.cons j xs₁)).val := of_decide_eq_true hj
          have h2 : (h.toFun (.cons j xs₁)).val ≤ (h.toFun (.cons j xs₂)).val :=
            h.mono ⟨Nat.le_refl _, hxs⟩
          exact decide_eq_true (Nat.le_trans h1 h2)
        exact Nat.le_trans step1 step2 }
  left_inv f := OrderHom.ext (fun u => by
    cases u with | cons i xs =>
    exact conjMap_involution c d (fun i' => f.toFun (.cons i' xs))
      (fun i₁ i₂ hi => f.mono ⟨hi, ChainProd.le_refl xs⟩) i)
  right_inv h := OrderHom.ext (fun u => by
    cases u with | cons j xs =>
    exact conjMap_involution d c (fun j' => h.toFun (.cons j' xs))
      (fun j₁ j₂ hj => h.mono ⟨hj, ChainProd.le_refl xs⟩) j)

/-- Dropping a trivial 1-element chain factor `C_1 × P ≃ P`. -/
def orderHomDropUnitChainEquiv (dims : List Nat) (Q : Poset) :
    Equiv (OrderHom (chainProdLattice (1 :: dims)).toPoset Q)
          (OrderHom (chainProdLattice dims).toPoset Q) where
  toFun f :=
    { toFun := fun xs => f.toFun (.cons ⟨0, Nat.zero_lt_one⟩ xs)
      mono := fun hxs => f.mono ⟨Nat.le_refl 0, hxs⟩ }
  invFun g :=
    { toFun := fun u => match u with | .cons _ xs => g.toFun xs
      mono := fun {u v} huv => by
        cases u with | cons _ _ =>
        cases v with | cons _ _ =>
        exact g.mono huv.2 }
  left_inv f := OrderHom.ext (fun u => by
    cases u with | cons i xs =>
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    subst hi; rfl)
  right_inv _ := OrderHom.ext (fun _ => rfl)

/-! ## Section 3: Binomial/Multinomial Coefficients and MacMahon Formula Classes -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : (n : Nat) → 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

def binom (n k : Nat) : Nat :=
  match k, n with
  | 0, _ => 1
  | _ + 1, 0 => 0
  | k + 1, n + 1 => binom n k + binom n (k + 1)

theorem binom_zero : (n : Nat) → binom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem binom_succ_one (m : Nat) : binom (m + 1) 1 = 1 + binom m 1 := by
  change binom m 0 + binom m 1 = 1 + binom m 1
  rw [binom_zero]

theorem binom_succ_two (m : Nat) : binom (m + 1) 2 = binom m 1 + binom m 2 := rfl
theorem binom_succ_three (m : Nat) : binom (m + 1) 3 = binom m 2 + binom m 3 := rfl
theorem binom_succ_four (m : Nat) : binom (m + 1) 4 = binom m 3 + binom m 4 := rfl
theorem binom_succ_five (m : Nat) : binom (m + 1) 5 = binom m 4 + binom m 5 := rfl
theorem binom_succ_six (m : Nat) : binom (m + 1) 6 = binom m 5 + binom m 6 := rfl
theorem binom_succ_seven (m : Nat) : binom (m + 1) 7 = binom m 6 + binom m 7 := rfl
theorem binom_succ_eight (m : Nat) : binom (m + 1) 8 = binom m 7 + binom m 8 := rfl

theorem binom_one : (n : Nat) → binom n 1 = n
  | 0 => rfl
  | n + 1 => by simp [binom, binom_one n]; omega

theorem binom_eq_zero_of_lt : ∀ (m k : Nat), m < k → binom m k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | m + 1, 0, h => by omega
  | m + 1, k + 1, h => by
      simp [binom, binom_eq_zero_of_lt m k (by omega), binom_eq_zero_of_lt m (k + 1) (by omega)]

theorem binom_self : (n : Nat) → binom n n = 1
  | 0 => rfl
  | n + 1 => by simp [binom, binom_self n, binom_eq_zero_of_lt n (n + 1) (by omega)]

theorem succ_mul_binom : ∀ (m k : Nat),
    (m + 1) * binom m k = (k + 1) * binom (m + 1) (k + 1)
  | 0, 0 => rfl
  | 0, _ + 1 => by simp [binom]
  | m + 1, 0 => by simp [binom, binom_one]; omega
  | m + 1, k + 1 => by
    have ih1 := succ_mul_binom m k
    have ih2 := succ_mul_binom m (k + 1)
    let a := binom m k
    let b := binom m (k + 1)
    let c := binom m (k + 2)
    change (m + 2) * (a + b) = (k + 2) * ((a + b) + (b + c))
    have lhs_split : (m + 2) * (a + b) = (m + 1) * a + (m + 1) * b + a + b := by
      calc (m + 2) * (a + b)
        _ = (m + 1) * (a + b) + (a + b) := by rw [Nat.succ_mul]
        _ = (m + 1) * a + (m + 1) * b + a + b := by rw [Nat.mul_add]; omega
    have rhs_split : (k + 2) * ((a + b) + (b + c)) =
        (k + 1) * (a + b) + (k + 2) * (b + c) + a + b := by
      calc (k + 2) * ((a + b) + (b + c))
        _ = (k + 2) * (a + b) + (k + 2) * (b + c) := by rw [Nat.mul_add]
        _ = ((k + 1) * (a + b) + (a + b)) + (k + 2) * (b + c) := by rw [Nat.succ_mul]
        _ = (k + 1) * (a + b) + (k + 2) * (b + c) + a + b := by omega
    have eq1 : (m + 1) * a = (k + 1) * (a + b) := ih1
    have eq2 : (m + 1) * b = (k + 2) * (b + c) := ih2
    omega

theorem binom_mul_fact : ∀ (s a b : Nat), a + b = s →
    binom (a + b) a * (fact a * fact b) = fact (a + b)
  | _, 0, _, _ => by simp [binom, fact]
  | _, a + 1, 0, _ => by simp [binom_self, fact]
  | _ + 1, a + 1, b + 1, _ => by
    let N := a + b + 1
    have hsum : a + 1 + (b + 1) = N + 1 := by omega
    have ih1 : binom N a * (fact a * fact (b + 1)) = fact N := by
      have := binom_mul_fact (a + (b + 1)) a (b + 1) rfl
      have hr : a + (b + 1) = N := by omega
      rwa [hr] at this
    have ih2 : binom N (a + 1) * (fact (a + 1) * fact b) = fact N := by
      have := binom_mul_fact ((a + 1) + b) (a + 1) b rfl
      have hr : (a + 1) + b = N := by omega
      rwa [hr] at this
    have t1 : binom N a * (fact (a + 1) * fact (b + 1)) = (a + 1) * fact N := by
      calc binom N a * (fact (a + 1) * fact (b + 1))
        _ = binom N a * (((a + 1) * fact a) * fact (b + 1)) := rfl
        _ = (a + 1) * (binom N a * (fact a * fact (b + 1))) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = (a + 1) * fact N := by rw [ih1]
    have t2 : binom N (a + 1) * (fact (a + 1) * fact (b + 1)) = (b + 1) * fact N := by
      calc binom N (a + 1) * (fact (a + 1) * fact (b + 1))
        _ = binom N (a + 1) * (fact (a + 1) * ((b + 1) * fact b)) := rfl
        _ = (b + 1) * (binom N (a + 1) * (fact (a + 1) * fact b)) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = (b + 1) * fact N := by rw [ih2]
    calc binom (a + 1 + (b + 1)) (a + 1) * (fact (a + 1) * fact (b + 1))
      _ = binom (N + 1) (a + 1) * (fact (a + 1) * fact (b + 1)) := by rw [hsum]
      _ = (binom N a + binom N (a + 1)) * (fact (a + 1) * fact (b + 1)) := rfl
      _ = binom N a * (fact (a + 1) * fact (b + 1)) +
          binom N (a + 1) * (fact (a + 1) * fact (b + 1)) := Nat.add_mul _ _ _
      _ = (a + 1) * fact N + (b + 1) * fact N := by rw [t1, t2]
      _ = ((a + 1) + (b + 1)) * fact N := (Nat.add_mul _ _ _).symm
      _ = (N + 1) * fact N := by rw [hsum]
      _ = fact (N + 1) := rfl
      _ = fact (a + 1 + (b + 1)) := by rw [hsum]

theorem binom_symm (a b : Nat) : binom (a + b) a = binom (a + b) b := by
  have h1 := binom_mul_fact (a + b) a b rfl
  have h2 := binom_mul_fact (b + a) b a rfl
  have hcomm_sum : b + a = a + b := Nat.add_comm b a
  have hcomm_fact : fact b * fact a = fact a * fact b := Nat.mul_comm _ _
  rw [hcomm_sum, hcomm_fact] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (fact_pos a) (fact_pos b)) (h1.trans h2.symm)

def listSum : List Nat → Nat
  | [] => 0
  | k :: ks => k + listSum ks

def prodFact : List Nat → Nat
  | [] => 1
  | k :: ks => fact k * prodFact ks

theorem prodFact_pos : (ks : List Nat) → 0 < prodFact ks
  | [] => Nat.zero_lt_one
  | k :: ks => Nat.mul_pos (fact_pos k) (prodFact_pos ks)

/-- Exact multinomial coefficient `(k_1 + ⋯ + k_r)! / (k_1! ⋯ k_r!)`. -/
def multinomial : List Nat → Nat
  | [] => 1
  | k :: ks => binom (k + listSum ks) k * multinomial ks

/-- Defining factorial identity of the multinomial coefficient. -/
theorem multinomial_spec : (ks : List Nat) →
    multinomial ks * prodFact ks = fact (listSum ks)
  | [] => rfl
  | k :: ks => by
    simp only [multinomial, prodFact, listSum]
    calc (binom (k + listSum ks) k * multinomial ks) * (fact k * prodFact ks)
      _ = binom (k + listSum ks) k * (fact k * (multinomial ks * prodFact ks)) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = binom (k + listSum ks) k * (fact k * fact (listSum ks)) := by
            rw [multinomial_spec ks]
      _ = fact (k + listSum ks) := binom_mul_fact _ k (listSum ks) rfl

def prodMultinomials : List (List Nat) → Nat
  | [] => 1
  | ks :: rest => multinomial ks * prodMultinomials rest

/-- A genuine (non-tautological) multinomial coefficient has positive parts and is neither
    the 0/1-part unit `1` nor the trivial edge `binom N 1 = N` (which tautologically equals
    every integer `N`). -/
def IsGenuineMultinomial (ks : List Nat) : Prop :=
  (∀ k ∈ ks, 1 ≤ k) ∧
  ((3 ≤ ks.length) ∨ (∃ a b : Nat, ks = [a, b] ∧ 2 ≤ a ∧ 2 ≤ b))

/-- Specification of a polynomial multinomial factor
    `multinomial ((a*m + b - sum ks) :: ks) = (∏_{j=0}^{sum ks - 1} (a*m + b - j)) / ∏_{k ∈ ks} k!`. -/
structure PolyMultinomSpec where
  slope : Int
  shift : Int
  parts : List Nat

def fallingProdInt (top : Int) : Nat → Int
  | 0 => 1
  | k + 1 => (top - (k : Int)) * fallingProdInt top k

def evalSpecNum (s : PolyMultinomSpec) (m : Int) : Int :=
  fallingProdInt (s.slope * m + s.shift) (listSum s.parts)

def evalSpecDen (s : PolyMultinomSpec) : Int :=
  (prodFact s.parts : Int)

def evalSpecsNum : List PolyMultinomSpec → Int → Int
  | [], _ => 1
  | s :: rest, m => evalSpecNum s m * evalSpecsNum rest m

def evalSpecsDen : List PolyMultinomSpec → Int
  | [] => 1
  | s :: rest => evalSpecDen s * evalSpecsDen rest

/-- Level 1 (Pure Multinomial Product): `f(m)` is a finite product of multinomial coefficients
    with nonnegative integer linear top arguments `a_r * m + b_r`. -/
def IsPureMultinomialPolyProd (f : Nat → Nat) : Prop :=
  ∃ (M0 : Nat) (specs : List (Nat × Nat × List Nat)),
    ∀ m : Nat, M0 ≤ m →
      (∀ (a b : Nat) (ks : List Nat), (a, b, ks) ∈ specs → listSum ks ≤ a * m + b) ∧
      f m = prodMultinomials
        (specs.map (fun (a, b, ks) => (a * m + b - listSum ks) :: ks))

/-- Level 2 (MacMahon Multinomial Quotient): `f(m)` is a quotient of two finite products of
    polynomial multinomial coefficients (with nonzero denominator for large `m`). -/
def IsMacMahonMultinomialQuotient (f : Nat → Nat) : Prop :=
  ∃ (M0 : Nat) (numSpecs denSpecs : List PolyMultinomSpec),
    (∃ m1 : Nat, M0 ≤ m1 ∧ evalSpecsNum denSpecs (m1 : Int) ≠ 0) ∧
    ∀ m : Nat, M0 ≤ m →
      (f m : Int) * evalSpecsDen numSpecs * evalSpecsNum denSpecs (m : Int) =
        evalSpecsDen denSpecs * evalSpecsNum numSpecs (m : Int)

def linListEval : List (Int × Int) → Int → Int
  | [], _ => 1
  | (a, b) :: rest, m => (a * m + b) * linListEval rest m

/-- Level 3 (General MacMahon Rational Linear Ratio): `f(m)` eventually agrees with a rational
    constant times a quotient of products of integer linear factors `(α_r m + β_r)`. -/
def IsRationalLinearRatio (f : Nat → Nat) : Prop :=
  ∃ (M0 : Nat) (cNum cDen : Int) (numLin denLin : List (Int × Int)),
    cDen ≠ 0 ∧
    (∃ m1 : Nat, M0 ≤ m1 ∧ linListEval denLin (m1 : Int) ≠ 0) ∧
    ∀ m : Nat, M0 ≤ m →
      cDen * linListEval denLin (m : Int) * (f m : Int) =
        cNum * linListEval numLin (m : Int)

theorem fallingProdInt_zero_of_lt : ∀ (k n : Nat), n < k → fallingProdInt (n : Int) k = 0
  | 0, _, h => by omega
  | k + 1, n, h => by
    simp only [fallingProdInt]
    by_cases hnk : n = k
    · subst hnk; simp
    · rw [fallingProdInt_zero_of_lt k n (by omega), Int.mul_zero]

theorem fallingProdInt_succ_succ : ∀ (j m : Nat),
    fallingProdInt ((m + 1 : Nat) : Int) (j + 1) =
      ((m + 1 : Nat) : Int) * fallingProdInt (m : Int) j
  | 0, m => by simp [fallingProdInt]
  | j + 1, m => by
    have step := fallingProdInt_succ_succ j m
    simp only [fallingProdInt] at step ⊢
    have hsub : ((m + 1 : Nat) : Int) - ((j + 1 : Nat) : Int) = (m : Int) - (j : Int) := by omega
    rw [hsub, step]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem fallingProdInt_eq_fact_binom : ∀ (k n : Nat),
    ((fact k * binom n k : Nat) : Int) = fallingProdInt (n : Int) k
  | 0, n => by simp [binom_zero, fact, fallingProdInt]
  | k + 1, 0 => by
    have hz := fallingProdInt_zero_of_lt (k + 1) 0 (by omega)
    rw [hz]
    rfl
  | k + 1, n + 1 => by
    have h := succ_mul_binom n k
    have ih := fallingProdInt_eq_fact_binom k n
    have hnat : fact (k + 1) * binom (n + 1) (k + 1) = (n + 1) * (fact k * binom n k) := by
      calc fact (k + 1) * binom (n + 1) (k + 1)
        _ = fact k * ((k + 1) * binom (n + 1) (k + 1)) := by
              simp [fact, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = fact k * ((n + 1) * binom n k) := by rw [← h]
        _ = (n + 1) * (fact k * binom n k) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hnat, natCast_mul, ih, fallingProdInt_succ_succ k n]

theorem multinomial_poly_bridge (top : Nat) (ks : List Nat) (hle : listSum ks ≤ top) :
    (multinomial ((top - listSum ks) :: ks) : Int) * (prodFact ks : Int) =
      fallingProdInt (top : Int) (listSum ks) := by
  let r := top - listSum ks
  have hr : r + listSum ks = top := by omega
  have hspec := multinomial_spec (r :: ks)
  simp only [prodFact, listSum] at hspec
  rw [hr] at hspec
  have hbinom := binom_mul_fact top (listSum ks) r (by omega)
  have hrew : listSum ks + r = top := by omega
  rw [hrew] at hbinom
  have hcancel : multinomial (r :: ks) * prodFact ks =
      fact (listSum ks) * binom top (listSum ks) := by
    have h1 : (multinomial (r :: ks) * prodFact ks) * fact r = fact top := by
      calc (multinomial (r :: ks) * prodFact ks) * fact r
        _ = multinomial (r :: ks) * (fact r * prodFact ks) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = fact top := hspec
    have h2 : (fact (listSum ks) * binom top (listSum ks)) * fact r = fact top := by
      calc (fact (listSum ks) * binom top (listSum ks)) * fact r
        _ = binom top (listSum ks) * (fact (listSum ks) * fact r) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = fact top := hbinom
    exact Nat.eq_of_mul_eq_mul_right (fact_pos r) (h1.trans h2.symm)
  calc (multinomial (r :: ks) : Int) * (prodFact ks : Int)
    _ = ((multinomial (r :: ks) * prodFact ks : Nat) : Int) := (natCast_mul _ _).symm
    _ = ((fact (listSum ks) * binom top (listSum ks) : Nat) : Int) := by rw [hcancel]
    _ = fallingProdInt (top : Int) (listSum ks) := fallingProdInt_eq_fact_binom _ _

/-- Inclusion 1: Every pure multinomial product is a MacMahon multinomial quotient. -/
theorem pure_imp_macmahon {f : Nat → Nat} (h : IsPureMultinomialPolyProd f) :
    IsMacMahonMultinomialQuotient f := by
  rcases h with ⟨M0, specs, hspecs⟩
  let toSpec : Nat × Nat × List Nat → PolyMultinomSpec :=
    fun (a, b, ks) => { slope := (a : Int), shift := (b : Int), parts := ks }
  refine ⟨M0, specs.map toSpec, [], ⟨M0, Nat.le_refl M0, by simp [evalSpecsNum]⟩, ?_⟩
  intro m hm
  rcases hspecs m hm with ⟨hbound, hfm⟩
  rw [hfm]
  simp only [evalSpecsDen, evalSpecsNum, Int.mul_one, Int.one_mul]
  clear hspecs hfm
  induction specs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b, ks⟩
    have hhd : listSum ks ≤ a * m + b := hbound a b ks (List.Mem.head _)
    have htl : ∀ a' b' ks', (a', b', ks') ∈ tl → listSum ks' ≤ a' * m + b' :=
      fun a' b' ks' hmem => hbound a' b' ks' (List.Mem.tail _ hmem)
    have ih_eq := ih htl
    simp only [List.map, toSpec, prodMultinomials, evalSpecsDen, evalSpecsNum, evalSpecDen, evalSpecNum]
    have hstep := multinomial_poly_bridge (a * m + b) ks hhd
    have htop : (a : Int) * (m : Int) + (b : Int) = ((a * m + b : Nat) : Int) := by
      simp [natCast_add, natCast_mul]
    rw [htop, ← hstep, natCast_mul]
    let P := (prodMultinomials (List.map (fun (a, b, ks) => (a * m + b - listSum ks) :: ks) tl) : Int)
    let D := evalSpecsDen (List.map toSpec tl)
    let N := evalSpecsNum (List.map toSpec tl) (m : Int)
    change ((multinomial ((a * m + b - listSum ks) :: ks) : Int) * P) * ((prodFact ks : Int) * D) =
           ((multinomial ((a * m + b - listSum ks) :: ks) : Int) * (prodFact ks : Int)) * N
    have ih_eq' : P * D = N := ih_eq
    calc ((multinomial ((a * m + b - listSum ks) :: ks) : Int) * P) * ((prodFact ks : Int) * D)
      _ = ((multinomial ((a * m + b - listSum ks) :: ks) : Int) * (prodFact ks : Int)) * (P * D) := by
            simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = ((multinomial ((a * m + b - listSum ks) :: ks) : Int) * (prodFact ks : Int)) * N := by
            rw [ih_eq']

def specToLinFactors (s : PolyMultinomSpec) : Nat → List (Int × Int)
  | 0 => []
  | k + 1 => (s.slope, s.shift - (k : Int)) :: specToLinFactors s k

theorem specToLinFactors_eval (s : PolyMultinomSpec) (k : Nat) (m : Int) :
    linListEval (specToLinFactors s k) m = fallingProdInt (s.slope * m + s.shift) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [specToLinFactors, linListEval, fallingProdInt, ih]
    have h : s.slope * m + (s.shift - (k : Int)) = s.slope * m + s.shift - (k : Int) := by omega
    rw [h]

def specsToLinFactors : List PolyMultinomSpec → List (Int × Int)
  | [] => []
  | s :: rest => specToLinFactors s (listSum s.parts) ++ specsToLinFactors rest

theorem linListEval_append (l1 l2 : List (Int × Int)) (m : Int) :
    linListEval (l1 ++ l2) m = linListEval l1 m * linListEval l2 m := by
  induction l1 with
  | nil => simp [linListEval]
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp [linListEval, ih, Int.mul_assoc]

theorem specsToLinFactors_eval (specs : List PolyMultinomSpec) (m : Int) :
    linListEval (specsToLinFactors specs) m = evalSpecsNum specs m := by
  induction specs with
  | nil => rfl
  | cons s rest ih =>
    simp only [specsToLinFactors, evalSpecsNum, evalSpecNum]
    rw [linListEval_append, specToLinFactors_eval, ih]

theorem evalSpecsDen_pos : (specs : List PolyMultinomSpec) → 1 ≤ evalSpecsDen specs
  | [] => Int.le_refl 1
  | s :: rest => by
    simp only [evalSpecsDen, evalSpecDen]
    have h1 : (1 : Int) ≤ (prodFact s.parts : Int) := by
      have := prodFact_pos s.parts; omega
    have h2 := evalSpecsDen_pos rest
    have := Int.mul_le_mul h1 h2 (by omega) (by omega)
    omega

/-- Inclusion 2: Every MacMahon multinomial quotient is a rational linear ratio. -/
theorem macmahon_imp_rationalLinear {f : Nat → Nat} (h : IsMacMahonMultinomialQuotient f) :
    IsRationalLinearRatio f := by
  rcases h with ⟨M0, numSpecs, denSpecs, ⟨m1, hm1, hden_nz⟩, heq⟩
  refine ⟨M0, evalSpecsDen denSpecs, evalSpecsDen numSpecs,
    specsToLinFactors numSpecs, specsToLinFactors denSpecs, ?_, ?_, ?_⟩
  · have := evalSpecsDen_pos numSpecs; omega
  · refine ⟨m1, hm1, ?_⟩
    rw [specsToLinFactors_eval]
    exact hden_nz
  · intro m hm
    rw [specsToLinFactors_eval, specsToLinFactors_eval]
    have hstep := heq m hm
    calc evalSpecsDen numSpecs * evalSpecsNum denSpecs (m : Int) * (f m : Int)
      _ = (f m : Int) * evalSpecsDen numSpecs * evalSpecsNum denSpecs (m : Int) := by
            simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = evalSpecsDen denSpecs * evalSpecsNum numSpecs (m : Int) := hstep

/-! ## Section 4: Polynomial Arithmetic Engine over `Int` -/

abbrev Poly := List Int

namespace Poly

def eval : Poly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => (c + d) :: add cs ds

def neg : Poly → Poly
  | [] => []
  | c :: cs => (-c) :: neg cs

def sub (p q : Poly) : Poly := add p (neg q)

def scale (k : Int) : Poly → Poly
  | [] => []
  | c :: cs => (k * c) :: scale k cs

def mul : Poly → Poly → Poly
  | [], _ => []
  | c :: cs, q => add (scale c q) (0 :: mul cs q)

def compScale (s : Int) : Poly → Poly
  | [] => []
  | c :: cs => c :: scale s (compScale s cs)

def allZero : Poly → Prop
  | [] => True
  | c :: cs => c = 0 ∧ allZero cs

theorem eval_add : ∀ (p q : Poly) (x : Int), eval (add p q) x = eval p x + eval q x
  | [], q, x => by simp [add, eval]
  | c :: cs, [], x => by simp [add, eval]
  | c :: cs, d :: ds, x => by
    simp only [add, eval, eval_add cs ds x, Int.mul_add]
    omega

theorem eval_neg : ∀ (p : Poly) (x : Int), eval (neg p) x = - eval p x
  | [], _ => by simp [neg, eval]
  | c :: cs, x => by
    simp only [neg, eval, eval_neg cs x, Int.mul_neg]
    omega

theorem eval_sub (p q : Poly) (x : Int) : eval (sub p q) x = eval p x - eval q x := by
  simp only [sub, eval_add, eval_neg]
  omega

theorem eval_scale (k : Int) : ∀ (p : Poly) (x : Int), eval (scale k p) x = k * eval p x
  | [], _ => by simp [scale, eval]
  | c :: cs, x => by
    simp only [scale, eval, eval_scale k cs x, Int.mul_add]
    have : x * (k * eval cs x) = k * (x * eval cs x) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega

theorem eval_mul : ∀ (p q : Poly) (x : Int), eval (mul p q) x = eval p x * eval q x
  | [], _, _ => by simp [mul, eval]
  | c :: cs, q, x => by
    simp only [mul, eval, eval_add, eval_scale, eval_mul cs q x, Int.add_mul]
    have : x * (eval cs x * eval q x) = (x * eval cs x) * eval q x := by
      simp [Int.mul_assoc]
    omega

theorem eval_compScale (s : Int) : ∀ (p : Poly) (x : Int),
    eval (compScale s p) x = eval p (s * x)
  | [], _ => rfl
  | c :: cs, x => by
    simp only [compScale, eval, eval_scale, eval_compScale s cs x]
    have hmul : x * (s * eval cs (s * x)) = s * x * eval cs (s * x) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [hmul]

theorem eval_allZero : ∀ {p : Poly}, allZero p → (x : Int) → eval p x = 0
  | [], _, _ => rfl
  | _ :: _, ⟨hc, hcs⟩, x => by simp [eval, hc, eval_allZero hcs x]

theorem allZero_scale_cancel {s : Int} (hs : s ≠ 0) :
    ∀ {p : Poly}, allZero (scale s p) → allZero p
  | [], _ => trivial
  | _ :: _, ⟨hc, hcs⟩ =>
    ⟨by cases Int.mul_eq_zero.mp hc with | inl h => exact absurd h hs | inr h => exact h,
     allZero_scale_cancel hs hcs⟩

theorem allZero_compScale_cancel {s : Int} (hs : s ≠ 0) :
    ∀ {p : Poly}, allZero (compScale s p) → allZero p
  | [], _ => trivial
  | _ :: _, ⟨hc, hcs⟩ => ⟨hc, allZero_compScale_cancel hs (allZero_scale_cancel hs hcs)⟩

/-- Identity principle: a polynomial vanishing at all integers `m ≥ M0` has all zero coefficients. -/
theorem eventually_zero_imp_allZero : ∀ (p : Poly) (M0 : Nat),
    (∀ m : Nat, M0 ≤ m → eval p (m : Int) = 0) → allZero p
  | [], _, _ => trivial
  | c :: cs, M0, h => by
    let m1 : Nat := M0 + c.natAbs + 1
    have hm1 : M0 ≤ m1 := by omega
    have hev1 := h m1 hm1
    simp only [eval] at hev1
    have hc : c = 0 := by
      let k := eval cs (m1 : Int)
      have hev_k : c + (m1 : Int) * k = 0 := hev1
      by_cases hk0 : k = 0
      · rw [hk0, Int.mul_zero, Int.add_zero] at hev_k
        exact hev_k
      · by_cases hkpos : 1 ≤ k
        · have hmul : (m1 : Int) * 1 ≤ (m1 : Int) * k :=
            Int.mul_le_mul_of_nonneg_left hkpos (by omega)
          omega
        · have hkneg : k ≤ -1 := by omega
          have hmul : (m1 : Int) * k ≤ (m1 : Int) * (-1) :=
            Int.mul_le_mul_of_nonneg_left hkneg (by omega)
          omega
    refine ⟨hc, eventually_zero_imp_allZero cs (M0 + 1) ?_⟩
    intro m hm
    have hevm := h m (by omega)
    simp only [eval, hc, Int.zero_add] at hevm
    cases Int.mul_eq_zero.mp hevm with
    | inl hm0 => omega
    | inr hcs0 => exact hcs0

/-- Two polynomials agreeing on `s * m` for all `m ≥ M0` (with `1 ≤ s`) agree at EVERY integer `z`. -/
theorem eq_everywhere_of_arith_prog (p q : Poly) (s M0 : Nat) (hs : 1 ≤ s)
    (h : ∀ m : Nat, M0 ≤ m → eval p ((s : Int) * (m : Int)) =
                              eval q ((s : Int) * (m : Int))) :
    ∀ z : Int, eval p z = eval q z := by
  let d := sub p q
  have hd : allZero (compScale (s : Int) d) := by
    apply eventually_zero_imp_allZero _ M0
    intro m hm
    rw [eval_compScale, eval_sub]
    have := h m hm
    omega
  have hd0 : allZero d := allZero_compScale_cancel (by omega) hd
  intro z
  have hz := eval_allZero hd0 z
  rw [eval_sub] at hz
  omega

def fallPoly : Nat → Poly
  | 0 => [1]
  | k + 1 => mul [- (k : Int), 1] (fallPoly k)

theorem eval_fallPoly (k : Nat) (x : Int) :
    eval (fallPoly k) x = fallingProdInt x k := by
  induction k with
  | zero => simp [fallPoly, fallingProdInt, eval]
  | succ k ih =>
    simp only [fallPoly, fallingProdInt, eval_mul, eval, ih]
    have : (- (k : Int) + x * (1 + x * 0)) = x - (k : Int) := by omega
    rw [this]

end Poly

/-! ## Section 5: Positive Non-Vacuity Witnesses (`C_2` and `C_2 × C_2`) -/

/-- Order polynomial of `C_2`: `Ω(C_2, m) = binom (m + 1) 2 = m(m+1)/2`. -/
def omegaChain2 (m : Nat) : Nat := binom (m + 1) 2

theorem omegaChain2_isPureMultinomial : IsPureMultinomialPolyProd omegaChain2 := by
  refine ⟨1, [(1, 1, [2])], ?_⟩
  intro m hm
  refine ⟨?_, ?_⟩
  · intro a b ks hmem
    simp at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    simp [listSum]; omega
  · simp only [List.map, prodMultinomials, multinomial, listSum, omegaChain2,
               Nat.add_zero, binom_self, Nat.mul_one]
    have h : 1 * m + 1 - 2 + 2 = m + 1 := by omega
    rw [h]
    have hs := binom_symm 2 (1 * m + 1 - 2)
    have h2 : 2 + (1 * m + 1 - 2) = m + 1 := by omega
    rwa [h2] at hs

abbrev Sq2 := Bool × Bool

def sq2LeBool (u v : Sq2) : Bool :=
  bImp u.1 v.1 && bImp u.2 v.2

def sq2Bit (u : Sq2) : Nat :=
  (if u.1 then 2 else 0) + (if u.2 then 1 else 0)

def sq2MaskNat : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | 4 => 7
  | 5 => 15
  | _ => 0

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

def inSq2IdealNat (idx : Nat) (u : Sq2) : Bool :=
  decide (((sq2MaskNat idx) / pow2 (sq2Bit u)) % 2 = 1)

def sq2IdealSubNat (j i : Nat) : Bool :=
  bImp (inSq2IdealNat j (false, false)) (inSq2IdealNat i (false, false)) &&
  bImp (inSq2IdealNat j (false, true))  (inSq2IdealNat i (false, true))  &&
  bImp (inSq2IdealNat j (true,  false)) (inSq2IdealNat i (true,  false)) &&
  bImp (inSq2IdealNat j (true,  true))  (inSq2IdealNat i (true,  true))

private theorem nat6_cases (n : Nat) (h : n < 6) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega

theorem inSq2IdealNat_downset (idx : Nat) (hidx : idx < 6) {u v : Sq2}
    (huv : sq2LeBool u v = true) (hv : inSq2IdealNat idx v = true) :
    inSq2IdealNat idx u = true := by
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  rcases nat6_cases idx hidx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;>
    revert huv hv <;> decide

theorem sq2IdealSubNat_iff (j i : Nat) :
    sq2IdealSubNat j i = true ↔
      ∀ u : Sq2, inSq2IdealNat j u = true → inSq2IdealNat i u = true := by
  constructor
  · intro hsub ⟨u1, u2⟩
    unfold sq2IdealSubNat at hsub
    simp only [Bool.and_eq_true] at hsub
    rcases hsub with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    cases u1 <;> cases u2
    · revert h0; cases inSq2IdealNat j (false, false) <;> cases inSq2IdealNat i (false, false) <;> decide
    · revert h1; cases inSq2IdealNat j (false, true)  <;> cases inSq2IdealNat i (false, true)  <;> decide
    · revert h2; cases inSq2IdealNat j (true,  false) <;> cases inSq2IdealNat i (true,  false) <;> decide
    · revert h3; cases inSq2IdealNat j (true,  true)  <;> cases inSq2IdealNat i (true,  true)  <;> decide
  · intro hall
    unfold sq2IdealSubNat
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨bImp_true (hall _), bImp_true (hall _)⟩, bImp_true (hall _)⟩, bImp_true (hall _)⟩

def classifySq2Bools (b00 b01 b10 b11 : Bool) : Nat :=
  if !b00 then 0
  else if b11 then 5
  else match b01, b10 with
  | false, false => 1
  | true,  false => 2
  | false, true  => 3
  | true,  true  => 4

theorem classifySq2Bools_lt (b00 b01 b10 b11 : Bool) :
    classifySq2Bools b00 b01 b10 b11 < 6 := by
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide

theorem classifySq2Bools_spec (b00 b01 b10 b11 : Bool)
    (hvalid : (bImp b01 b00 && bImp b10 b00 && bImp b11 b01 && bImp b11 b10) = true) :
    let idx := classifySq2Bools b00 b01 b10 b11
    inSq2IdealNat idx (false, false) = b00 ∧
    inSq2IdealNat idx (false, true)  = b01 ∧
    inSq2IdealNat idx (true,  false) = b10 ∧
    inSq2IdealNat idx (true,  true)  = b11 := by
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> revert hvalid <;> decide

def classifySq2Downset (S : Sq2 → Bool) : Fin 6 :=
  ⟨classifySq2Bools (S (false, false)) (S (false, true)) (S (true, false)) (S (true, true)),
   classifySq2Bools_lt _ _ _ _⟩

theorem classifySq2Downset_spec (S : Sq2 → Bool)
    (hS : ∀ u v : Sq2, sq2LeBool u v = true → S v = true → S u = true) (u : Sq2) :
    inSq2IdealNat (classifySq2Downset S).val u = S u := by
  have hv : (bImp (S (false, true)) (S (false, false)) &&
             bImp (S (true, false)) (S (false, false)) &&
             bImp (S (true, true))  (S (false, true))  &&
             bImp (S (true, true))  (S (true, false))) = true := by
    rw [bImp_true (hS (false, false) (false, true) rfl),
        bImp_true (hS (false, false) (true, false) rfl),
        bImp_true (hS (false, true) (true, true) rfl),
        bImp_true (hS (true, false) (true, true) rfl)]
    rfl
  have h4 := classifySq2Bools_spec _ _ _ _ hv
  rcases u with ⟨u1, u2⟩
  cases u1 <;> cases u2
  · exact h4.1
  · exact h4.2.1
  · exact h4.2.2.1
  · exact h4.2.2.2

theorem sq2Ideal_injective {i j : Fin 6}
    (h : ∀ u : Sq2, inSq2IdealNat i.val u = inSq2IdealNat j.val u) : i = j := by
  rcases i with ⟨iv, ilt⟩
  rcases j with ⟨jv, jlt⟩
  apply Fin.ext
  dsimp only [] at h ⊢
  have h00 := h (false, false)
  have h01 := h (false, true)
  have h10 := h (true, false)
  have h11 := h (true, true)
  rcases nat6_cases iv ilt with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases nat6_cases jv jlt with rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert h00 h01 h10 h11 <;> decide

structure SubSq2Hom (i : Fin 6) (m : Nat) where
  toFun : (u : Sq2) → inSq2IdealNat i.val u = true → Fin m
  mono  : ∀ u v (hu : inSq2IdealNat i.val u = true) (hv : inSq2IdealNat i.val v = true),
            sq2LeBool u v = true → (toFun u hu).val ≤ (toFun v hv).val

theorem SubSq2Hom.ext {i : Fin 6} {m : Nat} {f g : SubSq2Hom i m}
    (h : ∀ u hu, f.toFun u hu = g.toFun u hu) : f = g := by
  cases f with | mk tf _ =>
  cases g with | mk tg _ =>
  dsimp only [] at h
  have hfun : tf = tg := funext (fun u => funext (fun hu => h u hu))
  subst hfun; rfl

def sq2CoeffNat : Nat → Nat → Nat
  | 0, 0 => 1
  | 1, 0 => 1 | 1, 1 => 1
  | 2, 0 => 1 | 2, 1 => 2 | 2, 2 => 1
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 1
  | 4, 0 => 1 | 4, 1 => 4 | 4, 2 => 5 | 4, 3 => 2
  | 5, 0 => 1 | 5, 1 => 5 | 5, 2 => 9 | 5, 3 => 7 | 5, 4 => 2
  | _, _ => 0

def sq2DpNat (i m : Nat) : Nat :=
  sq2CoeffNat i 0 * binom m 0 + sq2CoeffNat i 1 * binom m 1 + sq2CoeffNat i 2 * binom m 2 +
  sq2CoeffNat i 3 * binom m 3 + sq2CoeffNat i 4 * binom m 4

theorem sq2DpNat_zero (i : Fin 6) : sq2DpNat i.val 0 = 1 := by
  rcases i with ⟨iv, ilt⟩
  dsimp only []
  rcases nat6_cases iv ilt with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sq2_coeff_rec (iv : Nat) (hiv : iv < 6) (kv : Nat) (hkv : kv < 5) :
    natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j kv else 0) =
      sq2CoeffNat iv kv + sq2CoeffNat iv (kv + 1) := by
  have hk : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 ∨ kv = 4 := by omega
  rcases nat6_cases iv hiv with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

theorem sq2DpNat_succ (i : Fin 6) (m : Nat) :
    natSum 6 (fun j => if sq2IdealSubNat j i.val then sq2DpNat j m else 0) =
      sq2DpNat i.val (m + 1) := by
  rcases i with ⟨iv, hiv⟩
  dsimp only []
  have h0 : natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 0 else 0) =
      sq2CoeffNat iv 0 + sq2CoeffNat iv 1 := sq2_coeff_rec iv hiv 0 (by omega)
  have h1 : natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 1 else 0) =
      sq2CoeffNat iv 1 + sq2CoeffNat iv 2 := sq2_coeff_rec iv hiv 1 (by omega)
  have h2 : natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 2 else 0) =
      sq2CoeffNat iv 2 + sq2CoeffNat iv 3 := sq2_coeff_rec iv hiv 2 (by omega)
  have h3 : natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 3 else 0) =
      sq2CoeffNat iv 3 + sq2CoeffNat iv 4 := sq2_coeff_rec iv hiv 3 (by omega)
  have h4 : natSum 6 (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 4 else 0) =
      sq2CoeffNat iv 4 + sq2CoeffNat iv 5 := sq2_coeff_rec iv hiv 4 (by omega)
  have hc5 : sq2CoeffNat iv 5 = 0 := by
    rcases nat6_cases iv hiv with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hc5, Nat.add_zero] at h4
  have hlin : ∀ n : Nat,
      natSum n (fun j => if sq2IdealSubNat j iv then sq2DpNat j m else 0) =
      natSum n (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 0 else 0) * binom m 0 +
      natSum n (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 1 else 0) * binom m 1 +
      natSum n (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 2 else 0) * binom m 2 +
      natSum n (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 3 else 0) * binom m 3 +
      natSum n (fun j => if sq2IdealSubNat j iv then sq2CoeffNat j 4 else 0) * binom m 4 := by
    intro n
    induction n with
    | zero => simp [natSum]
    | succ n ih =>
      simp only [natSum, ih, Nat.add_mul]
      cases sq2IdealSubNat n iv <;> simp [sq2DpNat] <;> omega
  rw [hlin 6, h0, h1, h2, h3, h4]
  simp only [sq2DpNat, binom_zero, binom_succ_one, binom_succ_two, binom_succ_three,
             binom_succ_four, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def extendSubSq2Hom (j i : Fin 6) (m : Nat) (g : SubSq2Hom j (m + 1)) : SubSq2Hom i (m + 2) where
  toFun u _ :=
    if hju : inSq2IdealNat j.val u = true then
      ⟨(g.toFun u hju).val, by have := (g.toFun u hju).isLt; omega⟩
    else
      ⟨m + 1, by omega⟩
  mono u v _ _ huv := by
    by_cases hjv : inSq2IdealNat j.val v = true
    · have hju : inSq2IdealNat j.val u = true := inSq2IdealNat_downset j.val j.isLt huv hjv
      rw [dif_pos hju, dif_pos hjv]
      exact g.mono u v hju hjv huv
    · by_cases hju : inSq2IdealNat j.val u = true
      · rw [dif_pos hju, dif_neg hjv]
        dsimp only []
        have := (g.toFun u hju).isLt
        omega
      · rw [dif_neg hju, dif_neg hjv]
        exact Nat.le_refl _

theorem sigmaSubSq2_ext {i j' j : Fin 6} {m : Nat}
    {x' : BoolFiber (sq2IdealSubNat j'.val i.val) (SubSq2Hom j' (m + 1))}
    {x  : BoolFiber (sq2IdealSubNat j.val i.val)  (SubSq2Hom j (m + 1))}
    (hj : j' = j)
    (hx : ∀ (u : Sq2) (hju' : inSq2IdealNat j'.val u = true) (hju : inSq2IdealNat j.val u = true),
            (x'.val.toFun u hju').val = (x.val.toFun u hju).val) :
    (⟨j', x'⟩ : (k : Fin 6) × BoolFiber (sq2IdealSubNat k.val i.val) (SubSq2Hom k (m + 1))) = ⟨j, x⟩ := by
  subst hj
  rcases x' with ⟨h1, g1⟩
  rcases x with ⟨h2, g2⟩
  have hh : h1 = h2 := Subsingleton.elim _ _
  subst hh
  congr 1
  congr 1
  apply SubSq2Hom.ext
  intro u hu
  exact Fin.ext (hx u hu hu)

def subSq2HomStepEquiv (i : Fin 6) (m : Nat) :
    Equiv (SubSq2Hom i (m + 2))
          ((j : Fin 6) × BoolFiber (sq2IdealSubNat j.val i.val) (SubSq2Hom j (m + 1))) where
  toFun f :=
    let S : Sq2 → Bool := fun u =>
      if hu : inSq2IdealNat i.val u = true then decide ((f.toFun u hu).val < m + 1) else false
    have hS : ∀ u v : Sq2, sq2LeBool u v = true → S v = true → S u = true := by
      intro u v huv hv
      dsimp only [S] at hv ⊢
      split at hv
      · rename_i hvi
        have hui := inSq2IdealNat_downset i.val i.isLt huv hvi
        simp only [hui, ↓reduceDIte]
        have hlt := of_decide_eq_true hv
        have hle := f.mono u v hui hvi huv
        exact decide_eq_true (by omega)
      · contradiction
    let j := classifySq2Downset S
    have hjS : ∀ u, inSq2IdealNat j.val u = S u := classifySq2Downset_spec S hS
    have hsub : sq2IdealSubNat j.val i.val = true := (sq2IdealSubNat_iff j.val i.val).mpr (fun u hju => by
      rw [hjS u] at hju
      dsimp only [S] at hju
      split at hju
      · assumption
      · contradiction)
    ⟨j, ⟨hsub, {
      toFun := fun u hju =>
        have hui := (sq2IdealSubNat_iff j.val i.val).mp hsub u hju
        have hStrue : S u = true := by rw [← hjS u]; exact hju
        have hlt : (f.toFun u hui).val < m + 1 := by
          dsimp only [S] at hStrue; simp only [hui, ↓reduceDIte] at hStrue
          exact of_decide_eq_true hStrue
        ⟨(f.toFun u hui).val, hlt⟩
      mono := fun u v hju hjv huv =>
        f.mono u v ((sq2IdealSubNat_iff j.val i.val).mp hsub u hju)
                   ((sq2IdealSubNat_iff j.val i.val).mp hsub v hjv) huv }⟩⟩
  invFun p := extendSubSq2Hom p.1 i m p.2.val
  left_inv f := SubSq2Hom.ext (fun u hui => by
    dsimp only [extendSubSq2Hom]
    split
    · rfl
    · rename_i hnot
      let S : Sq2 → Bool := fun w =>
        if hw : inSq2IdealNat i.val w = true then decide ((f.toFun w hw).val < m + 1) else false
      have hS : ∀ w1 w2 : Sq2, sq2LeBool w1 w2 = true → S w2 = true → S w1 = true := by
        intro w1 w2 hw12 hw2
        dsimp only [S] at hw2 ⊢
        split at hw2
        · rename_i hw2i
          have hw1i := inSq2IdealNat_downset i.val i.isLt hw12 hw2i
          simp only [hw1i, ↓reduceDIte]
          have hlt := of_decide_eq_true hw2
          have hle := f.mono w1 w2 hw1i hw2i hw12
          exact decide_eq_true (by omega)
        · contradiction
      have hspec := classifySq2Downset_spec S hS u
      have hSu_false : S u = false := by
        cases hSu : S u with
        | false => rfl
        | true => rw [hSu] at hspec; exact absurd hspec hnot
      dsimp only [S] at hSu_false
      simp only [hui, ↓reduceDIte] at hSu_false
      have hge : ¬ ((f.toFun u hui).val < m + 1) := of_decide_eq_false hSu_false
      have hval := (f.toFun u hui).isLt
      exact Fin.ext (by dsimp only []; omega))
  right_inv p := by
    rcases p with ⟨j, ⟨hsub, g⟩⟩
    let f := extendSubSq2Hom j i m g
    let S : Sq2 → Bool := fun u =>
      if hu : inSq2IdealNat i.val u = true then decide ((f.toFun u hu).val < m + 1) else false
    have hS : ∀ u v : Sq2, sq2LeBool u v = true → S v = true → S u = true := by
      intro u v huv hv
      dsimp only [S] at hv ⊢
      split at hv
      · rename_i hvi
        have hui := inSq2IdealNat_downset i.val i.isLt huv hvi
        simp only [hui, ↓reduceDIte]
        have hlt := of_decide_eq_true hv
        have hle := f.mono u v hui hvi huv
        exact decide_eq_true (by omega)
      · contradiction
    have hSj : ∀ u : Sq2, S u = inSq2IdealNat j.val u := by
      intro u
      dsimp only [S, f, extendSubSq2Hom]
      by_cases hju : inSq2IdealNat j.val u = true
      · have hui := (sq2IdealSubNat_iff j.val i.val).mp hsub u hju
        rw [dif_pos hui, dif_pos hju, hju]
        dsimp only []
        exact decide_eq_true (g.toFun u hju).isLt
      · have hjf : inSq2IdealNat j.val u = false :=
          Bool.eq_false_iff.mpr hju
        by_cases hui : inSq2IdealNat i.val u = true
        · rw [dif_pos hui, dif_neg hju, hjf]
          dsimp only []
          exact decide_eq_false (Nat.lt_irrefl _)
        · rw [dif_neg hui, hjf]
    have hjeq : classifySq2Downset S = j :=
      sq2Ideal_injective (fun u => (classifySq2Downset_spec S hS u).trans (hSj u))
    refine sigmaSubSq2_ext hjeq (fun u _ hju => ?_)
    dsimp only [f, extendSubSq2Hom]
    rw [dif_pos hju]

def subSq2HomFinEquiv : (m : Nat) → (i : Fin 6) →
    Equiv (SubSq2Hom i (m + 1)) (Fin (sq2DpNat i.val m))
  | 0, i =>
    { toFun := fun _ => ⟨0, by rw [sq2DpNat_zero]; exact Nat.zero_lt_one⟩
      invFun := fun _ => { toFun := fun _ _ => ⟨0, Nat.zero_lt_one⟩, mono := fun _ _ _ _ _ => Nat.le_refl 0 }
      left_inv := fun f => SubSq2Hom.ext (fun u hu => Fin.ext (by have := (f.toFun u hu).isLt; omega))
      right_inv := fun k => Fin.ext (by
        have hklt : k.val < 1 := Nat.lt_of_lt_of_eq k.isLt (sq2DpNat_zero i)
        dsimp only []; omega) }
  | m + 1, i =>
    let w : Nat → Nat := fun j => if sq2IdealSubNat j i.val then sq2DpNat j m else 0
    let eFib : (j : Fin 6) →
        Equiv (BoolFiber (sq2IdealSubNat j.val i.val) (SubSq2Hom j (m + 1))) (Fin (w j.val)) :=
      fun j => boolFiberEquiv (sq2IdealSubNat j.val i.val) (fun _ => subSq2HomFinEquiv m j)
    let eSigma : Equiv ((j : Fin 6) × BoolFiber (sq2IdealSubNat j.val i.val) (SubSq2Hom j (m + 1)))
                       ((j : Fin 6) × Fin (w j.val)) :=
      { toFun := fun ⟨j, x⟩ => ⟨j, (eFib j).toFun x⟩
        invFun := fun ⟨j, y⟩ => ⟨j, (eFib j).invFun y⟩
        left_inv := fun ⟨j, x⟩ => by simp [(eFib j).left_inv]
        right_inv := fun ⟨j, y⟩ => by simp [(eFib j).right_inv] }
    (subSq2HomStepEquiv i m).trans
      (eSigma.trans ((sigmaNatFinEquiv 6 w).trans (Equiv.finCast (sq2DpNat_succ i m))))

/-- Order polynomial of `C_2 × C_2`:
    `Ω(C_2 × C_2, m) = binom m 1 + 4*binom m 2 + 5*binom m 3 + 2*binom m 4`. -/
def omegaSq (m : Nat) : Nat :=
  binom m 1 + 4 * binom m 2 + 5 * binom m 3 + 2 * binom m 4

theorem omegaSq_succ (m : Nat) : sq2DpNat 5 m = omegaSq (m + 1) := by
  simp only [sq2DpNat, sq2CoeffNat, omegaSq, binom_zero, binom_succ_one, binom_succ_two,
             binom_succ_three, binom_succ_four, Nat.mul_add, Nat.mul_one]
  omega

/-- Exact cardinality of `OrderHom (C_2 × C_2) C_m` for ALL `m : Nat`. -/
theorem omegaSq_card (m : Nat) :
    HasCard (OrderHom (chainProdLattice [2, 2]).toPoset (chainLattice m).toPoset) (omegaSq m) := by
  cases m with
  | zero =>
    refine ⟨{
      toFun := fun f => f.toFun (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ .nil))
      invFun := fun k => Fin.elim0 k
      left_inv := fun f => Fin.elim0 (f.toFun (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ .nil)))
      right_inv := fun k => Fin.elim0 k }⟩
  | succ m =>
    let top : Fin 6 := ⟨5, by omega⟩
    have htop : ∀ u : Sq2, inSq2IdealNat 5 u = true := by
      intro ⟨u1, u2⟩; cases u1 <;> cases u2 <;> decide
    let b2fin : Bool → Fin 2 := fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
    let fin2b : Fin 2 → Bool := fun x => decide (x.val = 1)
    let uToChain : Sq2 → ChainProd [2, 2] := fun u => .cons (b2fin u.1) (.cons (b2fin u.2) .nil)
    let chainToU : ChainProd [2, 2] → Sq2 := fun c =>
      match c with | .cons x (.cons y .nil) => (fin2b x, fin2b y)
    have hcu : ∀ u : Sq2, chainToU (uToChain u) = u := by
      intro ⟨u1, u2⟩; cases u1 <;> cases u2 <;> rfl
    have huc : ∀ c : ChainProd [2, 2], uToChain (chainToU c) = c := by
      intro c
      cases c with | cons x rest =>
      cases rest with | cons y rest2 =>
      cases rest2 with | nil =>
      rcases x with ⟨xv, xlt⟩
      rcases y with ⟨yv, ylt⟩
      have hx : xv = 0 ∨ xv = 1 := by omega
      have hy : yv = 0 ∨ yv = 1 := by omega
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
    have hmono1 : ∀ u v : Sq2, sq2LeBool u v = true →
        (chainProdLattice [2, 2]).le (uToChain u) (uToChain v) := by
      intro ⟨u1, u2⟩ ⟨v1, v2⟩ huv
      cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;>
        simp [sq2LeBool, bImp, uToChain, b2fin, chainProdLattice, ChainProd.le] at huv ⊢
    have hmono2 : ∀ c1 c2 : ChainProd [2, 2],
        (chainProdLattice [2, 2]).le c1 c2 → sq2LeBool (chainToU c1) (chainToU c2) = true := by
      intro c1 c2 hc
      cases c1 with | cons x1 r1 => cases r1 with | cons y1 n1 => cases n1 with | nil =>
      cases c2 with | cons x2 r2 => cases r2 with | cons y2 n2 => cases n2 with | nil =>
      rcases hc with ⟨hx, hy, _⟩
      dsimp only [chainToU, fin2b, sq2LeBool]
      have hx' : bImp (decide (x1.val = 1)) (decide (x2.val = 1)) = true :=
        bImp_true (fun h1 => decide_eq_true (by have := of_decide_eq_true h1; have := x2.isLt; omega))
      have hy' : bImp (decide (y1.val = 1)) (decide (y2.val = 1)) = true :=
        bImp_true (fun h1 => decide_eq_true (by have := of_decide_eq_true h1; have := y2.isLt; omega))
      simp [hx', hy']
    let eBridge : Equiv (OrderHom (chainProdLattice [2, 2]).toPoset (chainLattice (m + 1)).toPoset)
                        (SubSq2Hom top (m + 1)) :=
      { toFun := fun f =>
          { toFun := fun u _ => f.toFun (uToChain u)
            mono := fun u v _ _ huv => f.mono (hmono1 u v huv) }
        invFun := fun g =>
          { toFun := fun c => g.toFun (chainToU c) (htop (chainToU c))
            mono := fun {c1 c2} hc => g.mono _ _ _ _ (hmono2 c1 c2 hc) }
        left_inv := fun f => OrderHom.ext (fun c => by dsimp only []; rw [huc c])
        right_inv := fun g => SubSq2Hom.ext (fun ⟨u1, u2⟩ _ => by
          dsimp only []
          cases u1 <;> cases u2 <;> exact congrArg (g.toFun _) (Subsingleton.elim _ _)) }
    exact ⟨eBridge.trans ((subSq2HomFinEquiv m top).trans (Equiv.finCast (omegaSq_succ m)))⟩

/-- MacMahon's polynomial identity for `C_2 × C_2`:
    `12 * Ω(C_2 × C_2, m) = m * (m + 1)^2 * (m + 2)`. -/
theorem omegaSq_poly_identity (m : Nat) :
    12 * omegaSq m = m * (m + 1) * (m + 1) * (m + 2) := by
  let pLHS : Poly :=
    Poly.add (Poly.scale 12 (Poly.fallPoly 1))
    (Poly.add (Poly.scale 24 (Poly.fallPoly 2))
    (Poly.add (Poly.scale 10 (Poly.fallPoly 3))
              (Poly.scale 1  (Poly.fallPoly 4))))
  let pRHS : Poly :=
    Poly.mul [0, 1] (Poly.mul [1, 1] (Poly.mul [1, 1] [2, 1]))
  have hpoly : pLHS = pRHS := rfl
  let x : Int := (m : Int)
  have b1 := fallingProdInt_eq_fact_binom 1 m
  have b2 := fallingProdInt_eq_fact_binom 2 m
  have b3 := fallingProdInt_eq_fact_binom 3 m
  have b4 := fallingProdInt_eq_fact_binom 4 m
  simp only [fact] at b1 b2 b3 b4
  have hlhs : Poly.eval pLHS x = ((12 * omegaSq m : Nat) : Int) := by
    dsimp only [pLHS, x]
    simp only [Poly.eval_add, Poly.eval_scale, Poly.eval_fallPoly]
    rw [← b1, ← b2, ← b3, ← b4]
    simp only [omegaSq, natCast_add, natCast_mul]
    omega
  have hrhs : Poly.eval pRHS x = ((m * (m + 1) * (m + 1) * (m + 2) : Nat) : Int) := by
    dsimp only [pRHS, x]
    simp only [Poly.eval_mul, Poly.eval, natCast_mul, natCast_add]
    have h0 : (m : Int) * 0 = 0 := Int.mul_zero _
    have h1 : 0 + (m : Int) * (1 + 0) = (m : Int) := by omega
    have h2 : 1 + (m : Int) * (1 + 0) = (m : Int) + 1 := by omega
    have h3 : 2 + (m : Int) * (1 + 0) = (m : Int) + 2 := by omega
    rw [h0, h1, h2, h3]
    simp [Int.mul_assoc]
  have heq : ((12 * omegaSq m : Nat) : Int) = ((m * (m + 1) * (m + 1) * (m + 2) : Nat) : Int) := by
    have := congrArg (fun p => Poly.eval p x) hpoly
    dsimp only [] at this
    rw [hlhs, hrhs] at this
    exact this
  omega

/-- Positive witness 2 (`d = 2`, `C_2 × C_2`): `omegaSq` satisfies MacMahon's multinomial
    quotient formula `Ω(C_2 × C_2, m) = binom(m+1, 2) * binom(m+2, 2) / (binom(2,2) * binom(3,2))`. -/
theorem omegaSq_isMacMahonMultinomialQuotient : IsMacMahonMultinomialQuotient omegaSq := by
  let numSpecs : List PolyMultinomSpec :=
    [{ slope := 1, shift := 1, parts := [2] },
     { slope := 1, shift := 2, parts := [2] }]
  let denSpecs : List PolyMultinomSpec :=
    [{ slope := 0, shift := 2, parts := [2] },
     { slope := 0, shift := 3, parts := [2] }]
  refine ⟨1, numSpecs, denSpecs, ⟨1, Nat.le_refl 1, by decide⟩, ?_⟩
  intro m _
  have hid := omegaSq_poly_identity m
  dsimp only [numSpecs, denSpecs, evalSpecsDen, evalSpecsNum, evalSpecDen, evalSpecNum,
              listSum, prodFact, fact, fallingProdInt]
  have hidInt : (12 : Int) * (omegaSq m : Int) =
      (m : Int) * ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 2) := by
    have := congrArg (fun n : Nat => (n : Int)) hid
    simpa [natCast_mul, natCast_add] using this
  let x : Int := (m : Int)
  have e1 : 1 * x + 1 - (1 : Nat) = x := by dsimp [x]; omega
  have e2 : 1 * x + 1 - (0 : Nat) = x + 1 := by dsimp [x]; omega
  have e3 : 1 * x + 2 - (1 : Nat) = x + 1 := by dsimp [x]; omega
  have e4 : 1 * x + 2 - (0 : Nat) = x + 2 := by dsimp [x]; omega
  change (omegaSq m : Int) * ((2 * 1) * ((2 * 1) * 1)) *
      (((0 * x + 2 - (1 : Nat)) * ((0 * x + 2 - (0 : Nat)) * 1)) *
       (((0 * x + 3 - (1 : Nat)) * ((0 * x + 3 - (0 : Nat)) * 1)) * 1)) =
      ((2 * 1) * ((2 * 1) * 1)) *
      (((1 * x + 1 - (1 : Nat)) * ((1 * x + 1 - (0 : Nat)) * 1)) *
       (((1 * x + 2 - (1 : Nat)) * ((1 * x + 2 - (0 : Nat)) * 1)) * 1))
  rw [e1, e2, e3, e4]
  have d0 : ((0 * x + 2 - (1 : Nat)) * ((0 * x + 2 - (0 : Nat)) * 1)) *
      (((0 * x + 3 - (1 : Nat)) * ((0 * x + 3 - (0 : Nat)) * 1)) * 1) = 12 := by omega
  rw [d0]
  have hmul_rhs : (2 * 1 * (2 * 1 * 1) : Int) * (x * ((x + 1) * 1) * ((x + 1) * ((x + 2) * 1) * 1)) =
      4 * (x * (x + 1) * (x + 1) * (x + 2)) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hmul_rhs]
  dsimp only [x] at hidInt ⊢
  omega

/-! ## Section 6: Exact Order Polynomial of `C_2 × C_2 × C_2` for All `m : Nat` -/

abbrev Cube := Bool × Bool × Bool

def cubeLeBool (u v : Cube) : Bool :=
  bImp u.1 v.1 && bImp u.2.1 v.2.1 && bImp u.2.2 v.2.2

def cubeBit (u : Cube) : Nat :=
  (if u.1 then 4 else 0) + (if u.2.1 then 2 else 0) + (if u.2.2 then 1 else 0)

def cubeMaskNat : Nat → Nat
  | 0  => 0   | 1  => 1   | 2  => 3   | 3  => 5   | 4  => 7
  | 5  => 15  | 6  => 17  | 7  => 19  | 8  => 21  | 9  => 23
  | 10 => 31  | 11 => 51  | 12 => 55  | 13 => 63  | 14 => 85
  | 15 => 87  | 16 => 95  | 17 => 119 | 18 => 127 | 19 => 255
  | _  => 0

def inCubeIdealNat (idx : Nat) (u : Cube) : Bool :=
  decide (((cubeMaskNat idx) / pow2 (cubeBit u)) % 2 = 1)

def cubeIdealSubNat (j i : Nat) : Bool :=
  bImp (inCubeIdealNat j (false, false, false)) (inCubeIdealNat i (false, false, false)) &&
  bImp (inCubeIdealNat j (false, false, true))  (inCubeIdealNat i (false, false, true))  &&
  bImp (inCubeIdealNat j (false, true,  false)) (inCubeIdealNat i (false, true,  false)) &&
  bImp (inCubeIdealNat j (false, true,  true))  (inCubeIdealNat i (false, true,  true))  &&
  bImp (inCubeIdealNat j (true,  false, false)) (inCubeIdealNat i (true,  false, false)) &&
  bImp (inCubeIdealNat j (true,  false, true))  (inCubeIdealNat i (true,  false, true))  &&
  bImp (inCubeIdealNat j (true,  true,  false)) (inCubeIdealNat i (true,  true,  false)) &&
  bImp (inCubeIdealNat j (true,  true,  true))  (inCubeIdealNat i (true,  true,  true))

private theorem nat20_cases (n : Nat) (h : n < 20) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
    n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 := by
  omega

theorem inCubeIdealNat_downset (idx : Nat) (hidx : idx < 20) {u v : Cube}
    (huv : cubeLeBool u v = true) (hv : inCubeIdealNat idx v = true) :
    inCubeIdealNat idx u = true := by
  rcases u with ⟨u1, u2, u3⟩
  rcases v with ⟨v1, v2, v3⟩
  rcases nat20_cases idx hidx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases u1 <;> cases u2 <;> cases u3 <;>
    cases v1 <;> cases v2 <;> cases v3 <;>
    revert huv hv <;> decide

theorem cubeIdealSubNat_iff (j i : Nat) :
    cubeIdealSubNat j i = true ↔
      ∀ u : Cube, inCubeIdealNat j u = true → inCubeIdealNat i u = true := by
  constructor
  · intro hsub ⟨u1, u2, u3⟩
    unfold cubeIdealSubNat at hsub
    simp only [Bool.and_eq_true] at hsub
    rcases hsub with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    cases u1 <;> cases u2 <;> cases u3
    · revert h0; cases inCubeIdealNat j (false, false, false) <;> cases inCubeIdealNat i (false, false, false) <;> decide
    · revert h1; cases inCubeIdealNat j (false, false, true)  <;> cases inCubeIdealNat i (false, false, true)  <;> decide
    · revert h2; cases inCubeIdealNat j (false, true,  false) <;> cases inCubeIdealNat i (false, true,  false) <;> decide
    · revert h3; cases inCubeIdealNat j (false, true,  true)  <;> cases inCubeIdealNat i (false, true,  true)  <;> decide
    · revert h4; cases inCubeIdealNat j (true,  false, false) <;> cases inCubeIdealNat i (true,  false, false) <;> decide
    · revert h5; cases inCubeIdealNat j (true,  false, true)  <;> cases inCubeIdealNat i (true,  false, true)  <;> decide
    · revert h6; cases inCubeIdealNat j (true,  true,  false) <;> cases inCubeIdealNat i (true,  true,  false) <;> decide
    · revert h7; cases inCubeIdealNat j (true,  true,  true)  <;> cases inCubeIdealNat i (true,  true,  true)  <;> decide
  · intro hall
    unfold cubeIdealSubNat
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨bImp_true (hall _), bImp_true (hall _)⟩, bImp_true (hall _)⟩, bImp_true (hall _)⟩,
      bImp_true (hall _)⟩, bImp_true (hall _)⟩, bImp_true (hall _)⟩, bImp_true (hall _)⟩

def classifyCubeBools (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Nat :=
  if !b0 then 0
  else if b7 then 19
  else match b1, b2, b4 with
  | false, false, false => 1
  | true,  false, false => 2
  | false, true,  false => 3
  | false, false, true  => 6
  | true,  true,  false => if b3 then 5 else 4
  | true,  false, true  => if b5 then 11 else 7
  | false, true,  true  => if b6 then 14 else 8
  | true,  true,  true  =>
      match b3, b5, b6 with
      | false, false, false => 9
      | true,  false, false => 10
      | false, true,  false => 12
      | false, false, true  => 15
      | true,  true,  false => 13
      | true,  false, true  => 16
      | false, true,  true  => 17
      | true,  true,  true  => 18

theorem classifyCubeBools_lt (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    classifyCubeBools b0 b1 b2 b3 b4 b5 b6 b7 < 20 := by
  cases b0 <;> cases b7 <;> cases b1 <;> cases b2 <;> cases b4 <;>
    cases b3 <;> cases b5 <;> cases b6 <;> decide

def validCubeDownsetBools (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  bImp b1 b0 && bImp b2 b0 && bImp b4 b0 &&
  bImp b3 b1 && bImp b3 b2 &&
  bImp b5 b1 && bImp b5 b4 &&
  bImp b6 b2 && bImp b6 b4 &&
  bImp b7 b3 && bImp b7 b5 && bImp b7 b6

theorem classifyCubeBools_spec (b0 b1 b2 b3 b4 b5 b6 b7 : Bool)
    (hvalid : validCubeDownsetBools b0 b1 b2 b3 b4 b5 b6 b7 = true) :
    let idx := classifyCubeBools b0 b1 b2 b3 b4 b5 b6 b7
    inCubeIdealNat idx (false, false, false) = b0 ∧
    inCubeIdealNat idx (false, false, true)  = b1 ∧
    inCubeIdealNat idx (false, true,  false) = b2 ∧
    inCubeIdealNat idx (false, true,  true)  = b3 ∧
    inCubeIdealNat idx (true,  false, false) = b4 ∧
    inCubeIdealNat idx (true,  false, true)  = b5 ∧
    inCubeIdealNat idx (true,  true,  false) = b6 ∧
    inCubeIdealNat idx (true,  true,  true)  = b7 := by
  cases b0 <;> cases b7 <;> cases b1 <;> cases b2 <;> cases b4 <;>
    cases b3 <;> cases b5 <;> cases b6 <;> revert hvalid <;> decide

def classifyCubeDownset (S : Cube → Bool) : Fin 20 :=
  ⟨classifyCubeBools
    (S (false, false, false)) (S (false, false, true))
    (S (false, true,  false)) (S (false, true,  true))
    (S (true,  false, false)) (S (true,  false, true))
    (S (true,  true,  false)) (S (true,  true,  true)),
   classifyCubeBools_lt _ _ _ _ _ _ _ _⟩

theorem classifyCubeDownset_spec (S : Cube → Bool)
    (hS : ∀ u v : Cube, cubeLeBool u v = true → S v = true → S u = true) (u : Cube) :
    inCubeIdealNat (classifyCubeDownset S).val u = S u := by
  have hv : validCubeDownsetBools
      (S (false, false, false)) (S (false, false, true))
      (S (false, true,  false)) (S (false, true,  true))
      (S (true,  false, false)) (S (true,  false, true))
      (S (true,  true,  false)) (S (true,  true,  true)) = true := by
    unfold validCubeDownsetBools
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
      bImp_true (hS (false, false, false) (false, false, true)  rfl),
      bImp_true (hS (false, false, false) (false, true,  false) rfl)⟩,
      bImp_true (hS (false, false, false) (true,  false, false) rfl)⟩,
      bImp_true (hS (false, false, true)  (false, true,  true)  rfl)⟩,
      bImp_true (hS (false, true,  false) (false, true,  true)  rfl)⟩,
      bImp_true (hS (false, false, true)  (true,  false, true)  rfl)⟩,
      bImp_true (hS (true,  false, false) (true,  false, true)  rfl)⟩,
      bImp_true (hS (false, true,  false) (true,  true,  false) rfl)⟩,
      bImp_true (hS (true,  false, false) (true,  true,  false) rfl)⟩,
      bImp_true (hS (false, true,  true)  (true,  true,  true)  rfl)⟩,
      bImp_true (hS (true,  false, true)  (true,  true,  true)  rfl)⟩,
      bImp_true (hS (true,  true,  false) (true,  true,  true)  rfl)⟩
  have h8 := classifyCubeBools_spec _ _ _ _ _ _ _ _ hv
  rcases u with ⟨u1, u2, u3⟩
  cases u1 <;> cases u2 <;> cases u3
  · exact h8.1
  · exact h8.2.1
  · exact h8.2.2.1
  · exact h8.2.2.2.1
  · exact h8.2.2.2.2.1
  · exact h8.2.2.2.2.2.1
  · exact h8.2.2.2.2.2.2.1
  · exact h8.2.2.2.2.2.2.2

theorem classifyCubeIdeal_roundtrip (idx : Nat) (hidx : idx < 20) :
    classifyCubeBools
      (inCubeIdealNat idx (false, false, false)) (inCubeIdealNat idx (false, false, true))
      (inCubeIdealNat idx (false, true,  false)) (inCubeIdealNat idx (false, true,  true))
      (inCubeIdealNat idx (true,  false, false)) (inCubeIdealNat idx (true,  false, true))
      (inCubeIdealNat idx (true,  true,  false)) (inCubeIdealNat idx (true,  true,  true)) = idx := by
  rcases nat20_cases idx hidx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem cubeIdeal_injective {i j : Fin 20}
    (h : ∀ u : Cube, inCubeIdealNat i.val u = inCubeIdealNat j.val u) : i = j := by
  apply Fin.ext
  have hi := classifyCubeIdeal_roundtrip i.val i.isLt
  have hj := classifyCubeIdeal_roundtrip j.val j.isLt
  rw [← hi, ← hj, h (false, false, false), h (false, false, true),
      h (false, true, false), h (false, true, true),
      h (true, false, false), h (true, false, true),
      h (true, true, false), h (true, true, true)]

structure SubCubeHom (i : Fin 20) (m : Nat) where
  toFun : (u : Cube) → inCubeIdealNat i.val u = true → Fin m
  mono  : ∀ u v (hu : inCubeIdealNat i.val u = true) (hv : inCubeIdealNat i.val v = true),
            cubeLeBool u v = true → (toFun u hu).val ≤ (toFun v hv).val

theorem SubCubeHom.ext {i : Fin 20} {m : Nat} {f g : SubCubeHom i m}
    (h : ∀ u hu, f.toFun u hu = g.toFun u hu) : f = g := by
  cases f with | mk tf _ =>
  cases g with | mk tg _ =>
  dsimp only [] at h
  have hfun : tf = tg := funext (fun u => funext (fun hu => h u hu))
  subst hfun; rfl

def cubeCoeffsNat : Nat → List Nat
  | 0  => [1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1  => [1, 1, 0, 0, 0, 0, 0, 0, 0]
  | 2  => [1, 2, 1, 0, 0, 0, 0, 0, 0]
  | 3  => [1, 2, 1, 0, 0, 0, 0, 0, 0]
  | 4  => [1, 4, 5, 2, 0, 0, 0, 0, 0]
  | 5  => [1, 5, 9, 7, 2, 0, 0, 0, 0]
  | 6  => [1, 2, 1, 0, 0, 0, 0, 0, 0]
  | 7  => [1, 4, 5, 2, 0, 0, 0, 0, 0]
  | 8  => [1, 4, 5, 2, 0, 0, 0, 0, 0]
  | 9  => [1, 8, 19, 18, 6, 0, 0, 0, 0]
  | 10 => [1, 10, 32, 46, 31, 8, 0, 0, 0]
  | 11 => [1, 5, 9, 7, 2, 0, 0, 0, 0]
  | 12 => [1, 10, 32, 46, 31, 8, 0, 0, 0]
  | 13 => [1, 13, 57, 119, 130, 72, 16, 0, 0]
  | 14 => [1, 5, 9, 7, 2, 0, 0, 0, 0]
  | 15 => [1, 10, 32, 46, 31, 8, 0, 0, 0]
  | 16 => [1, 13, 57, 119, 130, 72, 16, 0, 0]
  | 17 => [1, 13, 57, 119, 130, 72, 16, 0, 0]
  | 18 => [1, 18, 111, 331, 540, 495, 240, 48, 0]
  | 19 => [1, 19, 129, 442, 871, 1035, 735, 288, 48]
  | _  => []

def getAt : List Nat → Nat → Nat
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, k + 1 => getAt cs k

def cubeCoeffNat (i k : Nat) : Nat := getAt (cubeCoeffsNat i) k

def cubeDpNat (i m : Nat) : Nat :=
  cubeCoeffNat i 0 * binom m 0 + cubeCoeffNat i 1 * binom m 1 + cubeCoeffNat i 2 * binom m 2 +
  cubeCoeffNat i 3 * binom m 3 + cubeCoeffNat i 4 * binom m 4 + cubeCoeffNat i 5 * binom m 5 +
  cubeCoeffNat i 6 * binom m 6 + cubeCoeffNat i 7 * binom m 7 + cubeCoeffNat i 8 * binom m 8

theorem cubeDpNat_zero (i : Fin 20) : cubeDpNat i.val 0 = 1 := by
  rcases i with ⟨iv, ilt⟩
  dsimp only []
  rcases nat20_cases iv ilt with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cube_coeff_rec (iv : Nat) (hiv : iv < 20) (kv : Nat) (hkv : kv < 9) :
    natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j kv else 0) =
      cubeCoeffNat iv kv + cubeCoeffNat iv (kv + 1) := by
  have hk : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 ∨ kv = 4 ∨ kv = 5 ∨ kv = 6 ∨ kv = 7 ∨ kv = 8 := by
    omega
  rcases nat20_cases iv hiv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem cubeDpNat_succ (i : Fin 20) (m : Nat) :
    natSum 20 (fun j => if cubeIdealSubNat j i.val then cubeDpNat j m else 0) =
      cubeDpNat i.val (m + 1) := by
  rcases i with ⟨iv, hiv⟩
  dsimp only []
  have h0 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 0 else 0) =
      cubeCoeffNat iv 0 + cubeCoeffNat iv 1 := cube_coeff_rec iv hiv 0 (by omega)
  have h1 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 1 else 0) =
      cubeCoeffNat iv 1 + cubeCoeffNat iv 2 := cube_coeff_rec iv hiv 1 (by omega)
  have h2 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 2 else 0) =
      cubeCoeffNat iv 2 + cubeCoeffNat iv 3 := cube_coeff_rec iv hiv 2 (by omega)
  have h3 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 3 else 0) =
      cubeCoeffNat iv 3 + cubeCoeffNat iv 4 := cube_coeff_rec iv hiv 3 (by omega)
  have h4 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 4 else 0) =
      cubeCoeffNat iv 4 + cubeCoeffNat iv 5 := cube_coeff_rec iv hiv 4 (by omega)
  have h5 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 5 else 0) =
      cubeCoeffNat iv 5 + cubeCoeffNat iv 6 := cube_coeff_rec iv hiv 5 (by omega)
  have h6 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 6 else 0) =
      cubeCoeffNat iv 6 + cubeCoeffNat iv 7 := cube_coeff_rec iv hiv 6 (by omega)
  have h7 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 7 else 0) =
      cubeCoeffNat iv 7 + cubeCoeffNat iv 8 := cube_coeff_rec iv hiv 7 (by omega)
  have h8 : natSum 20 (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 8 else 0) =
      cubeCoeffNat iv 8 + cubeCoeffNat iv 9 := cube_coeff_rec iv hiv 8 (by omega)
  have hc9 : cubeCoeffNat iv 9 = 0 := by
    rcases nat20_cases iv hiv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hc9, Nat.add_zero] at h8
  have hlin : ∀ n : Nat,
      natSum n (fun j => if cubeIdealSubNat j iv then cubeDpNat j m else 0) =
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 0 else 0) * binom m 0 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 1 else 0) * binom m 1 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 2 else 0) * binom m 2 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 3 else 0) * binom m 3 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 4 else 0) * binom m 4 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 5 else 0) * binom m 5 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 6 else 0) * binom m 6 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 7 else 0) * binom m 7 +
      natSum n (fun j => if cubeIdealSubNat j iv then cubeCoeffNat j 8 else 0) * binom m 8 := by
    intro n
    induction n with
    | zero => simp [natSum]
    | succ n ih =>
      simp only [natSum, ih, Nat.add_mul]
      cases cubeIdealSubNat n iv <;> simp [cubeDpNat] <;> omega
  rw [hlin 20, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [cubeDpNat, binom_zero, binom_succ_one, binom_succ_two, binom_succ_three,
             binom_succ_four, binom_succ_five, binom_succ_six, binom_succ_seven,
             binom_succ_eight, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def extendSubCubeHom (j i : Fin 20) (m : Nat) (g : SubCubeHom j (m + 1)) : SubCubeHom i (m + 2) where
  toFun u _ :=
    if hju : inCubeIdealNat j.val u = true then
      ⟨(g.toFun u hju).val, by have := (g.toFun u hju).isLt; omega⟩
    else
      ⟨m + 1, by omega⟩
  mono u v _ _ huv := by
    by_cases hjv : inCubeIdealNat j.val v = true
    · have hju : inCubeIdealNat j.val u = true := inCubeIdealNat_downset j.val j.isLt huv hjv
      rw [dif_pos hju, dif_pos hjv]
      exact g.mono u v hju hjv huv
    · by_cases hju : inCubeIdealNat j.val u = true
      · rw [dif_pos hju, dif_neg hjv]
        dsimp only []
        have := (g.toFun u hju).isLt
        omega
      · rw [dif_neg hju, dif_neg hjv]
        exact Nat.le_refl _

theorem sigmaSubCube_ext {i j' j : Fin 20} {m : Nat}
    {x' : BoolFiber (cubeIdealSubNat j'.val i.val) (SubCubeHom j' (m + 1))}
    {x  : BoolFiber (cubeIdealSubNat j.val i.val)  (SubCubeHom j (m + 1))}
    (hj : j' = j)
    (hx : ∀ (u : Cube) (hju' : inCubeIdealNat j'.val u = true) (hju : inCubeIdealNat j.val u = true),
            (x'.val.toFun u hju').val = (x.val.toFun u hju).val) :
    (⟨j', x'⟩ : (k : Fin 20) × BoolFiber (cubeIdealSubNat k.val i.val) (SubCubeHom k (m + 1))) = ⟨j, x⟩ := by
  subst hj
  rcases x' with ⟨h1, g1⟩
  rcases x with ⟨h2, g2⟩
  have hh : h1 = h2 := Subsingleton.elim _ _
  subst hh
  congr 1
  congr 1
  apply SubCubeHom.ext
  intro u hu
  exact Fin.ext (hx u hu hu)

def subCubeHomStepEquiv (i : Fin 20) (m : Nat) :
    Equiv (SubCubeHom i (m + 2))
          ((j : Fin 20) × BoolFiber (cubeIdealSubNat j.val i.val) (SubCubeHom j (m + 1))) where
  toFun f :=
    let S : Cube → Bool := fun u =>
      if hu : inCubeIdealNat i.val u = true then decide ((f.toFun u hu).val < m + 1) else false
    have hS : ∀ u v : Cube, cubeLeBool u v = true → S v = true → S u = true := by
      intro u v huv hv
      dsimp only [S] at hv ⊢
      split at hv
      · rename_i hvi
        have hui := inCubeIdealNat_downset i.val i.isLt huv hvi
        simp only [hui, ↓reduceDIte]
        have hlt := of_decide_eq_true hv
        have hle := f.mono u v hui hvi huv
        exact decide_eq_true (by omega)
      · contradiction
    let j := classifyCubeDownset S
    have hjS : ∀ u, inCubeIdealNat j.val u = S u := classifyCubeDownset_spec S hS
    have hsub : cubeIdealSubNat j.val i.val = true := (cubeIdealSubNat_iff j.val i.val).mpr (fun u hju => by
      rw [hjS u] at hju
      dsimp only [S] at hju
      split at hju
      · assumption
      · contradiction)
    ⟨j, ⟨hsub, {
      toFun := fun u hju =>
        have hui := (cubeIdealSubNat_iff j.val i.val).mp hsub u hju
        have hStrue : S u = true := by rw [← hjS u]; exact hju
        have hlt : (f.toFun u hui).val < m + 1 := by
          dsimp only [S] at hStrue; simp only [hui, ↓reduceDIte] at hStrue
          exact of_decide_eq_true hStrue
        ⟨(f.toFun u hui).val, hlt⟩
      mono := fun u v hju hjv huv =>
        f.mono u v ((cubeIdealSubNat_iff j.val i.val).mp hsub u hju)
                   ((cubeIdealSubNat_iff j.val i.val).mp hsub v hjv) huv }⟩⟩
  invFun p := extendSubCubeHom p.1 i m p.2.val
  left_inv f := SubCubeHom.ext (fun u hui => by
    dsimp only [extendSubCubeHom]
    split
    · rfl
    · rename_i hnot
      let S : Cube → Bool := fun w =>
        if hw : inCubeIdealNat i.val w = true then decide ((f.toFun w hw).val < m + 1) else false
      have hS : ∀ w1 w2 : Cube, cubeLeBool w1 w2 = true → S w2 = true → S w1 = true := by
        intro w1 w2 hw12 hw2
        dsimp only [S] at hw2 ⊢
        split at hw2
        · rename_i hw2i
          have hw1i := inCubeIdealNat_downset i.val i.isLt hw12 hw2i
          simp only [hw1i, ↓reduceDIte]
          have hlt := of_decide_eq_true hw2
          have hle := f.mono w1 w2 hw1i hw2i hw12
          exact decide_eq_true (by omega)
        · contradiction
      have hspec := classifyCubeDownset_spec S hS u
      have hSu_false : S u = false := by
        cases hSu : S u with
        | false => rfl
        | true => rw [hSu] at hspec; exact absurd hspec hnot
      dsimp only [S] at hSu_false
      simp only [hui, ↓reduceDIte] at hSu_false
      have hge : ¬ ((f.toFun u hui).val < m + 1) := of_decide_eq_false hSu_false
      have hval := (f.toFun u hui).isLt
      exact Fin.ext (by dsimp only []; omega))
  right_inv p := by
    rcases p with ⟨j, ⟨hsub, g⟩⟩
    let f := extendSubCubeHom j i m g
    let S : Cube → Bool := fun u =>
      if hu : inCubeIdealNat i.val u = true then decide ((f.toFun u hu).val < m + 1) else false
    have hS : ∀ u v : Cube, cubeLeBool u v = true → S v = true → S u = true := by
      intro u v huv hv
      dsimp only [S] at hv ⊢
      split at hv
      · rename_i hvi
        have hui := inCubeIdealNat_downset i.val i.isLt huv hvi
        simp only [hui, ↓reduceDIte]
        have hlt := of_decide_eq_true hv
        have hle := f.mono u v hui hvi huv
        exact decide_eq_true (by omega)
      · contradiction
    have hSj : ∀ u : Cube, S u = inCubeIdealNat j.val u := by
      intro u
      dsimp only [S, f, extendSubCubeHom]
      by_cases hju : inCubeIdealNat j.val u = true
      · have hui := (cubeIdealSubNat_iff j.val i.val).mp hsub u hju
        rw [dif_pos hui, dif_pos hju, hju]
        dsimp only []
        exact decide_eq_true (g.toFun u hju).isLt
      · have hjf : inCubeIdealNat j.val u = false :=
          Bool.eq_false_iff.mpr hju
        by_cases hui : inCubeIdealNat i.val u = true
        · rw [dif_pos hui, dif_neg hju, hjf]
          dsimp only []
          exact decide_eq_false (Nat.lt_irrefl _)
        · rw [dif_neg hui, hjf]
    have hjeq : classifyCubeDownset S = j :=
      cubeIdeal_injective (fun u => (classifyCubeDownset_spec S hS u).trans (hSj u))
    refine sigmaSubCube_ext hjeq (fun u _ hju => ?_)
    dsimp only [f, extendSubCubeHom]
    rw [dif_pos hju]

def subCubeHomFinEquiv : (m : Nat) → (i : Fin 20) →
    Equiv (SubCubeHom i (m + 1)) (Fin (cubeDpNat i.val m))
  | 0, i =>
    { toFun := fun _ => ⟨0, by rw [cubeDpNat_zero]; exact Nat.zero_lt_one⟩
      invFun := fun _ => { toFun := fun _ _ => ⟨0, Nat.zero_lt_one⟩, mono := fun _ _ _ _ _ => Nat.le_refl 0 }
      left_inv := fun f => SubCubeHom.ext (fun u hu => Fin.ext (by have := (f.toFun u hu).isLt; omega))
      right_inv := fun k => Fin.ext (by
        have hklt : k.val < 1 := Nat.lt_of_lt_of_eq k.isLt (cubeDpNat_zero i)
        dsimp only []; omega) }
  | m + 1, i =>
    let w : Nat → Nat := fun j => if cubeIdealSubNat j i.val then cubeDpNat j m else 0
    let eFib : (j : Fin 20) →
        Equiv (BoolFiber (cubeIdealSubNat j.val i.val) (SubCubeHom j (m + 1))) (Fin (w j.val)) :=
      fun j => boolFiberEquiv (cubeIdealSubNat j.val i.val) (fun _ => subCubeHomFinEquiv m j)
    let eSigma : Equiv ((j : Fin 20) × BoolFiber (cubeIdealSubNat j.val i.val) (SubCubeHom j (m + 1)))
                       ((j : Fin 20) × Fin (w j.val)) :=
      { toFun := fun ⟨j, x⟩ => ⟨j, (eFib j).toFun x⟩
        invFun := fun ⟨j, y⟩ => ⟨j, (eFib j).invFun y⟩
        left_inv := fun ⟨j, x⟩ => by simp [(eFib j).left_inv]
        right_inv := fun ⟨j, y⟩ => by simp [(eFib j).right_inv] }
    (subCubeHomStepEquiv i m).trans
      (eSigma.trans ((sigmaNatFinEquiv 20 w).trans (Equiv.finCast (cubeDpNat_succ i m))))

/-- Exact order polynomial of the 3-chain cube lattice `C_2 × C_2 × C_2` in the binomial basis:
    `Ω(C_2^3, m) = binom m 1 + 18*binom m 2 + 111*binom m 3 + 331*binom m 4 +
                   540*binom m 5 + 495*binom m 6 + 240*binom m 7 + 48*binom m 8`. -/
def omegaCube (m : Nat) : Nat :=
  binom m 1 + 18 * binom m 2 + 111 * binom m 3 + 331 * binom m 4 +
  540 * binom m 5 + 495 * binom m 6 + 240 * binom m 7 + 48 * binom m 8

theorem omegaCube_succ (m : Nat) : cubeDpNat 19 m = omegaCube (m + 1) := by
  simp only [cubeDpNat, cubeCoeffNat, cubeCoeffsNat, getAt, omegaCube, binom_zero,
             binom_succ_one, binom_succ_two, binom_succ_three, binom_succ_four,
             binom_succ_five, binom_succ_six, binom_succ_seven, binom_succ_eight,
             Nat.mul_add, Nat.mul_one]
  omega

/-- Universal exact cardinality theorem for `C_2 × C_2 × C_2`:
    For EVERY `m : Nat`, `OrderHom (C_2 × C_2 × C_2) C_m` has cardinality `omegaCube m`. -/
theorem omegaCube_card (m : Nat) :
    HasCard (OrderHom (chainProdLattice [2, 2, 2]).toPoset (chainLattice m).toPoset)
            (omegaCube m) := by
  cases m with
  | zero =>
    refine ⟨{
      toFun := fun f => f.toFun (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ .nil)))
      invFun := fun k => Fin.elim0 k
      left_inv := fun f => Fin.elim0 (f.toFun (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ (.cons ⟨0, by omega⟩ .nil))))
      right_inv := fun k => Fin.elim0 k }⟩
  | succ m =>
    let top : Fin 20 := ⟨19, by omega⟩
    have htop : ∀ u : Cube, inCubeIdealNat 19 u = true := by
      intro ⟨u1, u2, u3⟩; cases u1 <;> cases u2 <;> cases u3 <;> decide
    let b2fin : Bool → Fin 2 := fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
    let fin2b : Fin 2 → Bool := fun x => decide (x.val = 1)
    let uToChain : Cube → ChainProd [2, 2, 2] := fun u =>
      .cons (b2fin u.1) (.cons (b2fin u.2.1) (.cons (b2fin u.2.2) .nil))
    let chainToU : ChainProd [2, 2, 2] → Cube := fun c =>
      match c with | .cons x (.cons y (.cons z .nil)) => (fin2b x, fin2b y, fin2b z)
    have hcu : ∀ u : Cube, chainToU (uToChain u) = u := by
      intro ⟨u1, u2, u3⟩; cases u1 <;> cases u2 <;> cases u3 <;> rfl
    have huc : ∀ c : ChainProd [2, 2, 2], uToChain (chainToU c) = c := by
      intro c
      cases c with | cons x r1 => cases r1 with | cons y r2 => cases r2 with | cons z r3 =>
      cases r3 with | nil =>
      rcases x with ⟨xv, xlt⟩; rcases y with ⟨yv, ylt⟩; rcases z with ⟨zv, zlt⟩
      have hx : xv = 0 ∨ xv = 1 := by omega
      have hy : yv = 0 ∨ yv = 1 := by omega
      have hz : zv = 0 ∨ zv = 1 := by omega
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> rfl
    have hmono1 : ∀ u v : Cube, cubeLeBool u v = true →
        (chainProdLattice [2, 2, 2]).le (uToChain u) (uToChain v) := by
      intro ⟨u1, u2, u3⟩ ⟨v1, v2, v3⟩ huv
      cases u1 <;> cases u2 <;> cases u3 <;>
        cases v1 <;> cases v2 <;> cases v3 <;>
        simp [cubeLeBool, bImp, uToChain, b2fin, chainProdLattice, ChainProd.le] at huv ⊢
    have hmono2 : ∀ c1 c2 : ChainProd [2, 2, 2],
        (chainProdLattice [2, 2, 2]).le c1 c2 → cubeLeBool (chainToU c1) (chainToU c2) = true := by
      intro c1 c2 hc
      cases c1 with | cons x1 r1 => cases r1 with | cons y1 r2 => cases r2 with | cons z1 n1 => cases n1 with | nil =>
      cases c2 with | cons x2 s1 => cases s1 with | cons y2 s2 => cases s2 with | cons z2 n2 => cases n2 with | nil =>
      rcases hc with ⟨hx, hy, hz, _⟩
      dsimp only [chainToU, fin2b, cubeLeBool]
      have hx' : bImp (decide (x1.val = 1)) (decide (x2.val = 1)) = true :=
        bImp_true (fun h1 => decide_eq_true (by have := of_decide_eq_true h1; have := x2.isLt; omega))
      have hy' : bImp (decide (y1.val = 1)) (decide (y2.val = 1)) = true :=
        bImp_true (fun h1 => decide_eq_true (by have := of_decide_eq_true h1; have := y2.isLt; omega))
      have hz' : bImp (decide (z1.val = 1)) (decide (z2.val = 1)) = true :=
        bImp_true (fun h1 => decide_eq_true (by have := of_decide_eq_true h1; have := z2.isLt; omega))
      simp [hx', hy', hz']
    let eBridge : Equiv (OrderHom (chainProdLattice [2, 2, 2]).toPoset (chainLattice (m + 1)).toPoset)
                        (SubCubeHom top (m + 1)) :=
      { toFun := fun f =>
          { toFun := fun u _ => f.toFun (uToChain u)
            mono := fun u v _ _ huv => f.mono (hmono1 u v huv) }
        invFun := fun g =>
          { toFun := fun c => g.toFun (chainToU c) (htop (chainToU c))
            mono := fun {c1 c2} hc => g.mono _ _ _ _ (hmono2 c1 c2 hc) }
        left_inv := fun f => OrderHom.ext (fun c => by dsimp only []; rw [huc c])
        right_inv := fun g => SubCubeHom.ext (fun ⟨u1, u2, u3⟩ _ => by
          dsimp only []
          cases u1 <;> cases u2 <;> cases u3 <;>
            exact congrArg (g.toFun _) (Subsingleton.elim _ _)) }
    exact ⟨eBridge.trans ((subCubeHomFinEquiv m top).trans (Equiv.finCast (omegaCube_succ m)))⟩

/-- Exact factored polynomial formula for `1680 * Ω(C_2 × C_2 × C_2, m)`:
    `1680 * omegaCube m = m(m+1)(m+2)(m+3)(2m^4 + 12m^3 + 25m^2 + 21m + 10)`. -/
def cubeQuarticNat (m : Nat) : Nat :=
  2 * (m * m * m * m) + 12 * (m * m * m) + 25 * (m * m) + 21 * m + 10

def cubeQuarticInt (x : Int) : Int :=
  2 * (x * x * x * x) + 12 * (x * x * x) + 25 * (x * x) + 21 * x + 10

theorem omegaCube_poly_identity (m : Nat) :
    1680 * omegaCube m = m * (m + 1) * (m + 2) * (m + 3) * cubeQuarticNat m := by
  let pLHS24 : Poly :=
    Poly.add (Poly.scale (24 * 1680)            (Poly.fallPoly 1))
    (Poly.add (Poly.scale (24 * 1680 * 18 / 2)   (Poly.fallPoly 2))
    (Poly.add (Poly.scale (24 * 1680 * 111 / 6)  (Poly.fallPoly 3))
    (Poly.add (Poly.scale (24 * 1680 * 331 / 24) (Poly.fallPoly 4))
    (Poly.add (Poly.scale (24 * 1680 * 540 / 120) (Poly.fallPoly 5))
    (Poly.add (Poly.scale (24 * 1680 * 495 / 720) (Poly.fallPoly 6))
    (Poly.add (Poly.scale (24 * 1680 * 240 / 5040) (Poly.fallPoly 7))
              (Poly.scale (24 * 1680 * 48 / 40320) (Poly.fallPoly 8))))))))
  let pRHS24 : Poly :=
    Poly.scale 24 (Poly.mul [0, 1] (Poly.mul [1, 1] (Poly.mul [2, 1] (Poly.mul [3, 1] [10, 21, 25, 12, 2]))))
  have hpoly : pLHS24 = pRHS24 := rfl
  let x : Int := (m : Int)
  have b1 := fallingProdInt_eq_fact_binom 1 m
  have b2 := fallingProdInt_eq_fact_binom 2 m
  have b3 := fallingProdInt_eq_fact_binom 3 m
  have b4 := fallingProdInt_eq_fact_binom 4 m
  have b5 := fallingProdInt_eq_fact_binom 5 m
  have b6 := fallingProdInt_eq_fact_binom 6 m
  have b7 := fallingProdInt_eq_fact_binom 7 m
  have b8 := fallingProdInt_eq_fact_binom 8 m
  simp only [fact] at b1 b2 b3 b4 b5 b6 b7 b8
  have hlhs : Poly.eval pLHS24 x = (24 : Int) * ((1680 * omegaCube m : Nat) : Int) := by
    dsimp only [pLHS24, x]
    simp only [Poly.eval_add, Poly.eval_scale, Poly.eval_fallPoly]
    rw [← b1, ← b2, ← b3, ← b4, ← b5, ← b6, ← b7, ← b8]
    simp only [omegaCube, natCast_add, natCast_mul]
    omega
  have hquart : Poly.eval [10, 21, 25, 12, 2] (m : Int) = (cubeQuarticNat m : Int) := by
    simp only [Poly.eval, cubeQuarticNat, natCast_add, natCast_mul]
    have h0 : (m : Int) * 0 = 0 := Int.mul_zero _
    rw [h0]
    simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
          Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have hrhs : Poly.eval pRHS24 x =
      (24 : Int) * ((m * (m + 1) * (m + 2) * (m + 3) * cubeQuarticNat m : Nat) : Int) := by
    dsimp only [pRHS24, x]
    rw [Poly.eval_scale]
    simp only [Poly.eval_mul, hquart]
    have e0 : Poly.eval [0, 1] (m : Int) = (m : Int) := by simp [Poly.eval]
    have e1 : Poly.eval [1, 1] (m : Int) = (m : Int) + 1 := by simp [Poly.eval]; omega
    have e2 : Poly.eval [2, 1] (m : Int) = (m : Int) + 2 := by simp [Poly.eval]; omega
    have e3 : Poly.eval [3, 1] (m : Int) = (m : Int) + 3 := by simp [Poly.eval]; omega
    rw [e0, e1, e2, e3]
    simp [natCast_mul, natCast_add, Int.mul_assoc]
  have heq24 : (24 : Int) * ((1680 * omegaCube m : Nat) : Int) =
      (24 : Int) * ((m * (m + 1) * (m + 2) * (m + 3) * cubeQuarticNat m : Nat) : Int) := by
    have := congrArg (fun p => Poly.eval p x) hpoly
    dsimp only [] at this
    rw [hlhs, hrhs] at this
    exact this
  omega

/-! ## Section 7: Algebraic Non-Splitting Disproof of Order-Polynomial Conjecture -/

/-- Bivariate polynomial ring `Int[g][z]` for constructive verification of bivariate identities. -/
abbrev Poly2 := List Poly

namespace Poly2

def eval2 : Poly2 → Int → Int → Int
  | [], _, _ => 0
  | c :: cs, g, z => Poly.eval c g + z * eval2 cs g z

def add : Poly2 → Poly2 → Poly2
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => Poly.add c d :: add cs ds

def scale1 (k : Poly) : Poly2 → Poly2
  | [] => []
  | c :: cs => Poly.mul k c :: scale1 k cs

def mul : Poly2 → Poly2 → Poly2
  | [], _ => []
  | c :: cs, q => add (scale1 c q) ([] :: mul cs q)

theorem eval2_add : ∀ (p q : Poly2) (g z : Int),
    eval2 (add p q) g z = eval2 p g z + eval2 q g z
  | [], q, g, z => by simp [add, eval2]
  | c :: cs, [], g, z => by simp [add, eval2]
  | c :: cs, d :: ds, g, z => by
    simp only [add, eval2, Poly.eval_add, eval2_add cs ds g z, Int.mul_add]
    omega

theorem eval2_scale1 (k : Poly) : ∀ (p : Poly2) (g z : Int),
    eval2 (scale1 k p) g z = Poly.eval k g * eval2 p g z
  | [], _, _ => by simp [scale1, eval2]
  | c :: cs, g, z => by
    simp only [scale1, eval2, Poly.eval_mul, eval2_scale1 k cs g z, Int.mul_add]
    have : z * (Poly.eval k g * eval2 cs g z) = Poly.eval k g * (z * eval2 cs g z) := by
      simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega

theorem eval2_mul : ∀ (p q : Poly2) (g z : Int),
    eval2 (mul p q) g z = eval2 p g z * eval2 q g z
  | [], _, _, _ => by simp [mul, eval2]
  | c :: cs, q, g, z => by
    simp only [mul, eval2, eval2_add, eval2_scale1, eval2_mul cs q g z, Poly.eval, Int.add_mul]
    have : z * (eval2 cs g z * eval2 q g z) = (z * eval2 cs g z) * eval2 q g z := by
      simp [Int.mul_assoc]
    omega

end Poly2

def homQuartic (g z : Int) : Int :=
  2 * z * z * z * z + 12 * g * z * z * z + 25 * g * g * z * z +
  21 * g * g * g * z + 10 * g * g * g * g

/-- Sum-of-squares completion of the homogenized quartic:
    `8 * homQuartic(g, z) = (4z^2 + 12gz + 7g^2)^2 + 31g^4`. -/
theorem homQuartic_sos_identity (g z : Int) :
    8 * homQuartic g z =
      (4 * z * z + 12 * g * z + 7 * g * g) * (4 * z * z + 12 * g * z + 7 * g * g) +
      31 * g * g * g * g := by
  let q2 : Poly2 := [[0, 0, 0, 0, 10], [0, 0, 0, 21], [0, 0, 25], [0, 12], [2]]
  let s2 : Poly2 := [[0, 0, 7], [0, 12], [4]]
  let lhsP : Poly2 := Poly2.scale1 [8] q2
  let rhsP : Poly2 := Poly2.add (Poly2.mul s2 s2) [[0, 0, 0, 0, 31]]
  have hpoly : lhsP = rhsP := rfl
  have hev := congrArg (fun P => Poly2.eval2 P g z) hpoly
  have h1 : Poly2.eval2 lhsP g z = 8 * homQuartic g z := by
    dsimp only [lhsP, q2]
    rw [Poly2.eval2_scale1]
    simp only [Poly2.eval2, Poly.eval, homQuartic]
    simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
          Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have h2 : Poly2.eval2 s2 g z = 4 * z * z + 12 * g * z + 7 * g * g := by
    dsimp only [s2]
    simp only [Poly2.eval2, Poly.eval]
    simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
          Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have h3 : Poly2.eval2 [[0, 0, 0, 0, 31]] g z = 31 * g * g * g * g := by
    simp only [Poly2.eval2, Poly.eval]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  dsimp only [rhsP] at hev
  rw [h1, Poly2.eval2_add, Poly2.eval2_mul, h2, h3] at hev
  exact hev

theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hmul := Int.mul_nonneg hn hn
    simpa [Int.neg_mul, Int.mul_neg, Int.neg_neg] using hmul

/-- Strict positivity: for every `g ≠ 0` and every `z : Int`, `homQuartic g z > 0` (hence `≠ 0`). -/
theorem homQuartic_pos {g : Int} (hg : g ≠ 0) (z : Int) : 0 < homQuartic g z := by
  let S : Int := 4 * z * z + 12 * g * z + 7 * g * g
  let G4 : Int := g * g * g * g
  have hsos : 8 * homQuartic g z = S * S + 31 * G4 := by
    have h0 := homQuartic_sos_identity g z
    have h31 : 31 * g * g * g * g = 31 * G4 := by simp [G4, Int.mul_assoc]
    dsimp only [S]
    rw [h0, h31]
  have hsq1 : 0 ≤ S * S := sq_nonneg S
  have hg2_pos : 1 ≤ g * g := by
    have h0 := sq_nonneg g
    by_cases heq : g * g = 0
    · cases Int.mul_eq_zero.mp heq with | inl h => exact absurd h hg | inr h => exact absurd h hg
    · omega
  have hg4_pos : 1 ≤ G4 := by
    have hmul := Int.mul_le_mul hg2_pos hg2_pos (by omega) (by omega)
    have hrew : (g * g) * (g * g) = G4 := by simp [G4, Int.mul_assoc]
    rw [hrew] at hmul
    omega
  have h31 : 31 * 1 ≤ 31 * G4 :=
    Int.mul_le_mul_of_nonneg_left hg4_pos (by omega)
  omega

def homLinPolyList (g : Int) : List (Int × Int) → Poly
  | [] => [1]
  | (a, b) :: rest => Poly.mul [b * g, a] (homLinPolyList g rest)

def powInt (g : Int) : Nat → Int
  | 0 => 1
  | n + 1 => g * powInt g n

theorem powInt_add (g : Int) : ∀ (a b : Nat), powInt g (a + b) = powInt g a * powInt g b
  | 0, _ => by simp [powInt]
  | a + 1, b => by simp [Nat.succ_add, powInt, powInt_add g a b, Int.mul_assoc]

theorem powInt_ne_zero {g : Int} (hg : g ≠ 0) : (n : Nat) → powInt g n ≠ 0
  | 0 => by simp [powInt]
  | n + 1 => fun h => by
    cases Int.mul_eq_zero.mp h with
    | inl h1 => exact hg h1
    | inr h2 => exact powInt_ne_zero hg n h2

theorem homLinPolyList_eval_mul (g x : Int) : (ls : List (Int × Int)) →
    Poly.eval (homLinPolyList g ls) (g * x) = powInt g ls.length * linListEval ls x
  | [] => by simp [homLinPolyList, Poly.eval, powInt, linListEval]
  | (a, b) :: rest => by
    simp only [homLinPolyList, Poly.eval_mul, Poly.eval, List.length_cons, powInt, linListEval]
    rw [homLinPolyList_eval_mul g x rest]
    have h1 : b * g + g * x * (a + g * x * 0) = g * (a * x + b) := by
      have : g * x * 0 = 0 := Int.mul_zero _
      rw [this, Int.add_zero]
      calc b * g + g * x * a
        _ = g * (a * x) + g * b := by
              rw [Int.add_comm]
              simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ = g * (a * x + b) := (Int.mul_add _ _ _).symm
    rw [h1]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem homLinPolyList_zero_iff (g z : Int) : (ls : List (Int × Int)) →
    Poly.eval (homLinPolyList g ls) z = 0 → ∃ p ∈ ls, p.1 * z + p.2 * g = 0
  | [], h => by simp [homLinPolyList, Poly.eval] at h
  | (a, b) :: rest, h => by
    simp only [homLinPolyList, Poly.eval_mul] at h
    cases Int.mul_eq_zero.mp h with
    | inl hhd =>
      refine ⟨(a, b), List.Mem.head _, ?_⟩
      dsimp only []
      simp only [Poly.eval] at hhd
      have hz0 : z * 0 = 0 := Int.mul_zero z
      rw [hz0, Int.add_zero] at hhd
      have hcomm : z * a = a * z := Int.mul_comm z a
      omega
    | inr htl =>
      rcases homLinPolyList_zero_iff g z rest htl with ⟨p, hp, hp0⟩
      exact ⟨p, List.Mem.tail _ hp, hp0⟩

theorem homLinPolyList_eval_zero_of_mem (g z a b : Int) :
    ∀ (ls : List (Int × Int)), (a, b) ∈ ls → a * z + b * g = 0 →
      Poly.eval (homLinPolyList g ls) z = 0
  | [], hmem, _ => nomatch hmem
  | (a', b') :: tl, hmem, hroot => by
    cases hmem with
    | head =>
      simp only [homLinPolyList, Poly.eval_mul, Poly.eval]
      have hz0 : z * 0 = 0 := Int.mul_zero z
      rw [hz0, Int.add_zero]
      have hcomm : z * a = a * z := Int.mul_comm z a
      have hzero : b * g + z * a = 0 := by omega
      rw [hzero, Int.zero_mul]
    | tail _ htl =>
      simp only [homLinPolyList, Poly.eval_mul,
                 homLinPolyList_eval_zero_of_mem g z a b tl htl hroot, Int.mul_zero]

theorem linListEval_const_of_slope_zero :
    ∀ (ls : List (Int × Int)), (∀ p ∈ ls, p.1 = 0) →
      ∀ x y : Int, linListEval ls x = linListEval ls y
  | [], _, _, _ => rfl
  | (a, b) :: tl, hall, x, y => by
    have ha : a = 0 := hall (a, b) (List.Mem.head _)
    subst ha
    simp [linListEval, linListEval_const_of_slope_zero tl (fun p hp => hall p (List.Mem.tail _ hp)) x y]

theorem linListEval_nz_of_slope_zero :
    ∀ (ls : List (Int × Int)), (∀ p ∈ ls, p.1 = 0 ∧ p.2 ≠ 0) →
      ∀ x : Int, linListEval ls x ≠ 0
  | [], _, _ => by simp [linListEval]
  | (a, b) :: tl, hall, x => by
    rcases hall (a, b) (List.Mem.head _) with ⟨rfl, hb⟩
    simp only [linListEval, Int.zero_mul, Int.zero_add]
    intro hmul
    cases Int.mul_eq_zero.mp hmul with
    | inl h => exact hb h
    | inr h => exact linListEval_nz_of_slope_zero tl (fun p hp => hall p (List.Mem.tail _ hp)) x h

def homQuarticPoly (g : Int) : Poly :=
  [10 * g * g * g * g, 21 * g * g * g, 25 * g * g, 12 * g, 2]

theorem homQuarticPoly_eval (g z : Int) :
    Poly.eval (homQuarticPoly g) z = homQuartic g z := by
  simp only [homQuarticPoly, Poly.eval, homQuartic]
  have : z * 0 = 0 := Int.mul_zero z
  rw [this]
  simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
        Int.add_assoc, Int.add_comm, Int.add_left_comm]

theorem homQuartic_scale (g x : Int) :
    homQuartic g (g * x) = powInt g 4 * cubeQuarticInt x := by
  simp only [homQuartic, powInt, cubeQuarticInt]
  simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Removing one matching element from a list to factor it out. -/
theorem extract_mem {α : Type} [DecidableEq α] : ∀ (ls : List α) {x : α},
    x ∈ ls → ∃ rest : List α, (∀ a ∈ rest, a ∈ ls) ∧
      ∀ (f : α → Int),
        (ls.foldr (fun a acc => f a * acc) 1) = f x * (rest.foldr (fun a acc => f a * acc) 1)
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    by_cases hxy : x = y
    · subst hxy
      exact ⟨ys, fun _ ha => List.Mem.tail _ ha, fun _ => rfl⟩
    · cases h with
      | head => exact absurd rfl hxy
      | tail _ hmem =>
        rcases extract_mem ys hmem with ⟨rest, hsub, hprod⟩
        refine ⟨y :: rest, fun a ha => ?_, fun f => ?_⟩
        · cases ha with
          | head => exact List.Mem.head _
          | tail _ hmem' => exact List.Mem.tail _ (hsub a hmem')
        · simp only [List.foldr]
          rw [hprod f]
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem linListEval_eq_foldr (ls : List (Int × Int)) (x : Int) :
    linListEval ls x = ls.foldr (fun p acc => (p.1 * x + p.2) * acc) 1 := by
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp [linListEval, ih]

theorem cubeQuarticInt_strict_mono_nat (m : Nat) :
    cubeQuarticInt (m : Int) < cubeQuarticInt ((m + 1 : Nat) : Int) := by
  have hu : 0 ≤ (m : Int) := by omega
  have hu2 : (m : Int) * (m : Int) ≤ ((m : Int) + 1) * ((m : Int) + 1) :=
    Int.mul_le_mul (by omega) (by omega) hu (by omega)
  have hu3 : (m : Int) * (m : Int) * (m : Int) ≤
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1) :=
    Int.mul_le_mul hu2 (by omega) hu (Int.mul_nonneg (by omega) (by omega))
  have hu4 : (m : Int) * (m : Int) * (m : Int) * (m : Int) ≤
      ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1) * ((m : Int) + 1) :=
    Int.mul_le_mul hu3 (by omega) hu
      (Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega))
  have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
  rw [hcast]
  unfold cubeQuarticInt
  omega

/-- Core Non-Splitting Lemma: `cubeQuarticInt` cannot satisfy any nontrivial linear-factor
    relation `c1 * (∏ (α m + β)) * Q(m) = c2 * (∏ (γ m + δ))` for all `m ≥ M0`. -/
theorem no_linear_relation_for_quartic :
    ∀ (n : Nat) (rhsLin lhsLin : List (Int × Int)) (c1 c2 : Int) (M0 : Nat),
      rhsLin.length = n →
      c1 ≠ 0 →
      c2 ≠ 0 →
      (∀ p ∈ lhsLin, p.1 ≠ 0 ∨ p.2 ≠ 0) →
      (∀ q ∈ rhsLin, q.1 ≠ 0 ∨ q.2 ≠ 0) →
      (∀ m : Nat, M0 ≤ m →
        c1 * linListEval lhsLin (m : Int) * cubeQuarticInt (m : Int) =
          c2 * linListEval rhsLin (m : Int)) →
      False
  | 0, rhsLin, lhsLin, c1, c2, M0, hlen, hc1, hc2, hlhs_nz, _, heq => by
    cases rhsLin with
    | cons _ _ => simp at hlen
    | nil =>
      by_cases hhas : ∃ p ∈ lhsLin, p.1 ≠ 0
      · rcases hhas with ⟨⟨a, b⟩, hmem, ha⟩
        let s : Nat := a.natAbs
        have hs : 1 ≤ s := by omega
        let g : Int := (s : Int)
        have hg : g ≠ 0 := by dsimp [g]; omega
        let F : Poly := Poly.scale c1 (Poly.mul (homLinPolyList g lhsLin) (homQuarticPoly g))
        let G : Poly := [c2 * powInt g (lhsLin.length + 4)]
        have hFG : ∀ z : Int, Poly.eval F z = Poly.eval G z := by
          apply Poly.eq_everywhere_of_arith_prog F G s M0 hs
          intro m hm
          dsimp only [F, G]
          rw [Poly.eval_scale, Poly.eval_mul, homLinPolyList_eval_mul, homQuarticPoly_eval,
              homQuartic_scale]
          simp only [Poly.eval, linListEval] at heq ⊢
          have step := heq m hm
          rw [powInt_add g lhsLin.length 4]
          have hz0 : (s : Int) * (m : Int) * 0 = 0 := Int.mul_zero _
          rw [hz0, Int.add_zero]
          calc c1 * ((powInt g lhsLin.length * linListEval lhsLin (m : Int)) *
                (powInt g 4 * cubeQuarticInt (m : Int)))
            _ = (powInt g lhsLin.length * powInt g 4) *
                (c1 * linListEval lhsLin (m : Int) * cubeQuarticInt (m : Int)) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
            _ = (powInt g lhsLin.length * powInt g 4) * (c2 * 1) := by rw [step]
            _ = c2 * (powInt g lhsLin.length * powInt g 4) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        let z0 : Int := if 0 ≤ a then -b else b
        have hroot : a * z0 + b * g = 0 := by
          dsimp only [z0, g, s]
          by_cases hpos : 0 ≤ a
          · simp only [hpos, ↓reduceIte]
            have ha_eq : (a.natAbs : Int) = a := by omega
            rw [ha_eq, Int.mul_neg, Int.mul_comm b a]
            omega
          · simp only [hpos, ↓reduceIte]
            have ha_eq : (a.natAbs : Int) = -a := by omega
            rw [ha_eq, Int.mul_neg, Int.mul_comm b a]
            omega
        have hF0 : Poly.eval F z0 = 0 := by
          dsimp only [F]
          rw [Poly.eval_scale, Poly.eval_mul,
              homLinPolyList_eval_zero_of_mem g z0 a b lhsLin hmem hroot,
              Int.zero_mul, Int.mul_zero]
        have hG0 := hFG z0
        rw [hF0] at hG0
        dsimp only [G, Poly.eval] at hG0
        have : z0 * 0 = 0 := Int.mul_zero z0
        rw [this, Int.add_zero] at hG0
        cases Int.mul_eq_zero.mp hG0.symm with
        | inl h => exact hc2 h
        | inr h => exact powInt_ne_zero hg _ h
      · have hall0 : ∀ p ∈ lhsLin, p.1 = 0 ∧ p.2 ≠ 0 := by
          intro p hp
          have hp1 : p.1 = 0 := by
            by_cases h1 : p.1 = 0
            · exact h1
            · exact False.elim (hhas ⟨p, hp, h1⟩)
          rcases hlhs_nz p hp with h1 | h2
          · exact absurd hp1 h1
          · exact ⟨hp1, h2⟩
        have hconst := linListEval_const_of_slope_zero lhsLin (fun p hp => (hall0 p hp).1)
          (M0 : Int) ((M0 + 1 : Nat) : Int)
        have hnz_lhs := linListEval_nz_of_slope_zero lhsLin hall0 (M0 : Int)
        have eqA := heq M0 (Nat.le_refl M0)
        have eqB := heq (M0 + 1) (by omega)
        rw [← hconst] at eqB
        simp only [linListEval] at eqA eqB
        have hdiff : (c1 * linListEval lhsLin (M0 : Int)) *
            (cubeQuarticInt ((M0 + 1 : Nat) : Int) - cubeQuarticInt (M0 : Int)) = 0 := by
          rw [Int.mul_sub]
          omega
        cases Int.mul_eq_zero.mp hdiff with
        | inl h =>
          cases Int.mul_eq_zero.mp h with
          | inl h1 => exact hc1 h1
          | inr h2 => exact hnz_lhs h2
        | inr hq =>
          have hstrict := cubeQuarticInt_strict_mono_nat M0
          omega
  | n + 1, rhsLin, lhsLin, c1, c2, M0, hlen, hc1, hc2, hlhs_nz, hrhs_nz, heq => by
    cases rhsLin with
    | nil => simp at hlen
    | cons q0 rhsRest =>
      rcases q0 with ⟨gamma, delta⟩
      have hlen' : rhsRest.length = n := by simp at hlen; exact hlen
      have hq0_nz := hrhs_nz (gamma, delta) (List.Mem.head _)
      have hrhs_rest_nz : ∀ q ∈ rhsRest, q.1 ≠ 0 ∨ q.2 ≠ 0 :=
        fun q hq => hrhs_nz q (List.Mem.tail _ hq)
      by_cases hgamma : gamma = 0
      · have hdelta : delta ≠ 0 := by
          rcases hq0_nz with h1 | h2
          · exact absurd hgamma h1
          · exact h2
        apply no_linear_relation_for_quartic n rhsRest lhsLin c1 (c2 * delta) M0
          hlen' hc1 (fun h => by
            cases Int.mul_eq_zero.mp h with | inl h1 => exact hc2 h1 | inr h2 => exact hdelta h2)
          hlhs_nz hrhs_rest_nz
        intro m hm
        have step := heq m hm
        subst hgamma
        simp only [linListEval, Int.zero_mul, Int.zero_add] at step
        calc c1 * linListEval lhsLin (m : Int) * cubeQuarticInt (m : Int)
          _ = c2 * (delta * linListEval rhsRest (m : Int)) := step
          _ = (c2 * delta) * linListEval rhsRest (m : Int) := (Int.mul_assoc _ _ _).symm
      · let s : Nat := gamma.natAbs
        have hs : 1 ≤ s := by omega
        let g : Int := (s : Int)
        have hg : g ≠ 0 := by dsimp [g]; omega
        let dSigned : Int := if 0 ≤ gamma then delta else -delta
        have hgd_rel : ∀ x : Int, gamma * x + delta =
            (if 0 ≤ gamma then 1 else -1) * (g * x + dSigned) := by
          intro x
          dsimp only [g, s, dSigned]
          by_cases hpos : 0 ≤ gamma
          · simp only [hpos, ↓reduceIte, Int.one_mul]
            have hg_eq : (gamma.natAbs : Int) = gamma := by omega
            rw [hg_eq]
          · simp only [hpos, ↓reduceIte]
            have hg_eq : (gamma.natAbs : Int) = -gamma := by omega
            rw [hg_eq]
            simp [Int.neg_mul]
            omega
        let rhsNorm : List (Int × Int) := (g, dSigned) :: rhsRest
        let c2Norm : Int := c2 * (if 0 ≤ gamma then 1 else -1)
        let F : Poly := Poly.scale (c1 * powInt g rhsNorm.length)
                          (Poly.mul (homLinPolyList g lhsLin) (homQuarticPoly g))
        let G : Poly := Poly.scale (c2Norm * powInt g (lhsLin.length + 4))
                          (homLinPolyList g rhsNorm)
        have hFG : ∀ z : Int, Poly.eval F z = Poly.eval G z := by
          apply Poly.eq_everywhere_of_arith_prog F G s M0 hs
          intro m hm
          dsimp only [F, G]
          rw [Poly.eval_scale, Poly.eval_mul, homLinPolyList_eval_mul, homQuarticPoly_eval,
              homQuartic_scale, Poly.eval_scale, homLinPolyList_eval_mul]
          have step := heq m hm
          have hnorm : c2 * linListEval ((gamma, delta) :: rhsRest) (m : Int) =
              c2Norm * linListEval rhsNorm (m : Int) := by
            simp only [linListEval, rhsNorm, c2Norm, hgd_rel]
            simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
          rw [hnorm] at step
          rw [powInt_add g lhsLin.length 4]
          calc c1 * powInt g rhsNorm.length *
              (powInt g lhsLin.length * linListEval lhsLin (m : Int) *
               (powInt g 4 * cubeQuarticInt (m : Int)))
            _ = (powInt g rhsNorm.length * powInt g lhsLin.length * powInt g 4) *
                (c1 * linListEval lhsLin (m : Int) * cubeQuarticInt (m : Int)) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
            _ = (powInt g rhsNorm.length * powInt g lhsLin.length * powInt g 4) *
                (c2Norm * linListEval rhsNorm (m : Int)) := by rw [step]
            _ = c2Norm * (powInt g lhsLin.length * powInt g 4) *
                (powInt g rhsNorm.length * linListEval rhsNorm (m : Int)) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have hG0 : Poly.eval G (-dSigned) = 0 := by
          dsimp only [G, rhsNorm]
          rw [Poly.eval_scale]
          simp only [homLinPolyList, Poly.eval_mul, Poly.eval]
          have h0 : (-dSigned) * 0 = 0 := Int.mul_zero _
          rw [h0, Int.add_zero]
          have h1 : dSigned * g + (-dSigned) * g = 0 := by
            rw [Int.neg_mul]
            omega
          rw [h1, Int.zero_mul, Int.mul_zero]
        have hF0 := (hFG (-dSigned)).trans hG0
        dsimp only [F] at hF0
        rw [Poly.eval_scale, Poly.eval_mul, homQuarticPoly_eval] at hF0
        have hq_pos := homQuartic_pos hg (-dSigned)
        have hc1_pow_nz : c1 * powInt g rhsNorm.length ≠ 0 := fun h => by
          cases Int.mul_eq_zero.mp h with
          | inl h1 => exact hc1 h1
          | inr h2 => exact powInt_ne_zero hg _ h2
        have hlin0 : Poly.eval (homLinPolyList g lhsLin) (-dSigned) = 0 := by
          cases Int.mul_eq_zero.mp hF0 with
          | inl h => exact absurd h hc1_pow_nz
          | inr h =>
            cases Int.mul_eq_zero.mp h with
            | inl h1 => exact h1
            | inr h2 => omega
        rcases homLinPolyList_zero_iff g (-dSigned) lhsLin hlin0 with ⟨⟨alpha, beta⟩, hmem, hrel⟩
        dsimp only [] at hrel
        have hbg : beta * g = alpha * dSigned := by
          have : alpha * (-dSigned) = -(alpha * dSigned) := Int.mul_neg _ _
          omega
        have halpha : alpha ≠ 0 := by
          intro ha0
          rw [ha0, Int.zero_mul] at hbg
          have hb0 : beta = 0 := by
            cases Int.mul_eq_zero.mp hbg with | inl h => exact h | inr h => exact absurd h hg
          rcases hlhs_nz (alpha, beta) hmem with h1 | h2
          · exact h1 ha0
          · exact h2 hb0
        rcases extract_mem lhsLin hmem with ⟨lhsRest, hsub, hprod⟩
        have hlhs_rest_nz : ∀ p ∈ lhsRest, p.1 ≠ 0 ∨ p.2 ≠ 0 :=
          fun p hp => hlhs_nz p (hsub p hp)
        let M1 : Nat := M0 + dSigned.natAbs + 1
        have hc1' : c1 * alpha ≠ 0 := fun h => by
          cases Int.mul_eq_zero.mp h with | inl h1 => exact hc1 h1 | inr h2 => exact halpha h2
        have hc2' : c2Norm * g ≠ 0 := fun h => by
          cases Int.mul_eq_zero.mp h with
          | inl h1 =>
            dsimp only [c2Norm] at h1
            cases Int.mul_eq_zero.mp h1 with
            | inl hc => exact hc2 hc
            | inr hsgn => by_cases hp : 0 ≤ gamma <;> simp [hp] at hsgn
          | inr h2 => exact hg h2
        apply no_linear_relation_for_quartic n rhsRest lhsRest (c1 * alpha) (c2Norm * g) M1
          hlen' hc1' hc2' hlhs_rest_nz hrhs_rest_nz
        intro m hm
        let x : Int := (m : Int)
        have hfac_nz : g * x + dSigned ≠ 0 := by
          dsimp only [x, g]
          have hgx : (m : Int) ≤ (s : Int) * (m : Int) := by
            have hg1 : (1 : Int) ≤ (s : Int) := by omega
            have hmul := Int.mul_le_mul_of_nonneg_right hg1 (by omega : 0 ≤ (m : Int))
            simpa [Int.one_mul] using hmul
          omega
        have step := heq m (by omega)
        have hnorm : c2 * linListEval ((gamma, delta) :: rhsRest) x =
            (g * x + dSigned) * (c2Norm * linListEval rhsRest x) := by
          simp only [linListEval, c2Norm, hgd_rel]
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        have hlhs_split : linListEval lhsLin x =
            (alpha * x + beta) * linListEval lhsRest x := by
          rw [linListEval_eq_foldr, linListEval_eq_foldr]
          exact hprod (fun p => p.1 * x + p.2)
        have hg_prop : g * (alpha * x + beta) = alpha * (g * x + dSigned) := by
          calc g * (alpha * x + beta)
            _ = g * (alpha * x) + g * beta := Int.mul_add _ _ _
            _ = alpha * (g * x) + beta * g := by
                  rw [Int.mul_comm g beta]
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
            _ = alpha * (g * x) + alpha * dSigned := by rw [hbg]
            _ = alpha * (g * x + dSigned) := (Int.mul_add _ _ _).symm
        have hcomb : (g * x + dSigned) *
            ((c1 * alpha) * linListEval lhsRest x * cubeQuarticInt x -
             (c2Norm * g) * linListEval rhsRest x) = 0 := by
          rw [Int.mul_sub]
          have t1 : (g * x + dSigned) * ((c1 * alpha) * linListEval lhsRest x * cubeQuarticInt x) =
              g * (c1 * linListEval lhsLin x * cubeQuarticInt x) := by
            rw [hlhs_split]
            calc (g * x + dSigned) * (c1 * alpha * linListEval lhsRest x * cubeQuarticInt x)
              _ = (alpha * (g * x + dSigned)) * (c1 * linListEval lhsRest x * cubeQuarticInt x) := by
                    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
              _ = (g * (alpha * x + beta)) * (c1 * linListEval lhsRest x * cubeQuarticInt x) := by
                    rw [← hg_prop]
              _ = g * (c1 * ((alpha * x + beta) * linListEval lhsRest x) * cubeQuarticInt x) := by
                    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
          have t2 : (g * x + dSigned) * ((c2Norm * g) * linListEval rhsRest x) =
              g * (c2 * linListEval ((gamma, delta) :: rhsRest) x) := by
            rw [hnorm]
            simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
          dsimp only [x] at t1 t2 ⊢
          rw [t1, t2, step]
          omega
        cases Int.mul_eq_zero.mp hcomb with
        | inl h => exact absurd h hfac_nz
        | inr h =>
          dsimp only [x] at h
          exact Int.sub_eq_zero.mp h

def maxShift : List (Int × Int) → Nat
  | [] => 0
  | (_, b) :: rest => b.natAbs + maxShift rest

theorem linListEval_factors_nz_of_nz {ls : List (Int × Int)} {x : Int}
    (h : linListEval ls x ≠ 0) : ∀ p ∈ ls, p.1 ≠ 0 ∨ p.2 ≠ 0 := by
  induction ls with
  | nil => intro _ hm; nomatch hm
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [linListEval] at h
    have hhd : a * x + b ≠ 0 := fun h0 => h (by rw [h0, Int.zero_mul])
    have htl : linListEval tl x ≠ 0 := fun h0 => h (by rw [h0, Int.mul_zero])
    intro p hp
    cases hp with
    | head =>
      by_cases ha : a = 0
      · right
        intro hb
        dsimp only [] at hb
        apply hhd
        simp [ha, hb]
      · exact Or.inl ha
    | tail _ hmem => exact ih htl p hmem

theorem linListEval_nz_above_maxShift : ∀ (ls : List (Int × Int)) (m : Nat),
    (∀ p ∈ ls, p.1 ≠ 0 ∨ p.2 ≠ 0) →
    maxShift ls < m →
    linListEval ls (m : Int) ≠ 0
  | [], _, _, _ => by simp [linListEval]
  | (a, b) :: rest, m, hnz, hm => by
    simp only [maxShift] at hm
    simp only [linListEval]
    have h1 : a * (m : Int) + b ≠ 0 := by
      by_cases ha0 : a = 0
      · rcases hnz (a, b) (List.Mem.head _) with ha | hb
        · exact absurd ha0 ha
        · subst ha0; simp [hb]
      · by_cases hapos : 1 ≤ a
        · have hmul : 1 * (m : Int) ≤ a * (m : Int) :=
            Int.mul_le_mul_of_nonneg_right hapos (by omega)
          omega
        · have haneg : a ≤ -1 := by omega
          have hmul : a * (m : Int) ≤ (-1) * (m : Int) :=
            Int.mul_le_mul_of_nonneg_right haneg (by omega)
          omega
    have h2 := linListEval_nz_above_maxShift rest m
      (fun p hp => hnz p (List.Mem.tail _ hp)) (by omega)
    intro hmul
    cases Int.mul_eq_zero.mp hmul with
    | inl h => exact h1 h
    | inr h => exact h2 h

/-- Theorem: `omegaCube` CANNOT be expressed as any rational linear ratio (even eventually). -/
theorem omegaCube_not_rationalLinearRatio : ¬ IsRationalLinearRatio omegaCube := by
  intro ⟨M0, cNum, cDen, numLin, denLin, hcDen, ⟨_, _, hden_m1⟩, heq⟩
  have hden_nz : ∀ p ∈ denLin, p.1 ≠ 0 ∨ p.2 ≠ 0 :=
    linListEval_factors_nz_of_nz hden_m1
  let m2 : Nat := M0 + maxShift denLin + 1
  have hm2_ge : M0 ≤ m2 := by omega
  have hden_m2 : linListEval denLin (m2 : Int) ≠ 0 :=
    linListEval_nz_above_maxShift denLin m2 hden_nz (by omega)
  have homega_m2 : 1 ≤ omegaCube m2 := by
    unfold omegaCube
    have hb1 : binom m2 1 = m2 := binom_one m2
    omega
  have hlhs_m2_nz : cDen * linListEval denLin (m2 : Int) * (omegaCube m2 : Int) ≠ 0 := by
    intro h0
    cases Int.mul_eq_zero.mp h0 with
    | inl h1 =>
      cases Int.mul_eq_zero.mp h1 with
      | inl hc => exact hcDen hc
      | inr hd => exact hden_m2 hd
    | inr ho => omega
  have hrhs_m2_nz : cNum * linListEval numLin (m2 : Int) ≠ 0 := by
    rw [← heq m2 hm2_ge]; exact hlhs_m2_nz
  have hcNum : cNum ≠ 0 := fun h0 => hrhs_m2_nz (by rw [h0, Int.zero_mul])
  have hnum_m2 : linListEval numLin (m2 : Int) ≠ 0 :=
    fun h0 => hrhs_m2_nz (by rw [h0, Int.mul_zero])
  have hnum_nz : ∀ q ∈ numLin, q.1 ≠ 0 ∨ q.2 ≠ 0 :=
    linListEval_factors_nz_of_nz hnum_m2
  let lhsLinFull : List (Int × Int) := (1, 0) :: (1, 1) :: (1, 2) :: (1, 3) :: denLin
  have hlhsFull_nz : ∀ p ∈ lhsLinFull, p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    intro p hp
    simp only [lhsLinFull, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | rfl | hp'
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact hden_nz p hp'
  apply no_linear_relation_for_quartic numLin.length numLin lhsLinFull
    cDen (1680 * cNum) M0 rfl hcDen (fun h => by
      cases Int.mul_eq_zero.mp h with | inl h1 => omega | inr h2 => exact hcNum h2)
    hlhsFull_nz hnum_nz
  intro m hm
  have hpoly := omegaCube_poly_identity m
  have hpolyInt : (1680 : Int) * (omegaCube m : Int) =
      (m : Int) * ((m : Int) + 1) * ((m : Int) + 2) * ((m : Int) + 3) *
      cubeQuarticInt (m : Int) := by
    have := congrArg (fun n : Nat => (n : Int)) hpoly
    simpa [natCast_mul, natCast_add, cubeQuarticNat, cubeQuarticInt, Int.mul_assoc] using this
  have step := congrArg (fun t => (1680 : Int) * t) (heq m hm)
  dsimp only [] at step
  let x : Int := (m : Int)
  have hlhs_eval : linListEval lhsLinFull x =
      x * (x + 1) * (x + 2) * (x + 3) * linListEval denLin x := by
    simp only [lhsLinFull, linListEval, Int.one_mul, Int.add_zero]
    simp [Int.mul_assoc]
  dsimp only [x] at hlhs_eval
  rw [hlhs_eval]
  calc cDen * ((m : Int) * ((m : Int) + 1) * ((m : Int) + 2) * ((m : Int) + 3) * linListEval denLin (m : Int)) *
        cubeQuarticInt (m : Int)
    _ = cDen * linListEval denLin (m : Int) *
        ((m : Int) * ((m : Int) + 1) * ((m : Int) + 2) * ((m : Int) + 3) * cubeQuarticInt (m : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = cDen * linListEval denLin (m : Int) * (1680 * (omegaCube m : Int)) := by
          rw [← hpolyInt]
    _ = 1680 * (cDen * linListEval denLin (m : Int) * (omegaCube m : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = 1680 * (cNum * linListEval numLin (m : Int)) := step
    _ = (1680 * cNum) * linListEval numLin (m : Int) := (Int.mul_assoc _ _ _).symm

theorem omegaCube_not_macmahonMultinomialQuotient :
    ¬ IsMacMahonMultinomialQuotient omegaCube :=
  fun h => omegaCube_not_rationalLinearRatio (macmahon_imp_rationalLinear h)

theorem omegaCube_not_pureMultinomialPolyProd :
    ¬ IsPureMultinomialPolyProd omegaCube :=
  fun h => omegaCube_not_macmahonMultinomialQuotient (pure_imp_macmahon h)

/-! ## Section 8: Prime-Factor, Endomorphism, and Naive-Box Disproofs -/

/-- Constructive primality predicate on `Nat`. -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private theorem nat_le_29_cases (n : Nat) (h2 : 2 ≤ n) (h29 : n ≤ 29) :
    n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨
    n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨
    n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 := by
  omega

/-- `887` is prime (`√887 < 30`). -/
theorem isPrime_887 : IsPrimeNat 887 := by
  refine ⟨by omega, fun d hd => ?_⟩
  rcases hd with ⟨q, hq⟩
  have hd0 : d ≠ 0 := by intro h; subst h; omega
  have hq0 : q ≠ 0 := by intro h; subst h; omega
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · by_cases hq1 : q = 1
    · subst hq1; right; omega
    · exfalso
      have hd2 : 2 ≤ d := by omega
      have hq2 : 2 ≤ q := by omega
      have hmin : d ≤ 29 ∨ q ≤ 29 := by
        by_cases h : d ≤ 29
        · exact Or.inl h
        · right
          by_cases hq30 : 30 ≤ q
          · have hmul : 30 * 30 ≤ d * q := Nat.mul_le_mul (by omega) hq30
            omega
          · omega
      rcases hmin with hsmall | hsmall
      · rcases nat_le_29_cases d hd2 hsmall with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · rcases nat_le_29_cases q hq2 hsmall with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Gauss's elementary proof of Euclid's lemma (pure `Nat`, zero Bézout/GCD machinery). -/
theorem gauss_euclid_lt {p : Nat} (hp : IsPrimeNat p) :
    ∀ (k : Nat) (x y : Nat), x ≤ k → 1 ≤ x → x < p → p ∣ x * y → p ∣ y
  | 0, x, _, hxk, hx1, _, _ => by omega
  | k + 1, x, y, hxk, hx1, hxp, hdvd => by
    by_cases hlt : x ≤ k
    · exact gauss_euclid_lt hp k x y hlt hx1 hxp hdvd
    · by_cases hx1_eq : x = 1
      · subst hx1_eq; simpa using hdvd
      · let r := p % x
        let q := p / x
        have hdiv : x * q + r = p := Nat.div_add_mod p x
        have hr_lt : r < x := Nat.mod_lt p (by omega)
        have hr_pos : 1 ≤ r := by
          by_cases hr0 : r = 0
          · rw [hr0, Nat.add_zero] at hdiv
            have hxdvd : x ∣ p := ⟨q, hdiv.symm⟩
            rcases hp.2 x hxdvd with hx_eq1 | hx_eqp <;> omega
          · omega
        have hpy : (x * y) * q + r * y = p * y := by
          calc (x * y) * q + r * y
            _ = (x * q) * y + r * y := by
                  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            _ = (x * q + r) * y := (Nat.add_mul _ _ _).symm
            _ = p * y := by rw [hdiv]
        rcases hdvd with ⟨u, hu⟩
        have hrdvd : p ∣ r * y := by
          refine ⟨y - u * q, ?_⟩
          rw [hu] at hpy
          have h1 : p * (u * q) + r * y = p * y := by
            calc p * (u * q) + r * y
              _ = (p * u) * q + r * y := by simp [Nat.mul_assoc]
              _ = p * y := hpy
          have hle : u * q ≤ y := by
            by_cases hgt : y < u * q
            · have hmul : p * (y + 1) ≤ p * (u * q) :=
                Nat.mul_le_mul_left p (by omega)
              rw [Nat.mul_add, Nat.mul_one] at hmul
              have hp2 := hp.1
              omega
            · omega
          rw [Nat.mul_sub_left_distrib]
          omega
        exact gauss_euclid_lt hp k r y (by omega) hr_pos (by omega) hrdvd

theorem prime_dvd_mul {p x y : Nat} (hp : IsPrimeNat p) (h : p ∣ x * y) :
    p ∣ x ∨ p ∣ y := by
  let r := x % p
  let q := x / p
  have hdiv : p * q + r = x := Nat.div_add_mod x p
  by_cases hr0 : r = 0
  · left
    rw [hr0, Nat.add_zero] at hdiv
    exact ⟨q, hdiv.symm⟩
  · right
    have hr_lt : r < p := Nat.mod_lt x (by have := hp.1; omega)
    rcases h with ⟨u, hu⟩
    have hrdvd : p ∣ r * y := by
      have hexp : p * (q * y) + r * y = p * u := by
        calc p * (q * y) + r * y
          _ = (p * q + r) * y := by simp [Nat.add_mul, Nat.mul_assoc]
          _ = x * y := by rw [hdiv]
          _ = p * u := hu
      have hle : q * y ≤ u := by
        by_cases hgt : u < q * y
        · have hmul := Nat.mul_le_mul_left p (by omega : u + 1 ≤ q * y)
          rw [Nat.mul_add, Nat.mul_one] at hmul
          have hp2 := hp.1
          omega
        · omega
      refine ⟨u - q * y, ?_⟩
      rw [Nat.mul_sub_left_distrib]
      omega
    exact gauss_euclid_lt hp r r y (Nat.le_refl r) (by omega) hr_lt hrdvd

theorem not_prime_dvd_fact_of_lt {p : Nat} (hp : IsPrimeNat p) :
    ∀ n : Nat, n < p → ¬ (p ∣ fact n)
  | 0, _, ⟨q, hq⟩ => by
    simp only [fact] at hq
    have := hp.1
    by_cases hq0 : q = 0
    · subst hq0; omega
    · have : p * 1 ≤ p * q := Nat.mul_le_mul_left p (by omega)
      omega
  | n + 1, hlt, hdvd => by
    simp only [fact] at hdvd
    rcases prime_dvd_mul hp hdvd with h1 | h2
    · rcases h1 with ⟨q, hq⟩
      by_cases hq0 : q = 0
      · subst hq0; omega
      · have : p * 1 ≤ p * q := Nat.mul_le_mul_left p (by omega)
        omega
    · exact not_prime_dvd_fact_of_lt hp n (by omega) h2

/-- Prime-Factor Obstruction for Bounded Multinomial Quotients:
    If a prime `p` divides `M`, then NO quotient of products of multinomial coefficients
    `M * ∏ multinomial(ds_j) = ∏ multinomial(ns_i)` with nonzero denominator and top entries
    `listSum(ns_i) < p` can hold! -/
theorem no_bounded_multinomial_quotient_of_prime_dvd {p M : Nat}
    (hp : IsPrimeNat p) (hpM : p ∣ M)
    (numParts denParts : List (List Nat))
    (_hden_pos : 1 ≤ prodMultinomials denParts)
    (hbound : ∀ ks ∈ numParts, listSum ks < p)
    (heq : M * prodMultinomials denParts = prodMultinomials numParts) : False := by
  let bigFactProd : List (List Nat) → Nat :=
    fun l => l.foldr (fun ks acc => prodFact ks * acc) 1
  let numTopFacts : List (List Nat) → Nat :=
    fun l => l.foldr (fun ks acc => fact (listSum ks) * acc) 1
  have hbridge : ∀ l : List (List Nat),
      prodMultinomials l * bigFactProd l = numTopFacts l := by
    intro l
    induction l with
    | nil => rfl
    | cons ks rest ih =>
      simp only [prodMultinomials, bigFactProd, numTopFacts, List.foldr]
      calc (multinomial ks * prodMultinomials rest) * (prodFact ks * bigFactProd rest)
        _ = (multinomial ks * prodFact ks) * (prodMultinomials rest * bigFactProd rest) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = fact (listSum ks) * numTopFacts rest := by rw [multinomial_spec, ih]
  have hnot_dvd : ∀ l : List (List Nat), (∀ ks ∈ l, listSum ks < p) → ¬ (p ∣ numTopFacts l) := by
    intro l hl hdvd
    induction l with
    | nil =>
      rcases hdvd with ⟨q, hq⟩
      simp only [numTopFacts, List.foldr] at hq
      have := hp.1
      by_cases hq0 : q = 0
      · subst hq0; omega
      · have : p * 1 ≤ p * q := Nat.mul_le_mul_left p (by omega)
        omega
    | cons ks rest ih =>
      simp only [numTopFacts, List.foldr] at hdvd
      rcases prime_dvd_mul hp hdvd with h1 | h2
      · exact not_prime_dvd_fact_of_lt hp (listSum ks) (hl ks (List.Mem.head _)) h1
      · exact ih (fun ks' hmem => hl ks' (List.Mem.tail _ hmem)) h2
  have hlhs_dvd : p ∣ numTopFacts numParts := by
    rw [← hbridge numParts, ← heq]
    rcases hpM with ⟨u, hu⟩
    rw [hu]
    refine ⟨u * prodMultinomials denParts * bigFactProd numParts, ?_⟩
    simp [Nat.mul_assoc]
  exact hnot_dvd numParts hbound hlhs_dvd

theorem binom_last_sub_one (n : Nat) : binom (n + 1) n = n + 1 := by
  have h1 := binom_mul_fact (n + 1) n 1 rfl
  have hf1 : fact 1 = 1 := rfl
  have hfn : fact (n + 1) = (n + 1) * fact n := rfl
  rw [hf1, Nat.mul_one, hfn] at h1
  exact Nat.eq_of_mul_eq_mul_right (fact_pos n) h1

theorem sum_lt_binom_of_ge_two : ∀ (s a b : Nat), a + b = s → 2 ≤ a → 2 ≤ b →
    a + b < binom (a + b) a
  | 0, _, _, hs, ha, _ => by omega
  | s + 1, a, b, hs, ha, hb => by
    by_cases ha2 : a = 2
    · by_cases hb2 : b = 2
      · subst ha2; subst hb2; decide
      · have hb' : ∃ b0, b = b0 + 1 ∧ 2 ≤ b0 := ⟨b - 1, by omega, by omega⟩
        rcases hb' with ⟨b0, rfl, hb0⟩
        have ih := sum_lt_binom_of_ge_two (2 + b0) 2 b0 rfl (by omega) hb0
        subst ha2
        have hstep : binom (2 + (b0 + 1)) 2 = binom (2 + b0) 1 + binom (2 + b0) 2 := by
          have : 2 + (b0 + 1) = (2 + b0) + 1 := by omega
          rw [this]; rfl
        rw [hstep, binom_one]
        omega
    · by_cases hb2 : b = 2
      · have ha' : ∃ a0, a = a0 + 1 ∧ 2 ≤ a0 := ⟨a - 1, by omega, by omega⟩
        rcases ha' with ⟨a0, rfl, ha0⟩
        have ih := sum_lt_binom_of_ge_two (a0 + 2) a0 2 rfl ha0 (by omega)
        subst hb2
        have hstep : binom (a0 + 1 + 2) (a0 + 1) = binom (a0 + 2) a0 + binom (a0 + 2) (a0 + 1) := by
          have : a0 + 1 + 2 = (a0 + 2) + 1 := by omega
          rw [this]; rfl
        have hlast : binom (a0 + 2) (a0 + 1) = a0 + 2 := binom_last_sub_one (a0 + 1)
        rw [hstep, hlast]
        omega
      · have ha' : ∃ a0, a = a0 + 1 ∧ 2 ≤ a0 := ⟨a - 1, by omega, by omega⟩
        rcases ha' with ⟨a0, rfl, ha0⟩
        have hb' : ∃ b0, b = b0 + 1 ∧ 2 ≤ b0 := ⟨b - 1, by omega, by omega⟩
        rcases hb' with ⟨b0, rfl, hb0⟩
        have ih1 := sum_lt_binom_of_ge_two (a0 + (b0 + 1)) a0 (b0 + 1) rfl ha0 (by omega)
        have ih2 := sum_lt_binom_of_ge_two (a0 + 1 + b0) (a0 + 1) b0 rfl (by omega) hb0
        have hrew : a0 + 1 + (b0 + 1) = (a0 + 1 + b0) + 1 := by omega
        have hrew2 : a0 + (b0 + 1) = a0 + 1 + b0 := by omega
        rw [hrew2] at ih1
        rw [hrew]
        simp only [binom]
        omega

theorem binom_pos_of_le : ∀ (n k : Nat), k ≤ n → 0 < binom n k
  | n, 0, _ => by rw [binom_zero]; exact Nat.zero_lt_one
  | 0, _ + 1, h => by omega
  | n + 1, k + 1, h => by
    simp only [binom]
    have := binom_pos_of_le n k (by omega)
    omega

theorem multinomial_pos : (ks : List Nat) → 0 < multinomial ks
  | [] => Nat.zero_lt_one
  | k :: ks =>
    Nat.mul_pos (binom_pos_of_le (k + listSum ks) k (by omega)) (multinomial_pos ks)

theorem prodMultinomials_pos : (l : List (List Nat)) → 0 < prodMultinomials l
  | [] => Nat.zero_lt_one
  | ks :: rest => Nat.mul_pos (multinomial_pos ks) (prodMultinomials_pos rest)

theorem binom_ge_top_of_pos {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b ≤ binom (a + b) a := by
  by_cases ha1 : a = 1
  · subst ha1
    have : 1 + b = b + 1 := by omega
    rw [this, binom_one]
    exact Nat.le_refl _
  · by_cases hb1 : b = 1
    · subst hb1
      rw [binom_last_sub_one a]
      exact Nat.le_refl _
    · have := sum_lt_binom_of_ge_two (a + b) a b rfl (by omega) (by omega)
      omega

theorem genuine_multinomial_gt_sum {ks : List Nat} (h : IsGenuineMultinomial ks) :
    listSum ks < multinomial ks := by
  rcases h with ⟨hpos, hshape⟩
  rcases hshape with hlen3 | ⟨a, b, rfl, ha, hb⟩
  · cases ks with
    | nil => simp at hlen3
    | cons k1 r1 =>
      cases r1 with
      | nil => simp at hlen3
      | cons k2 r2 =>
        cases r2 with
        | nil => simp at hlen3
        | cons k3 r3 =>
          have hk1 := hpos k1 (List.Mem.head _)
          have hk2 := hpos k2 (List.Mem.tail _ (List.Mem.head _))
          have hk3 := hpos k3 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
          let S1 := k1 + (k2 + (k3 + listSum r3))
          let S2 := k2 + (k3 + listSum r3)
          have hb1 : S1 ≤ binom S1 k1 := binom_ge_top_of_pos hk1 (by omega)
          have hb2 : S2 ≤ binom S2 k2 := binom_ge_top_of_pos hk2 (by omega)
          have hm3 : 1 ≤ multinomial (k3 :: r3) := multinomial_pos (k3 :: r3)
          have htail : 2 ≤ binom S2 k2 * multinomial (k3 :: r3) := by
            have hmul := Nat.mul_le_mul hb2 hm3
            have hs2 : 2 ≤ S2 := by omega
            omega
          have htot : S1 * 2 ≤ binom S1 k1 * (binom S2 k2 * multinomial (k3 :: r3)) :=
            Nat.mul_le_mul hb1 htail
          have hs1_pos : 3 ≤ S1 := by omega
          change S1 < binom S1 k1 * (binom S2 k2 * multinomial (k3 :: r3))
          omega
  · simp only [multinomial, listSum, Nat.add_zero, binom_self, Nat.mul_one]
    exact sum_lt_binom_of_ge_two (a + b) a b rfl ha hb

theorem genuine_multinomial_ge_two {ks : List Nat} (h : IsGenuineMultinomial ks) :
    2 ≤ multinomial ks := by
  have hgt := genuine_multinomial_gt_sum h
  rcases h with ⟨hpos, hshape⟩
  rcases hshape with hlen3 | ⟨a, b, rfl, ha, hb⟩
  · cases ks with
    | nil => simp at hlen3
    | cons k1 r1 =>
      have hk1 := hpos k1 (List.Mem.head _)
      simp only [listSum] at hgt
      omega
  · simp only [listSum] at hgt
    omega

/-- No finite product of genuine (non-edge) multinomial coefficients equals `887`! -/
theorem no_genuine_multinomial_prod_eq_887 (l : List (List Nat))
    (hgen : ∀ ks ∈ l, IsGenuineMultinomial ks) :
    prodMultinomials l ≠ 887 := by
  intro heq
  cases l with
  | nil => simp [prodMultinomials] at heq
  | cons ks1 rest =>
    have hg1 := hgen ks1 (List.Mem.head _)
    have hm1_ge2 := genuine_multinomial_ge_two hg1
    cases rest with
    | cons ks2 rest2 =>
      have hg2 := hgen ks2 (List.Mem.tail _ (List.Mem.head _))
      have hm2_ge2 := genuine_multinomial_ge_two hg2
      let P := prodMultinomials (ks2 :: rest2)
      have hrest_pos : 2 ≤ P := by
        dsimp only [P, prodMultinomials]
        have hpos : 1 ≤ prodMultinomials rest2 := prodMultinomials_pos rest2
        have hmul := Nat.mul_le_mul hm2_ge2 hpos
        omega
      have heqP : multinomial ks1 * P = 887 := heq
      have hdvd : multinomial ks1 ∣ 887 := ⟨P, heqP.symm⟩
      rcases isPrime_887.2 (multinomial ks1) hdvd with h1 | h887
      · omega
      · rw [h887] at heqP
        have hmul : 887 * 2 ≤ 887 * P := Nat.mul_le_mul_left 887 hrest_pos
        omega
    | nil =>
      simp only [prodMultinomials, Nat.mul_one] at heq
      by_cases hlt : listSum ks1 < 887
      · exact no_bounded_multinomial_quotient_of_prime_dvd isPrime_887 ⟨1, rfl⟩
          [ks1] [] (Nat.le_refl 1)
          (fun ks hmem => by simp at hmem; subst hmem; exact hlt)
          (by simp [prodMultinomials, heq])
      · have hgt := genuine_multinomial_gt_sum hg1
        omega

/-- Permuting coordinates of `ChainProd [2, 2, 3]` and `ChainProd [3, 2, 2]`. -/
def chainProd223SwapEquiv :
    Equiv (ChainProd [2, 2, 3]) (ChainProd [3, 2, 2]) where
  toFun c := match c with | .cons x (.cons y (.cons z .nil)) => .cons z (.cons x (.cons y .nil))
  invFun c := match c with | .cons z (.cons x (.cons y .nil)) => .cons x (.cons y (.cons z .nil))
  left_inv c := by
    cases c with | cons x r1 => cases r1 with | cons y r2 => cases r2 with | cons z r3 =>
    cases r3 with | nil => rfl
  right_inv c := by
    cases c with | cons z r1 => cases r1 with | cons x r2 => cases r2 with | cons y r3 =>
    cases r3 with | nil => rfl

def orderHom223To322Equiv (Q : Poset) :
    Equiv (OrderHom (chainProdLattice [2, 2, 3]).toPoset Q)
          (OrderHom (chainProdLattice [3, 2, 2]).toPoset Q) where
  toFun f :=
    { toFun := fun u => f.toFun (chainProd223SwapEquiv.invFun u)
      mono := fun {u v} huv => by
        cases u with | cons z1 r1 => cases r1 with | cons x1 r2 => cases r2 with | cons y1 n1 => cases n1 with | nil =>
        cases v with | cons z2 s1 => cases s1 with | cons x2 s2 => cases s2 with | cons y2 n2 => cases n2 with | nil =>
        rcases huv with ⟨hz, hx, hy, _⟩
        exact f.mono ⟨hx, hy, hz, trivial⟩ }
  invFun g :=
    { toFun := fun u => g.toFun (chainProd223SwapEquiv.toFun u)
      mono := fun {u v} huv => by
        cases u with | cons x1 r1 => cases r1 with | cons y1 r2 => cases r2 with | cons z1 n1 => cases n1 with | nil =>
        cases v with | cons x2 s1 => cases s1 with | cons y2 s2 => cases s2 with | cons z2 n2 => cases n2 with | nil =>
        rcases huv with ⟨hx, hy, hz, _⟩
        exact g.mono ⟨hz, hx, hy, trivial⟩ }
  left_inv _ := OrderHom.ext (fun _ => by simp [chainProd223SwapEquiv.left_inv])
  right_inv _ := OrderHom.ext (fun _ => by simp [chainProd223SwapEquiv.right_inv])

theorem omega_222_at_4 :
    HasCard (OrderHom (chainProdLattice [2, 2, 2]).toPoset (chainLattice 4).toPoset) 887 := by
  have h : omegaCube 4 = 887 := by decide
  rw [← h]
  exact omegaCube_card 4

theorem omega_2222_at_2 :
    HasCard (OrderHom (chainProdLattice [2, 2, 2, 2]).toPoset (chainLattice 2).toPoset) 168 := by
  have e1 := orderHomChainSwapEquiv 2 1 [2, 2, 2]
  have e2 := orderHomDropUnitChainEquiv [2, 2, 2] (chainLattice 3).toPoset
  have hc : omegaCube 3 = 168 := by decide
  apply HasCard.ofEquiv (e1.trans e2)
  rw [← hc]
  exact omegaCube_card 3

theorem omega_223_at_2 :
    HasCard (OrderHom (chainProdLattice [2, 2, 3]).toPoset (chainLattice 2).toPoset) 50 := by
  have e0 := orderHom223To322Equiv (chainLattice 2).toPoset
  have e1 := orderHomChainSwapEquiv 3 1 [2, 2]
  have e2 := orderHomDropUnitChainEquiv [2, 2] (chainLattice 4).toPoset
  have hc : omegaSq 4 = 50 := by decide
  apply HasCard.ofEquiv (e0.trans (e1.trans e2))
  rw [← hc]
  exact omegaSq_card 4

theorem omega_223_at_3 :
    HasCard (OrderHom (chainProdLattice [2, 2, 3]).toPoset (chainLattice 3).toPoset) 887 := by
  have e0 := orderHom223To322Equiv (chainLattice 3).toPoset
  have e1 := orderHomChainSwapEquiv 3 2 [2, 2]
  apply HasCard.ofEquiv (e0.trans e1)
  exact omega_222_at_4

def orderHomEmptyCodomainUnit (P : Poset) :
    HasCard (OrderHom P (chainProdLattice []).toPoset) 1 :=
  ⟨{ toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
     invFun := fun _ => { toFun := fun _ => .nil, mono := fun _ => trivial }
     left_inv := fun f => OrderHom.ext (fun x => by cases f.toFun x; rfl)
     right_inv := fun k => Fin.ext (by have := k.isLt; dsimp only []; omega) }⟩

/-- Exact cardinality of the order-preserving endomorphism monoid of `C_2 × C_2 × C_3`:
    `|End_≤(C_2 × C_2 × C_3)| = 50 * 50 * 887 = 2,217,500`. -/
theorem orderEnd_223_card :
    HasCard (OrderHom (chainProdLattice [2, 2, 3]).toPoset
                      (chainProdLattice [2, 2, 3]).toPoset) 2217500 := by
  let P := (chainProdLattice [2, 2, 3]).toPoset
  have hnil : HasCard (OrderHom P (chainProdLattice []).toPoset) 1 :=
    orderHomEmptyCodomainUnit P
  have h3 : HasCard (OrderHom P (chainProdLattice [3]).toPoset) 887 := by
    have e := orderHomConsCodomainEquiv P 3 []
    exact HasCard.ofEquiv e (HasCard.prod omega_223_at_3 hnil)
  have h23 : HasCard (OrderHom P (chainProdLattice [2, 3]).toPoset) (50 * 887) := by
    have e := orderHomConsCodomainEquiv P 2 [3]
    exact HasCard.ofEquiv e (HasCard.prod omega_223_at_2 h3)
  have h223 : HasCard (OrderHom P (chainProdLattice [2, 2, 3]).toPoset) (50 * (50 * 887)) := by
    have e := orderHomConsCodomainEquiv P 2 [2, 3]
    exact HasCard.ofEquiv e (HasCard.prod omega_223_at_2 h23)
  have hmul : 50 * (50 * 887) = 2217500 := by decide
  rw [hmul] at h223
  exact h223

/-! ## Section 9: Master Disproof Theorems for Conjecture 00000008552 -/

/-- `OrderPolyCounts dims f` states that `f(m)` counts order-preserving maps `L(dims) → C_m`
    for every chain length `m ≥ 1`. -/
def OrderPolyCounts (dims : List Nat) (f : Nat → Nat) : Prop :=
  ∀ m : Nat, 1 ≤ m →
    HasCard (OrderHom (chainProdLattice dims).toPoset (chainLattice m).toPoset) (f m)

/-- Non-vacuity witness (`d = 2`, `C_2 × C_2`): MacMahon's multinomial quotient formula
    genuinely holds for 2-chain product lattices. -/
theorem macmahon_holds_for_two_chains_witness :
    ValidChainDims [2, 2] ∧
    OrderPolyCounts [2, 2] omegaSq ∧
    IsMacMahonMultinomialQuotient omegaSq ∧
    IsRationalLinearRatio omegaSq :=
  ⟨⟨by decide, fun a ha => by simp at ha; omega⟩,
   fun m _ => omegaSq_card m,
   omegaSq_isMacMahonMultinomialQuotient,
   macmahon_imp_rationalLinear omegaSq_isMacMahonMultinomialQuotient⟩

/-- MASTER DISPROOF 1 (Order Polynomial / MacMahon Product Reading):
    It is FALSE that for every finite nonempty chain product lattice `L`, its order-preserving
    map count `m ↦ |Hom_≤(L, C_m)|` is a pure product of polynomial multinomial coefficients,
    a MacMahon-type quotient of products of polynomial multinomial coefficients, or even
    eventually equal to ANY rational quotient of products of integer linear factors in `m`.
    Counterexample: `L = C_2 × C_2 × C_2` (`dims = [2, 2, 2]`). -/
theorem conjecture_00000008552_order_polynomial_disproved :
    (¬ ∀ dims : List Nat, ValidChainDims dims →
        ∃ f : Nat → Nat, OrderPolyCounts dims f ∧ IsPureMultinomialPolyProd f) ∧
    (¬ ∀ dims : List Nat, ValidChainDims dims →
        ∃ f : Nat → Nat, OrderPolyCounts dims f ∧ IsMacMahonMultinomialQuotient f) ∧
    (¬ ∀ dims : List Nat, ValidChainDims dims →
        ∃ f : Nat → Nat, OrderPolyCounts dims f ∧ IsRationalLinearRatio f) := by
  have hvalid : ValidChainDims [2, 2, 2] :=
    ⟨by decide, fun a ha => by simp at ha; omega⟩
  have hnot_rat : ¬ ∃ f : Nat → Nat, OrderPolyCounts [2, 2, 2] f ∧ IsRationalLinearRatio f := by
    intro ⟨f, hcnt, ⟨M0, cNum, cDen, numLin, denLin, hcDen, ⟨_, _, hden_m1⟩, heq⟩⟩
    apply omegaCube_not_rationalLinearRatio
    have hden_nz : ∀ p ∈ denLin, p.1 ≠ 0 ∨ p.2 ≠ 0 :=
      linListEval_factors_nz_of_nz hden_m1
    let m2 : Nat := M0 + 1 + maxShift denLin + 1
    refine ⟨M0 + 1, cNum, cDen, numLin, denLin, hcDen,
      ⟨m2, by omega, linListEval_nz_above_maxShift denLin m2 hden_nz (by omega)⟩, ?_⟩
    intro m hm
    have hf_eq : f m = omegaCube m :=
      HasCard.unique (hcnt m (by omega)) (omegaCube_card m)
    rw [← hf_eq]
    exact heq m (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hall
    rcases hall [2, 2, 2] hvalid with ⟨f, hcnt, hpure⟩
    exact hnot_rat ⟨f, hcnt, macmahon_imp_rationalLinear (pure_imp_macmahon hpure)⟩
  · intro hall
    rcases hall [2, 2, 2] hvalid with ⟨f, hcnt, hmac⟩
    exact hnot_rat ⟨f, hcnt, macmahon_imp_rationalLinear hmac⟩
  · intro hall
    exact hnot_rat (hall [2, 2, 2] hvalid)

/-- MASTER DISPROOF 2 (Pointwise / Fixed-Parameter Multinomial & Prime-Factor Reading):
    For `L = C_2 × C_2 × C_2` (`|L| = 8`) and `m = 4`, the exact number of order-preserving
    maps `|Hom_≤(L, C_4)| = 887` is PRIME, hence:
    (a) cannot be factored as `a * b` with `a > 1` and `b > 1`;
    (b) cannot equal any finite product of genuine (non-edge) multinomial coefficients; and
    (c) cannot equal any quotient of multinomial products whose top entries are `< 887`. -/
theorem conjecture_00000008552_pointwise_disproved :
    ∃ (dims : List Nat) (m N : Nat),
      ValidChainDims dims ∧ 1 ≤ m ∧
      HasCard (OrderHom (chainProdLattice dims).toPoset (chainLattice m).toPoset) N ∧
      IsPrimeNat N ∧
      (∀ a b : Nat, a * b = N → a = 1 ∨ b = 1) ∧
      (∀ l : List (List Nat), (∀ ks ∈ l, IsGenuineMultinomial ks) → prodMultinomials l ≠ N) ∧
      (∀ numParts denParts : List (List Nat),
        1 ≤ prodMultinomials denParts →
        (∀ ks ∈ numParts, listSum ks < N) →
        N * prodMultinomials denParts ≠ prodMultinomials numParts) := by
  refine ⟨[2, 2, 2], 4, 887, ⟨by decide, fun a ha => by simp at ha; omega⟩, by omega,
    omega_222_at_4, isPrime_887, ?_, no_genuine_multinomial_prod_eq_887, ?_⟩
  · intro a b hab
    rcases isPrime_887.2 a ⟨b, hab.symm⟩ with rfl | rfl
    · exact Or.inl rfl
    · right
      have : 887 * b = 887 * 1 := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · intro numParts denParts hden hbound heq
    exact no_bounded_multinomial_quotient_of_prime_dvd isPrime_887 ⟨1, rfl⟩
      numParts denParts hden hbound heq

/-- MASTER DISPROOF 3 (Naive d-Dimensional MacMahon Rank-Box Formula):
    For `C_2^3` (`rk` counts: `1, 3, 3, 1`) at `m = 3` and `C_2^4` (`rk` counts: `1, 4, 6, 4, 1`)
    at `m = 2`, the rank-box product `∏_{x ∈ L} (m + rk x)/(1 + rk x)` fails even to be an integer
    (`500 / 3 ≠ 168`). -/
def macmahonBoxCubeNum (m : Nat) : Nat :=
  m * (m + 1) * (m + 1) * (m + 1) * (m + 2) * (m + 2) * (m + 2) * (m + 3)

def macmahonBoxCubeDen : Nat :=
  1 * 2 * 2 * 2 * 3 * 3 * 3 * 4

def macmahonBoxHypercube4Num (m : Nat) : Nat :=
  m *
  ((m + 1) * (m + 1) * (m + 1) * (m + 1)) *
  ((m + 2) * (m + 2) * (m + 2) * (m + 2) * (m + 2) * (m + 2)) *
  ((m + 3) * (m + 3) * (m + 3) * (m + 3)) *
  (m + 4)

def macmahonBoxHypercube4Den : Nat :=
  1 * (2 * 2 * 2 * 2) * (3 * 3 * 3 * 3 * 3 * 3) * (4 * 4 * 4 * 4) * 5

theorem not_dvd_of_mod_ne_zero {a b : Nat} (h : b % a ≠ 0) : ¬ (a ∣ b) := by
  intro ⟨q, hq⟩
  have hm : b % a = 0 := by rw [hq]; exact Nat.mul_mod_right a q
  exact h hm

theorem naive_macmahon_box_disproved :
    (∀ N : Nat,
      HasCard (OrderHom (chainProdLattice [2, 2, 2]).toPoset (chainLattice 3).toPoset) N →
      macmahonBoxCubeDen * N ≠ macmahonBoxCubeNum 3) ∧
    (¬ (macmahonBoxCubeDen ∣ macmahonBoxCubeNum 3)) ∧
    (∀ N : Nat,
      HasCard (OrderHom (chainProdLattice [2, 2, 2, 2]).toPoset (chainLattice 2).toPoset) N →
      macmahonBoxHypercube4Den * N ≠ macmahonBoxHypercube4Num 2) ∧
    (¬ (macmahonBoxHypercube4Den ∣ macmahonBoxHypercube4Num 2)) := by
  refine ⟨?_, not_dvd_of_mod_ne_zero (by decide), ?_, not_dvd_of_mod_ne_zero (by decide)⟩
  · intro N hN
    have hc : omegaCube 3 = 168 := by decide
    have hNeq : N = 168 := HasCard.unique hN (hc ▸ omegaCube_card 3)
    subst hNeq
    decide
  · intro N hN
    have hNeq : N = 168 := HasCard.unique hN omega_2222_at_2
    subst hNeq
    decide

/-- MASTER DISPROOF 4 (Order-Preserving Endomorphism Reading `Hom_≤(L, L)`):
    For the 12-element chain product lattice `L = C_2 × C_2 × C_3` (`dims = [2, 2, 3]`),
    the exact count of order-preserving endomorphisms `|Hom_≤(L, L)| = 2,217,500` is divisible
    by the prime `887`, hence cannot equal any product or quotient of multinomial coefficients
    whose top arguments are `< 887` (whereas `|L| = 12` and `∑ a_i = 7`). -/
theorem conjecture_00000008552_endomorphism_disproved :
    ∃ (dims : List Nat) (N : Nat),
      ValidChainDims dims ∧
      HasCard (OrderHom (chainProdLattice dims).toPoset (chainProdLattice dims).toPoset) N ∧
      887 ∣ N ∧
      ∀ numParts denParts : List (List Nat),
        1 ≤ prodMultinomials denParts →
        (∀ ks ∈ numParts, listSum ks < 887) →
        N * prodMultinomials denParts ≠ prodMultinomials numParts := by
  refine ⟨[2, 2, 3], 2217500, ⟨by decide, fun a ha => by simp at ha; omega⟩,
    orderEnd_223_card, ⟨2500, by decide⟩, ?_⟩
  intro numParts denParts hden hbound heq
  exact no_bounded_multinomial_quotient_of_prime_dvd isPrime_887 ⟨2500, by decide⟩
    numParts denParts hden hbound heq

end Conjecture00000008552

#print axioms Conjecture00000008552.macmahon_holds_for_two_chains_witness
#print axioms Conjecture00000008552.omegaCube_card
#print axioms Conjecture00000008552.omegaCube_poly_identity
#print axioms Conjecture00000008552.conjecture_00000008552_order_polynomial_disproved
#print axioms Conjecture00000008552.conjecture_00000008552_pointwise_disproved
#print axioms Conjecture00000008552.naive_macmahon_box_disproved
#print axioms Conjecture00000008552.conjecture_00000008552_endomorphism_disproved
