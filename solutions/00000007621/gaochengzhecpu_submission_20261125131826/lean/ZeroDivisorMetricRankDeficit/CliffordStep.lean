/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
 Unified orthogonal Clifford step construction for ε ∈ {0, +1, -1} and
 radical projection / exterior algebra theorems.
-/
import ZeroDivisorMetricRankDeficit.Basic

namespace ZeroDivisorMetricRankDeficit

/-- Metric generator sign mode: `zero` (`e² = 0`), `pos` (`e² = +1`), `neg` (`e² = -1`). -/
inductive SignMode where
  | zero
  | pos
  | neg
  deriving DecidableEq, Repr

namespace AssocInvolAlg

/-- Four-term associative rearrangement `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem add_add_add_comm {A : Type u} (alg : AssocInvolAlg A) (a b c d : A) :
    alg.add (alg.add a b) (alg.add c d) = alg.add (alg.add a c) (alg.add b d) := by
  calc
    alg.add (alg.add a b) (alg.add c d)
      = alg.add a (alg.add b (alg.add c d)) := alg.add_assoc a b (alg.add c d)
    _ = alg.add a (alg.add (alg.add b c) d) := by rw [← alg.add_assoc b c d]
    _ = alg.add a (alg.add (alg.add c b) d) := by rw [alg.add_comm b c]
    _ = alg.add a (alg.add c (alg.add b d)) := by rw [alg.add_assoc c b d]
    _ = alg.add (alg.add a c) (alg.add b d) := (alg.add_assoc a c (alg.add b d)).symm

/-- Action of a metric sign `ε ∈ {0, +1, -1}` on an algebra `A`. -/
def signAct {A : Type u} (alg : AssocInvolAlg A) : SignMode → A → A
  | .zero, _ => alg.zero
  | .pos, x => x
  | .neg, x => alg.neg x

theorem signAct_zero {A : Type u} (alg : AssocInvolAlg A) (s : SignMode) :
    alg.signAct s alg.zero = alg.zero := by
  cases s with
  | zero => rfl
  | pos => rfl
  | neg => exact alg.neg_zero

theorem signAct_add {A : Type u} (alg : AssocInvolAlg A) (s : SignMode) (x y : A) :
    alg.signAct s (alg.add x y) = alg.add (alg.signAct s x) (alg.signAct s y) := by
  cases s with
  | zero => exact (alg.add_zero alg.zero).symm
  | pos => rfl
  | neg => exact alg.neg_add x y

theorem signAct_mul_left {A : Type u} (alg : AssocInvolAlg A) (s : SignMode) (x y : A) :
    alg.mul (alg.signAct s x) y = alg.signAct s (alg.mul x y) := by
  cases s with
  | zero => exact alg.zero_mul y
  | pos => rfl
  | neg => exact alg.neg_mul x y

theorem signAct_mul_right {A : Type u} (alg : AssocInvolAlg A) (s : SignMode) (x y : A) :
    alg.mul x (alg.signAct s y) = alg.signAct s (alg.mul x y) := by
  cases s with
  | zero => exact alg.mul_zero x
  | pos => rfl
  | neg => exact alg.mul_neg x y

theorem invl_signAct {A : Type u} (alg : AssocInvolAlg A) (s : SignMode) (x : A) :
    alg.invl (alg.signAct s x) = alg.signAct s (alg.invl x) := by
  cases s with
  | zero => exact alg.invl_zero
  | pos => rfl
  | neg => exact alg.invl_neg x

/--
Orthogonal Clifford extension `A ⊕ A·e` adjoining a generator `e = (0, 1)` that
anticommutes with odd elements (`e · u = invl(u) · e`) and satisfies `e² = ε · 1`.
-/
def cliffordStep {A : Type u} (s : SignMode) (alg : AssocInvolAlg A) : AssocInvolAlg (A × A) where
  zero := (alg.zero, alg.zero)
  one := (alg.one, alg.zero)
  add x y := (alg.add x.1 y.1, alg.add x.2 y.2)
  neg x := (alg.neg x.1, alg.neg x.2)
  mul x y :=
    ( alg.add (alg.mul x.1 y.1) (alg.signAct s (alg.mul x.2 (alg.invl y.2))),
      alg.add (alg.mul x.1 y.2) (alg.mul x.2 (alg.invl y.1)) )
  invl x := (alg.invl x.1, alg.neg (alg.invl x.2))
  zero_ne_one := by
    intro h
    exact alg.zero_ne_one (congrArg Prod.fst h)
  add_assoc a b c := Prod.ext (alg.add_assoc a.1 b.1 c.1) (alg.add_assoc a.2 b.2 c.2)
  add_comm a b := Prod.ext (alg.add_comm a.1 b.1) (alg.add_comm a.2 b.2)
  zero_add a := Prod.ext (alg.zero_add a.1) (alg.zero_add a.2)
  add_zero a := Prod.ext (alg.add_zero a.1) (alg.add_zero a.2)
  neg_add_cancel a := Prod.ext (alg.neg_add_cancel a.1) (alg.neg_add_cancel a.2)
  mul_assoc a b c := by
    apply Prod.ext
    · dsimp only
      have hL :
          alg.add
            (alg.mul (alg.add (alg.mul a.1 b.1) (alg.signAct s (alg.mul a.2 (alg.invl b.2)))) c.1)
            (alg.signAct s (alg.mul (alg.add (alg.mul a.1 b.2) (alg.mul a.2 (alg.invl b.1))) (alg.invl c.2)))
          =
          alg.add
            (alg.add (alg.mul a.1 (alg.mul b.1 c.1))
                     (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.1))))
            (alg.add (alg.signAct s (alg.mul a.1 (alg.mul b.2 (alg.invl c.2))))
                     (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.2))))) := by
        rw [alg.right_distrib, alg.mul_assoc a.1 b.1 c.1, alg.signAct_mul_left,
            alg.mul_assoc a.2 (alg.invl b.2) c.1]
        rw [alg.right_distrib (alg.mul a.1 b.2) (alg.mul a.2 (alg.invl b.1)) (alg.invl c.2),
            alg.mul_assoc a.1 b.2 (alg.invl c.2),
            alg.mul_assoc a.2 (alg.invl b.1) (alg.invl c.2),
            alg.signAct_add]
      have hR :
          alg.add
            (alg.mul a.1 (alg.add (alg.mul b.1 c.1) (alg.signAct s (alg.mul b.2 (alg.invl c.2)))))
            (alg.signAct s (alg.mul a.2 (alg.invl (alg.add (alg.mul b.1 c.2) (alg.mul b.2 (alg.invl c.1))))))
          =
          alg.add
            (alg.add (alg.mul a.1 (alg.mul b.1 c.1))
                     (alg.signAct s (alg.mul a.1 (alg.mul b.2 (alg.invl c.2)))))
            (alg.add (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.2))))
                     (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.1)))) := by
        rw [alg.left_distrib a.1, alg.signAct_mul_right s a.1]
        rw [alg.invl_add, alg.invl_mul, alg.invl_mul, alg.invl_invl c.1]
        rw [alg.left_distrib a.2, alg.signAct_add]
      rw [hL, hR]
      rw [alg.add_comm (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.2))))
                       (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.1)))]
      exact alg.add_add_add_comm _ _ _ _
    · dsimp only
      have hL :
          alg.add
            (alg.mul (alg.add (alg.mul a.1 b.1) (alg.signAct s (alg.mul a.2 (alg.invl b.2)))) c.2)
            (alg.mul (alg.add (alg.mul a.1 b.2) (alg.mul a.2 (alg.invl b.1))) (alg.invl c.1))
          =
          alg.add
            (alg.add (alg.mul a.1 (alg.mul b.1 c.2))
                     (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.2))))
            (alg.add (alg.mul a.1 (alg.mul b.2 (alg.invl c.1)))
                     (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.1)))) := by
        rw [alg.right_distrib, alg.mul_assoc a.1 b.1 c.2, alg.signAct_mul_left,
            alg.mul_assoc a.2 (alg.invl b.2) c.2]
        rw [alg.right_distrib (alg.mul a.1 b.2) (alg.mul a.2 (alg.invl b.1)) (alg.invl c.1),
            alg.mul_assoc a.1 b.2 (alg.invl c.1),
            alg.mul_assoc a.2 (alg.invl b.1) (alg.invl c.1)]
      have hR :
          alg.add
            (alg.mul a.1 (alg.add (alg.mul b.1 c.2) (alg.mul b.2 (alg.invl c.1))))
            (alg.mul a.2 (alg.invl (alg.add (alg.mul b.1 c.1) (alg.signAct s (alg.mul b.2 (alg.invl c.2))))))
          =
          alg.add
            (alg.add (alg.mul a.1 (alg.mul b.1 c.2))
                     (alg.mul a.1 (alg.mul b.2 (alg.invl c.1))))
            (alg.add (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.1)))
                     (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.2)))) := by
        rw [alg.left_distrib a.1]
        rw [alg.invl_add, alg.invl_mul, alg.invl_signAct, alg.invl_mul, alg.invl_invl c.2]
        rw [alg.left_distrib a.2, alg.signAct_mul_right s a.2]
      rw [hL, hR]
      rw [alg.add_comm (alg.mul a.2 (alg.mul (alg.invl b.1) (alg.invl c.1)))
                       (alg.signAct s (alg.mul a.2 (alg.mul (alg.invl b.2) c.2)))]
      exact alg.add_add_add_comm _ _ _ _
  one_mul a := by
    apply Prod.ext <;> dsimp only
    · rw [alg.one_mul, alg.zero_mul, alg.signAct_zero, alg.add_zero]
    · rw [alg.one_mul, alg.zero_mul, alg.add_zero]
  mul_one a := by
    apply Prod.ext <;> dsimp only
    · rw [alg.mul_one, alg.invl_zero, alg.mul_zero, alg.signAct_zero, alg.add_zero]
    · rw [alg.mul_zero, alg.invl_one, alg.mul_one, alg.zero_add]
  left_distrib a b c := by
    apply Prod.ext <;> dsimp only
    · rw [alg.left_distrib, alg.invl_add, alg.left_distrib, alg.signAct_add]
      exact (alg.add_add_add_comm _ _ _ _).symm
    · rw [alg.left_distrib, alg.invl_add, alg.left_distrib]
      exact (alg.add_add_add_comm _ _ _ _).symm
  right_distrib a b c := by
    apply Prod.ext <;> dsimp only
    · rw [alg.right_distrib, alg.right_distrib, alg.signAct_add]
      exact (alg.add_add_add_comm _ _ _ _).symm
    · rw [alg.right_distrib, alg.right_distrib]
      exact (alg.add_add_add_comm _ _ _ _).symm
  invl_invl a := by
    apply Prod.ext <;> dsimp only
    · exact alg.invl_invl a.1
    · rw [alg.invl_neg, alg.neg_neg, alg.invl_invl]
  invl_zero := Prod.ext alg.invl_zero (by dsimp only; rw [alg.invl_zero, alg.neg_zero])
  invl_one := Prod.ext alg.invl_one (by dsimp only; rw [alg.invl_zero, alg.neg_zero])
  invl_add a b := by
    apply Prod.ext <;> dsimp only
    · exact alg.invl_add a.1 b.1
    · rw [alg.invl_add, alg.neg_add]
  invl_neg a := by
    apply Prod.ext <;> dsimp only
    · exact alg.invl_neg a.1
    · rw [alg.invl_neg]
  invl_mul a b := by
    apply Prod.ext <;> dsimp only
    · rw [alg.invl_add, alg.invl_mul, alg.invl_signAct, alg.invl_mul, alg.invl_invl b.2]
      rw [alg.invl_neg, alg.invl_invl b.2, alg.neg_mul_neg]
    · rw [alg.invl_add, alg.neg_add, alg.invl_mul, alg.invl_mul, alg.invl_invl b.1]
      rw [alg.mul_neg, alg.neg_mul]

/-- The newly adjoined generator `e = (0, 1)` satisfies `e² = (signAct s 1, 0)`. -/
theorem cliffordStep_gen_sq {A : Type u} (s : SignMode) (alg : AssocInvolAlg A) :
    (alg.cliffordStep s).mul (alg.zero, alg.one) (alg.zero, alg.one) =
      (alg.signAct s alg.one, alg.zero) := by
  apply Prod.ext <;> dsimp only [cliffordStep]
  · rw [alg.zero_mul, alg.invl_one, alg.one_mul, alg.zero_add]
  · rw [alg.zero_mul, alg.invl_zero, alg.mul_zero, alg.add_zero]

/-!
## 2. Radical Extension (`s = .zero`, `e² = 0`) & Metric Nullity Reduction Theorem

When adjoining a degenerate generator `e` (`e² = 0`) to any `alg : AssocInvolAlg A`,
an element `(u, v)` has a two-sided inverse iff `u` has a two-sided inverse, and is a
zero divisor iff `u` is a zero divisor (whenever `alg` satisfies the unit/zero-divisor dichotomy).
-/

abbrev radStep {A : Type u} (alg : AssocInvolAlg A) : AssocInvolAlg (A × A) :=
  alg.cliffordStep .zero

theorem radStep_mul_eq {A : Type u} (alg : AssocInvolAlg A) (x y : A × A) :
    alg.radStep.mul x y =
      (alg.mul x.1 y.1, alg.add (alg.mul x.1 y.2) (alg.mul x.2 (alg.invl y.1))) := by
  apply Prod.ext
  · dsimp only [radStep, cliffordStep, signAct]
    exact alg.add_zero (alg.mul x.1 y.1)
  · rfl

/-- Explicit two-sided inverse lift across a nilpotent radical step `A ⊕ A·e` (`e² = 0`). -/
theorem radStep_hasTwoSidedInv {A : Type u} (alg : AssocInvolAlg A) {u : A} (v : A)
    (hInv : HasTwoSidedInv alg.one alg.mul u) :
    HasTwoSidedInv alg.radStep.one alg.radStep.mul (u, v) := by
  rcases hInv with ⟨uInv, huR, huL⟩
  let w : A := alg.neg (alg.mul (alg.mul uInv v) (alg.invl uInv))
  refine ⟨(uInv, w), ?_, ?_⟩
  · rw [radStep_mul_eq]
    apply Prod.ext <;> dsimp only [radStep, cliffordStep]
    · exact huR
    · have h1 : alg.mul u w = alg.neg (alg.mul v (alg.invl uInv)) := by
        dsimp only [w]
        rw [alg.mul_neg, ← alg.mul_assoc u (alg.mul uInv v) (alg.invl uInv),
            ← alg.mul_assoc u uInv v, huR, alg.one_mul]
      rw [h1, alg.neg_add_cancel]
  · rw [radStep_mul_eq]
    apply Prod.ext <;> dsimp only [radStep, cliffordStep]
    · exact huL
    · have h1 : alg.mul w (alg.invl u) = alg.neg (alg.mul uInv v) := by
        dsimp only [w]
        rw [alg.neg_mul, alg.mul_assoc (alg.mul uInv v) (alg.invl uInv) (alg.invl u),
            ← alg.invl_mul uInv u, huL, alg.invl_one, alg.mul_one]
      rw [h1, alg.add_neg_cancel]

/-- Zero divisors in `A` lift to zero divisors in `A ⊕ A·e` for arbitrary radical component `v`. -/
theorem radStep_isZeroDivisor_of_base {A : Type u} (alg : AssocInvolAlg A) {u : A} (v : A)
    (hZD : IsZeroDivisor alg.zero alg.mul u) :
    IsZeroDivisor alg.radStep.zero alg.radStep.mul (u, v) := by
  rcases hZD with ⟨y, hyNe, hMul | hMul⟩
  · refine ⟨(alg.zero, y), ?_, Or.inl ?_⟩
    · intro hEq
      exact hyNe (congrArg Prod.snd hEq)
    · rw [radStep_mul_eq]
      apply Prod.ext <;> dsimp only [radStep, cliffordStep]
      · exact alg.mul_zero u
      · rw [hMul, alg.invl_zero, alg.mul_zero, alg.add_zero]
  · refine ⟨(alg.zero, alg.invl y), ?_, Or.inr ?_⟩
    · intro hEq
      have hInvZ : alg.invl y = alg.zero := congrArg Prod.snd hEq
      exact hyNe ((alg.invl_eq_zero_iff y).mp hInvZ)
    · rw [radStep_mul_eq]
      apply Prod.ext <;> dsimp only [radStep, cliffordStep]
      · exact alg.zero_mul u
      · rw [alg.zero_mul, alg.zero_add, ← alg.invl_mul, hMul, alg.invl_zero]

/-- Dichotomy property: every element is either a zero divisor or two-sided invertible. -/
def HasDichotomy {A : Type u} (alg : AssocInvolAlg A) : Prop :=
  ∀ x : A, IsZeroDivisor alg.zero alg.mul x ∨ HasTwoSidedInv alg.one alg.mul x

theorem radStep_dichotomy {A : Type u} (alg : AssocInvolAlg A) (hDic : HasDichotomy alg) :
    HasDichotomy alg.radStep := by
  intro ⟨u, v⟩
  rcases hDic u with hZD | hInv
  · exact Or.inl (radStep_isZeroDivisor_of_base alg v hZD)
  · exact Or.inr (radStep_hasTwoSidedInv alg v hInv)

theorem radStep_isZeroDivisor_iff {A : Type u} (alg : AssocInvolAlg A) (hDic : HasDichotomy alg)
    (x : A × A) :
    IsZeroDivisor alg.radStep.zero alg.radStep.mul x ↔ IsZeroDivisor alg.zero alg.mul x.1 := by
  constructor
  · intro hZD
    rcases hDic x.1 with hBaseZD | hBaseInv
    · exact hBaseZD
    · exfalso
      exact alg.radStep.not_isZeroDivisor_of_inv (radStep_hasTwoSidedInv alg x.2 hBaseInv) hZD
  · intro hBaseZD
    exact radStep_isZeroDivisor_of_base alg x.2 hBaseZD

/-!
## 3. Iterated Radical Extension (`r` Null Generators) & Exterior Algebra `Λ(K^r)`
-/

/-- Carrier of `r`-fold radical extension adjoining `r` anticommuting null generators (`g_k² = 0`). -/
@[reducible] def RadIter (r : Nat) (A : Type u) : Type u :=
  match r with
  | 0 => A
  | m + 1 => RadIter m A × RadIter m A

/-- Algebra structure on `RadIter r A`. -/
def radIterAlg {A : Type u} (r : Nat) (alg : AssocInvolAlg A) : AssocInvolAlg (RadIter r A) :=
  match r with
  | 0 => alg
  | m + 1 => (radIterAlg m alg).radStep

/-- Canonical quotient projection `RadIter r A → A` modulo the nilpotent radical ideal `J`. -/
def radProj {A : Type u} : (r : Nat) → RadIter r A → A
  | 0, x => x
  | m + 1, x => radProj m x.1

theorem radIter_dichotomy {A : Type u} (r : Nat) (alg : AssocInvolAlg A) (hDic : HasDichotomy alg) :
    HasDichotomy (radIterAlg r alg) := by
  induction r with
  | zero => exact hDic
  | succ m ih => exact radStep_dichotomy (radIterAlg m alg) ih

/--
**Master Radical Reduction Theorem:** Adjoining `r` degenerate metric directions (`g_k² = 0`)
satisfies `x ∈ Z(Cl_{p,q,r}(K)) ↔ π(x) ∈ Z(Cl_{p,q}(K))`. Thus `Z` is the full preimage of
`Z(Cl_{p,q}(K))` under `π`, preserving codimension independently of the nullity `r`.
-/
theorem radIter_isZeroDivisor_iff {A : Type u} (r : Nat) (alg : AssocInvolAlg A)
    (hDic : HasDichotomy alg) (x : RadIter r A) :
    IsZeroDivisor (radIterAlg r alg).zero (radIterAlg r alg).mul x ↔
      IsZeroDivisor alg.zero alg.mul (radProj r x) := by
  induction r with
  | zero => exact Iff.rfl
  | succ m ih =>
    have hDicM := radIter_dichotomy m alg hDic
    exact Iff.trans (radStep_isZeroDivisor_iff (radIterAlg m alg) hDicM x) (ih x.1)

/-!
## 4. Purely Degenerate Exterior Algebra `Λ(K^r) = Cl_{0,0,r}(K)`
-/

/-- The exterior algebra `Λ(K^r) = Cl_{0,0,r}(K)` over any field `K` (`FieldOps K`). -/
abbrev ExtAlg (K : Type u) (r : Nat) : Type u := RadIter r K

abbrev extAlg (K : Type u) [FieldOps K] (r : Nat) : AssocInvolAlg (ExtAlg K r) :=
  radIterAlg r (FieldOps.toAssocInvolAlg K)

/-- Grade-0 scalar component `x₀ : K` of `x ∈ Λ(K^r)`. -/
def scalarPart {K : Type u} (r : Nat) (x : ExtAlg K r) : K :=
  radProj r x

/--
**Exterior Algebra Zero-Divisor Classification:**
For every `r : Nat` and every field `K`, `x ∈ Λ(K^r)` is a zero divisor iff `scalarPart r x = 0`.
Hence for `r ≥ 1`, `Z(Λ(K^r)) = Λ⁺(K^r)` is a linear hyperplane of dimension `2^r - 1`
(codimension `1`), identical in codimension to split nondegenerate Clifford algebras (`r = 0`).
-/
theorem extAlg_isZeroDivisor_iff (K : Type u) [FieldOps K] (r : Nat) (x : ExtAlg K r) :
    IsZeroDivisor (extAlg K r).zero (extAlg K r).mul x ↔ scalarPart r x = 0 := by
  have h1 := radIter_isZeroDivisor_iff r (FieldOps.toAssocInvolAlg K) FieldOps.field_dichotomy x
  exact Iff.trans h1 (FieldOps.field_isZeroDivisor_iff (scalarPart r x))

theorem scalarPart_invl (K : Type u) [FieldOps K] :
    ∀ (r : Nat) (x : ExtAlg K r), scalarPart r ((extAlg K r).invl x) = scalarPart r x
  | 0, _ => rfl
  | m + 1, x => scalarPart_invl K m x.1

/-- Top exterior basis blade `e₁ ∧ ⋯ ∧ e_r ∈ Λ(K^r)`. -/
def topMonomial (K : Type u) [FieldOps K] : (r : Nat) → ExtAlg K r
  | 0 => (1 : K)
  | m + 1 => ((extAlg K m).zero, topMonomial K m)

theorem topMonomial_ne_zero (K : Type u) [FieldOps K] :
    ∀ r : Nat, topMonomial K r ≠ (extAlg K r).zero
  | 0 => FieldOps.zero_ne_one.symm
  | m + 1 => by
    intro h
    exact topMonomial_ne_zero K m (congrArg Prod.snd h)

theorem scalarPart_topMonomial_succ (K : Type u) [FieldOps K] (m : Nat) :
    scalarPart (m + 1) (topMonomial K (m + 1)) = 0 := by
  dsimp only [scalarPart, radProj, topMonomial]
  induction m with
  | zero => rfl
  | succ k ih => exact ih

/-- Right annihilator of `topMonomial K r` is the entire maximal ideal `scalarPart r y = 0`. -/
theorem inRightAnn_topMonomial_iff (K : Type u) [FieldOps K] :
    ∀ (r : Nat) (y : ExtAlg K r),
      InRightAnn (extAlg K r).zero (extAlg K r).mul (topMonomial K r) y ↔ scalarPart r y = 0
  | 0, y => by
    change (1 : K) * y = 0 ↔ y = 0
    rw [FieldOps.one_mul]
  | m + 1, y => by
    let algM := extAlg K m
    change (algM.radStep.mul (algM.zero, topMonomial K m) y = algM.radStep.zero) ↔
           scalarPart m y.1 = 0
    rw [radStep_mul_eq]
    have hz : algM.mul algM.zero y.1 = algM.zero := algM.zero_mul y.1
    have hz2 : algM.mul algM.zero y.2 = algM.zero := algM.zero_mul y.2
    constructor
    · intro hEq
      have hSnd := congrArg Prod.snd hEq
      dsimp only [radStep, cliffordStep] at hSnd
      rw [hz2, algM.zero_add] at hSnd
      have hRec := (inRightAnn_topMonomial_iff K m (algM.invl y.1)).mp hSnd
      rw [scalarPart_invl K m y.1] at hRec
      exact hRec
    · intro hScal
      have hScalInv : scalarPart m (algM.invl y.1) = 0 := by
        rw [scalarPart_invl K m y.1]
        exact hScal
      have hRec := (inRightAnn_topMonomial_iff K m (algM.invl y.1)).mpr hScalInv
      dsimp only [InRightAnn] at hRec
      apply Prod.ext <;> dsimp only [radStep, cliffordStep]
      · exact hz
      · rw [hz2, algM.zero_add, hRec]

/-- Last exterior generator `e_{m+1} = (0, 1) ∈ Λ(K^{m+1})`. -/
def lastGen (K : Type u) [FieldOps K] (m : Nat) : ExtAlg K (m + 1) :=
  ((extAlg K m).zero, (extAlg K m).one)

theorem lastGen_ne_zero (K : Type u) [FieldOps K] (m : Nat) :
    lastGen K m ≠ (extAlg K (m + 1)).zero := by
  intro h
  exact (extAlg K m).zero_ne_one.symm (congrArg Prod.snd h)

theorem scalarPart_lastGen (K : Type u) [FieldOps K] (m : Nat) :
    scalarPart (m + 1) (lastGen K m) = 0 := by
  dsimp only [scalarPart, radProj, lastGen]
  induction m with
  | zero => rfl
  | succ k ih => exact ih

/-- Right annihilator of `e_{m+1}` is precisely `{ (0, v) : v ∈ Λ(K^m) }` (`y.1 = 0`). -/
theorem inRightAnn_lastGen_iff (K : Type u) [FieldOps K] (m : Nat) (y : ExtAlg K (m + 1)) :
    InRightAnn (extAlg K (m + 1)).zero (extAlg K (m + 1)).mul (lastGen K m) y ↔
      y.1 = (extAlg K m).zero := by
  let algM := extAlg K m
  change (algM.radStep.mul (algM.zero, algM.one) y = algM.radStep.zero) ↔ y.1 = algM.zero
  rw [radStep_mul_eq]
  constructor
  · intro hEq
    have hSnd := congrArg Prod.snd hEq
    dsimp only [radStep, cliffordStep] at hSnd
    rw [algM.zero_mul, algM.zero_add, algM.one_mul] at hSnd
    exact (algM.invl_eq_zero_iff y.1).mp hSnd
  · intro hy1
    apply Prod.ext <;> dsimp only [radStep, cliffordStep]
    · exact algM.zero_mul y.1
    · rw [algM.zero_mul, algM.zero_add, algM.one_mul, hy1, algM.invl_zero]

/--
**Non-Constancy of Annihilator Nullity in `Λ(K^r)` (`r ≥ 2`):**
For every `r = k + 2 ≥ 2`, `topMonomial K (k + 2)` and `lastGen K (k + 1)` are both nonzero
zero divisors in `Λ(K^{k+2})`, yet `(lastGen K k, 0)` annihilates `topMonomial` without
annihilating `lastGen`. (Over `𝔽_q`, `|Ann_R(lastGen)| = q^{2^{r-1}} < q^{2^r - 1} = |Ann_R(topMonomial)|`.)
-/
theorem extAlg_annihilator_nonconstant (K : Type u) [FieldOps K] (k : Nat) :
    let r := k + 2
    let witness : ExtAlg K r := (lastGen K k, (extAlg K (k + 1)).zero)
    IsZeroDivisor (extAlg K r).zero (extAlg K r).mul (topMonomial K r) ∧
    IsZeroDivisor (extAlg K r).zero (extAlg K r).mul (lastGen K (k + 1)) ∧
    InRightAnn (extAlg K r).zero (extAlg K r).mul (topMonomial K r) witness ∧
    ¬ InRightAnn (extAlg K r).zero (extAlg K r).mul (lastGen K (k + 1)) witness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (extAlg_isZeroDivisor_iff K (k + 2) (topMonomial K (k + 2))).mpr
      (scalarPart_topMonomial_succ K (k + 1))
  · exact (extAlg_isZeroDivisor_iff K (k + 2) (lastGen K (k + 1))).mpr
      (scalarPart_lastGen K (k + 1))
  · rw [inRightAnn_topMonomial_iff]
    exact scalarPart_lastGen K k
  · rw [inRightAnn_lastGen_iff]
    exact lastGen_ne_zero K k

end AssocInvolAlg

end ZeroDivisorMetricRankDeficit
