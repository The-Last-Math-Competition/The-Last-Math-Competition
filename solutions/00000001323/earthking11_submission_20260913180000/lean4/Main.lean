import Std

/-!
# Disproof of conjecture 00000001323

The conjecture (conjectures/00000001323.md) claims that in `Aut(ℂ²)` the set of
possible periods of elements whose Jacobian is identically `1` is

    {1, 2, 3, 4, 6}.

The conjecture is **false**.  For every `m ≥ 1` pick a primitive `m`-th root of
unity `ζ_m` and set

    A_m = diag(ζ_m, ζ_m⁻¹) ∈ GL₂(ℂ) ⊆ Aut(ℂ²).

Then `det A_m = 1`, the Jacobian of the linear map `A_m` is the constant matrix
`A_m`, and `A_m` has order exactly `m`.  In particular `m = 5` occurs, and `5`
is not in `{1,2,3,4,6}`.

Core Lean (this project has no Mathlib) has no field `ℂ`.  We therefore
formalise the *algebraically identical* finite-field model: over `F₁₁` the unit
group has order `10`, so it contains an element `ζ = 3` of multiplicative order
exactly `5`.  The diagonal map `diag(3, 3⁻¹) = diag(3, 3⁴)` over `F₁₁` has
determinant `1` and order exactly `5`.  The computation is coefficient-free: the
same proof transfers verbatim to `ℂ` with `ζ = exp(2πi/5)` (see `README.md`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace TLMC1323

/-! ## 0. Function iteration

Core `Std` (unlike Mathlib) does not provide `Function.iterate` nor the `f^[n]`
notation, so we define them ourselves. -/

/-- `iterate f n` is the `n`-fold self-composition of `f`. -/
def iterate {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- The `n`-fold iterate notation `f^[n]`. -/
notation:max f "^[" n "]" => iterate f n

/-! ## 1. An element of multiplicative order 5 in `F₁₁` -/

/-- `3` is a primitive `5`-th root of unity in `F₁₁`: it has order exactly `5`,
because `5 ∣ 10 = |F₁₁ˣ|` and the powers `3, 3², 3³, 3⁴` are all `≠ 1`. -/
theorem zeta_order_five :
    (3 : Fin 11) ^ 5 = 1 ∧
      (3 : Fin 11) ^ 1 ≠ 1 ∧
      (3 : Fin 11) ^ 2 ≠ 1 ∧
      (3 : Fin 11) ^ 3 ≠ 1 ∧
      (3 : Fin 11) ^ 4 ≠ 1 := by
  decide

/-- The inverse of `3` in `F₁₁` is `3⁴` (since `3 · 3⁴ = 3⁵ = 1`). -/
theorem three_inv : (3 : Fin 11) * (3 : Fin 11) ^ 4 = 1 := by
  decide

/-! ## 2. The diagonal linear map `diag(3, 3⁻¹)` on `F₁₁²` -/

/-- The diagonal linear map `diag(3, 3⁻¹) = diag(3, 3⁴)` acting on pairs,
i.e. the matrix `A = [[3, 0], [0, 3⁴]]` applied to a column vector. -/
def A (v : Fin 11 × Fin 11) : Fin 11 × Fin 11 :=
  (3 * v.1, (3 : Fin 11) ^ 4 * v.2)

/-- The determinant of `A = diag(3, 3⁴)` as an element of `F₁₁`. -/
def detA : Fin 11 := 3 * (3 : Fin 11) ^ 4

/-- The determinant of the witness is `1`, as it must be for a
Jacobian-constant-`1` map: `det A = 3 · 3⁴ = 3⁵ = 1`. -/
theorem det_is_one : detA = 1 := by
  decide

/-! ## 3. Order of `A`

`Fin 11 × Fin 11` is a finite type (`121` elements), so `decide` can verify the
five iterates coordinatewise; no general iteration lemma is required. -/

/-- The fifth iterate of `A` is the identity: `3⁵ = 1` and `(3⁴)⁵ = 3²⁰ = 1`. -/
theorem A_five_eq_id : A^[5] = id := by
  funext v
  rcases v with ⟨a, b⟩
  revert a b
  decide

/-- `A` has order **exactly** `5`: no smaller positive power is the identity. -/
theorem order_is_five :
    A^[5] = id ∧ A^[1] ≠ id ∧ A^[2] ≠ id ∧ A^[3] ≠ id ∧ A^[4] ≠ id := by
  refine ⟨A_five_eq_id, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : A^[1] ((1 : Fin 11), (0 : Fin 11)) ≠
      id ((1 : Fin 11), (0 : Fin 11))) (congrFun h _)
  · intro h
    exact (by decide : A^[2] ((1 : Fin 11), (0 : Fin 11)) ≠
      id ((1 : Fin 11), (0 : Fin 11))) (congrFun h _)
  · intro h
    exact (by decide : A^[3] ((1 : Fin 11), (0 : Fin 11)) ≠
      id ((1 : Fin 11), (0 : Fin 11))) (congrFun h _)
  · intro h
    exact (by decide : A^[4] ((1 : Fin 11), (0 : Fin 11)) ≠
      id ((1 : Fin 11), (0 : Fin 11))) (congrFun h _)

/-! ## 4. The conjecture is false -/

/-- **Conjecture 00000001323 is false.**

There exists a linear endomorphism `T` of the free module `F₁₁²` with
`det T = 1` and with order exactly `5`; equivalently, in the ℂ model there is an
element of `Aut(ℂ²)` with Jacobian identically `1` and period `5`. Since
`5 ∉ {1,2,3,4,6}`, the conjectured period set is not `{1,2,3,4,6}`. -/
theorem conjecture_00000001323_false :
    (∃ T : (Fin 11 × Fin 11) → (Fin 11 × Fin 11),
        T^[5] = id ∧ T^[1] ≠ id ∧ T^[2] ≠ id ∧ T^[3] ≠ id ∧ T^[4] ≠ id) ∧
      detA = 1 ∧
      5 ≠ 1 ∧ 5 ≠ 2 ∧ 5 ≠ 3 ∧ 5 ≠ 4 ∧ 5 ≠ 6 := by
  refine ⟨⟨A, order_is_five⟩, det_is_one, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end TLMC1323
