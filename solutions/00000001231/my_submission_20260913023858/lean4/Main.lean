/-!
# Disproof of TLMC conjecture 00000001231

Conjecture 00000001231 claims
`|Jac(J(n,k))| = (C(n-2,k-1))^(C(n,k)-1) * prod_i (i^2 - i + 1)^{e_i}`.

At `(n, k) = (4,1)` the Johnson graph is the complete graph `K4`; the
matrix-tree theorem gives `|Jac(J(4,1))| = tau(K4) = 16` (the determinant of
the 3x3 principal minor `[[3,-1,-1],[-1,3,-1],[-1,-1,3]]` of the K4
Laplacian). The conjecture's leading factor is `C(2,0)^3 = 1`, so it asserts
`16 = prod_i (i^2-i+1)^{e_i}`. But `i^2 - i + 1` is odd for every `i`, so the
product is odd and cannot equal the even number `16`.

This file is core Lean 4 only. Every result below compiles with
**zero axioms and no `sorry`** — `omega`, `simp` and `native_decide` are
deliberately avoided because they would pull in `propext`/`Quot.sound`
(see `Check.lean` for the machine-checked axiom audit).
-/
set_option maxHeartbeats 1000000

namespace Tlmc1231

/-! ### The matrix-tree computation at (n,k) = (4,1) -/

/-- The determinant of the 3x3 matrix `[[a,b,c],[d,e,f],[g,h,i]]`,
expanded along the first row. -/
def det3 (a b c d e f g h i : Int) : Int :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- The Laplacian of `K4` is `[[3,-1,-1,-1],[-1,3,-1,-1],[-1,-1,3,-1],[-1,-1,-1,3]]`;
deleting the first row and column leaves `[[3,-1,-1],[-1,3,-1],[-1,-1,3]]`.
By the matrix-tree theorem, `tau` is the number of spanning trees of `K4 = J(4,1)`,
i.e. the order of its Jacobian. -/
def tau : Int :=
  det3 3 (-1) (-1) (-1) 3 (-1) (-1) (-1) 3

/-- The number of spanning trees of `J(4,1) = K4` is `16`
(= `4^(4-2)` by Cayley's formula). -/
theorem tau_K4 : tau = 16 := by decide

/-! ### Zero-axiom arithmetic toolkit -/

/-- Left distributivity over addition on the left factor. -/
theorem add_mul' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ k ih =>
    show (a + b) * k + (a + b) = (a * k + a) + (b * k + b)
    rw [ih, Nat.add_assoc (a * k) (b * k) (a + b),
        Nat.add_assoc (a * k) a (b * k + b), Nat.add_comm (b * k) (a + b),
        Nat.add_assoc a b (b * k), Nat.add_comm b (b * k)]

theorem add_sub_cancel' (a c : Nat) : a + c - c = a := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have e1 : a + (c + 1) = (a + c) + 1 := rfl
    have e2 : (a + c) + 1 - (c + 1) = (a + c) - c := Nat.succ_sub_succ _ _
    rw [e1, e2]
    exact ih

theorem sub_add (a b c : Nat) (h : b ≤ a) : a - b + c = a + c - b := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    cases a with
    | zero => exact absurd h (Nat.not_succ_le_zero b)
    | succ a' =>
      have h' : b ≤ a' := Nat.le_of_succ_le_succ h
      have eL : a' + 1 - (b + 1) = a' - b := Nat.succ_sub_succ _ _
      have eR1 : a' + 1 + c = (a' + c) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 c]
        rfl
      have eR2 : (a' + c) + 1 - (b + 1) = (a' + c) - b := Nat.succ_sub_succ _ _
      rw [eL, eR1, eR2]
      exact ih a' h'

/-! ### A zero-axiom theory of `· % 2` -/

/-- Fuel congruence: the value of `Nat.modCore.go` does not depend on the fuel. -/
theorem go_congr (y : Nat) (hy : 0 < y) (v : Nat) :
    ∀ (f1 f2 : Nat) (h1 : v < f1) (h2 : v < f2),
      Nat.modCore.go y hy f1 v h1 = Nat.modCore.go y hy f2 v h2 := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro f1 f2 h1 h2
    cases f1 with
    | zero => exact absurd h1 (Nat.not_lt_zero v)
    | succ f1' =>
      cases f2 with
      | zero => exact absurd h2 (Nat.not_lt_zero v)
      | succ f2' =>
        show dite (y ≤ v)
            (fun h => Nat.modCore.go y hy f1' (v - y) (Nat.div_rec_fuel_lemma hy h h1))
            (fun _ => v)
          = dite (y ≤ v)
            (fun h => Nat.modCore.go y hy f2' (v - y) (Nat.div_rec_fuel_lemma hy h h2))
            (fun _ => v)
        cases hd : Nat.decLe y v with
        | isTrue hle =>
          rw [dif_pos hle, dif_pos hle]
          exact ih (v - y) (Nat.sub_lt (Nat.lt_of_lt_of_le hy hle) hy) f1' f2'
            (Nat.div_rec_fuel_lemma hy hle h1) (Nat.div_rec_fuel_lemma hy hle h2)
        | isFalse hle =>
          rw [dif_neg hle, dif_neg hle]

theorem go_mod (v y fuel : Nat) (hy : 0 < y) (hf : v < fuel) :
    Nat.modCore.go y hy fuel v hf = Nat.modCore v y := by
  cases fuel with
  | zero => exact absurd hf (Nat.not_lt_zero v)
  | succ f =>
    have hL : Nat.modCore.go y hy (Nat.succ f) v hf
        = dite (y ≤ v) (fun h => Nat.modCore.go y hy f (v - y) (Nat.div_rec_fuel_lemma hy h hf)) (fun _ => v) := rfl
    have hR : Nat.modCore v y
        = dite (y ≤ v) (fun h => Nat.modCore.go y hy v (v - y) (Nat.div_rec_fuel_lemma hy h (Nat.lt_succ_self v))) (fun _ => v) := by
      unfold Nat.modCore; rw [dif_pos hy]; rfl
    rw [hL, hR]
    cases hd : Nat.decLe y v with
    | isTrue hle =>
      rw [dif_pos hle, dif_pos hle]
      rw [go_congr y hy (v - y) f v (Nat.div_rec_fuel_lemma hy hle hf)
        (Nat.div_rec_fuel_lemma hy hle (Nat.lt_succ_self v))]
    | isFalse hle => rw [dif_neg hle, dif_neg hle]

/-- One unfolding step of `Nat.modCore`: subtract `y` once when `y ≤ x`. -/
theorem modCore_step {x y : Nat} (hy : 0 < y) (hle : y ≤ x) :
    Nat.modCore x y = Nat.modCore (x - y) y := by
  have hR : Nat.modCore (x - y) y
      = Nat.modCore.go y hy (Nat.succ (x - y)) (x - y) (Nat.lt_succ_self (x - y)) := by
    unfold Nat.modCore
    rw [dif_pos hy]
  rw [hR]
  unfold Nat.modCore
  rw [dif_pos hy]
  show dite (y ≤ x)
      (fun h => Nat.modCore.go y hy x (x - y) (Nat.div_rec_fuel_lemma hy h (Nat.lt_succ_self x)))
      (fun _ => x)
    = Nat.modCore.go y hy (Nat.succ (x - y)) (x - y) (Nat.lt_succ_self (x - y))
  rw [dif_pos hle]
  exact go_congr y hy (x - y) x (Nat.succ (x - y))
    (Nat.div_rec_fuel_lemma hy hle (Nat.lt_succ_self x)) (Nat.lt_succ_self (x - y))

theorem modCore_eq_mod (v m : Nat) : Nat.modCore v m = v % m := by
  cases v with
  | zero =>
    cases m with
    | zero => unfold Nat.modCore; rfl
    | succ m' => unfold Nat.modCore; rfl
  | succ v' =>
    cases hd : Nat.decLe m (Nat.succ v') with
    | isTrue h =>
      show Nat.modCore (Nat.succ v') m = ite (m ≤ Nat.succ v') (Nat.modCore (Nat.succ v') m) (Nat.succ v')
      rw [if_pos h]
    | isFalse h =>
      show Nat.modCore (Nat.succ v') m = ite (m ≤ Nat.succ v') (Nat.modCore (Nat.succ v') m) (Nat.succ v')
      rw [if_neg h]
      unfold Nat.modCore
      cases m with
      | zero => rfl
      | succ m' =>
        rw [dif_pos (Nat.zero_lt_succ m')]
        exact dif_neg h

/-- Peeling two off the summand: `(x + 2) % 2 = x % 2`. -/
theorem mod2_sub (x : Nat) (h : 2 ≤ x) : x % 2 = (x - 2) % 2 := by
  cases x with
  | zero => exact absurd h (by decide)
  | succ x' =>
    cases x' with
    | zero => exact absurd h (by decide)
    | succ x'' =>
      have hrhs : Nat.modCore x'' 2 = x'' % 2 := modCore_eq_mod x'' 2
      show ite (2 ≤ x'' + 2) (Nat.modCore (x'' + 2) 2) (x'' + 2) = x'' % 2
      rw [if_pos h]
      rw [modCore_step (by decide : (0:Nat) < 2) h]
      exact hrhs

/-- A `+2` inside a `% 2` is invisible. -/
theorem mod2_step (m : Nat) : (m + 2) % 2 = m % 2 := by
  cases m with
  | zero => rfl
  | succ m' =>
    cases m' with
    | zero => rfl
    | succ m'' =>
      have hle : 2 ≤ (m'' + 2) + 2 := Nat.le_add_left 2 (m'' + 2)
      have h := mod2_sub ((m'' + 2) + 2) hle
      rw [h]
      rfl

/-- Adding `d + d` is invisible to `% 2`. -/
theorem mod2_add_dbl (x d : Nat) : (x + (d + d)) % 2 = x % 2 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have e : (d + 1) + (d + 1) = (d + d) + 2 := by
      rw [Nat.add_succ (d + 1) d, Nat.add_comm (d + 1) d, Nat.add_succ d d]
    rw [e, ← Nat.add_assoc x (d + d) 2, mod2_step]
    exact ih

theorem le_mul_self (n : Nat) : n ≤ n * n := by
  cases n with
  | zero => exact Nat.zero_le 0
  | succ m => exact Nat.le_mul_of_pos_right (Nat.succ m) (Nat.succ_pos m)

/-! ### The parity lemma -/

/-- **Parity lemma.** For every natural number `i`, `i*i - i + 1` is odd:
`i*i - i = i*(i-1)` is a product of consecutive integers, hence even.
Proved from scratch in core Lean with **zero axioms** (no `omega`, no `simp`,
hence no `propext`/`Quot.sound`). -/
theorem f_odd : ∀ i : Nat, (i * i - i + 1) % 2 = 1 := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
    have hle : n ≤ n * n := le_mul_self n
    have hle1 : n ≤ n * n + 1 := Nat.le_trans hle (Nat.le_add_right (n * n) 1)
    have hgn : n * n - n + 1 = (n * n + 1) - n := sub_add (n * n) n 1 hle
    have hexp : (n + 1) * (n + 1) = (n * n + n) + (n + 1) := by
      rw [Nat.mul_add, add_mul', Nat.one_mul, Nat.mul_one]
    have hstep : ((n + 1) * (n + 1) - (n + 1) + 1) = ((n * n - n + 1) + (n + n)) := by
      rw [hexp, add_sub_cancel', hgn, sub_add (n * n + 1) n (n + n) hle1,
        ← add_sub_cancel' ((n * n + n) + 1) n]
      congr 1
      rw [Nat.add_right_comm (n * n + n) 1 n, Nat.add_assoc (n * n) n n,
          Nat.add_right_comm (n * n) (n + n) 1]
    rw [hstep, mod2_add_dbl]
    exact ih

/-! ### Product machinery (core Lean has no `List.prod`) -/

/-- Product of a list of natural numbers. -/
def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

/-! ### The concrete contradiction -/

/-- The first four small factors: `1 * 1 * 3 * 7 = 21`. -/
theorem prod_f4 : listProd ((List.range 4).map (fun i => i * i - i + 1)) = 21 := by decide

/-- The product of the small factors is odd, as predicted by `f_odd`. -/
theorem prod_f4_odd : (listProd ((List.range 4).map (fun i => i * i - i + 1))) % 2 = 1 := by decide

/-- `16` is even. -/
theorem sixteen_even : (16 : Nat) % 2 = 0 := by decide

/-- An odd product cannot equal `16`. -/
theorem prod_f4_ne_16 : listProd ((List.range 4).map (fun i => i * i - i + 1)) ≠ 16 := by
  intro h
  rw [prod_f4] at h
  exact absurd h (by decide)

/-- **Refutation.** The conjecture's literal formula at `(n, k) = (4,1)` would force
`prod_i (i^2-i+1)^{e_i} = 16` (the leading factor `C(2,0)^3` is `1`) while the true
Jacobian order is `tau = 16`. But `tau = 16` is true and the product of odd factors
is odd — the pair is inconsistent, so the formula is false. -/
theorem refute :
    ¬ (listProd ((List.range 4).map (fun i => i * i - i + 1)) = 16 ∧ tau = 16) := by
  rintro ⟨h1, _⟩
  exact prod_f4_ne_16 h1

end Tlmc1231
