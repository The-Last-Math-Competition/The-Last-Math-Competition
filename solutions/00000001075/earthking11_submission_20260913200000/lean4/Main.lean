/-
  Disproof of conjecture 00000001075.

    Definition: the entropic uncertainty principle for the finite-field
                Fourier transform states #supp(f) + #supp(f_hat) >= q + 1.
    Conjecture: equality holds exactly for Fourier translates of affine
                functions a*x + b (support pairs of q and 1), and no other
                equality configurations exist.

  Counterexample (q = 5): f = delta_0 - delta_1 on Z/5, i.e. f = (1,-1,0,0,0).

    * #supp(f) = 2.
    * f_hat(xi) = 1 - omega^xi, which vanishes only at xi = 0, so
      #supp(f_hat) = 4.
    * Hence #supp(f) + #supp(f_hat) = 6 = 5 + 1: an equality configuration,
      with support pair (2,4) rather than the claimed (5,1).
    * f has three zeros while a nonzero affine function on Z/5 has exactly
      one, and a constant nonzero affine function has none; time-frequency
      translates preserve the zero set, so f is not such a translate.

  Everything below is core Lean (`import Std`, no Mathlib, no `sorry`).  The
  arithmetic is carried out exactly in Z[omega] = Z[x]/(x^4+x^3+x^2+x+1),
  represented as integer 4-tuples, so there is no floating point anywhere.

  The only proof method is `decide`/`rw`, hence the only axiom used is
  `propext`; there is no `sorryAx` and no `Lean.ofReduceBool`.
-/

import Std

namespace Tlmc1075

/-- Z[omega] with omega^4 = -(1 + omega + omega^2 + omega^3), i.e. the ring of
integers of Q(omega) for omega a primitive fifth root of unity. -/
structure Q4 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving DecidableEq, Repr

/-- Coefficientwise addition. -/
def Q4.add (a b : Q4) : Q4 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

/-- Multiplication in Z[omega].  With `r0 .. r6` the plain convolution
coefficients and `omega^4 = -(1 + omega + omega^2 + omega^3)` (so that
`omega^5 = 1`, `omega^6 = omega`), the reduced tuple is
`<r0 - r4 + r5, r1 - r4 + r6, r2 - r4, r3 - r4>`. -/
def Q4.mul (a b : Q4) : Q4 :=
  let r0 := a.c0 * b.c0
  let r1 := a.c0 * b.c1 + a.c1 * b.c0
  let r2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let r3 := a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0
  let r4 := a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1
  let r5 := a.c2 * b.c3 + a.c3 * b.c2
  let r6 := a.c3 * b.c3
  ⟨r0 - r4 + r5, r1 - r4 + r6, r2 - r4, r3 - r4⟩

instance : Add Q4 where add := Q4.add
instance : Mul Q4 where mul := Q4.mul

/-- Zero of Z[omega]. -/
def Q4.zero : Q4 := ⟨0, 0, 0, 0⟩
/-- One of Z[omega]. -/
def Q4.one : Q4 := ⟨1, 0, 0, 0⟩

instance : Zero Q4 where zero := Q4.zero
instance : One Q4 where one := Q4.one

/-- The embedding Z -> Z[omega] as scalar multiples of 1. -/
def scalar (n : Int) : Q4 := ⟨n, 0, 0, 0⟩

/-- omega itself. -/
def w : Q4 := ⟨0, 1, 0, 0⟩

/-- `omega^k`, reduced using `k % 5`. -/
def wpow (k : Nat) : Q4 :=
  match k % 5 with
  | 0 => Q4.one
  | 1 => w
  | 2 => w * w
  | 3 => w * (w * w)
  | _ => ⟨-1, -1, -1, -1⟩

/-- Sum of a function on the five residues. -/
def sum5 (g : Fin 5 → Q4) : Q4 :=
  g 0 + g 1 + g 2 + g 3 + g 4

/-- The finite-field Fourier transform over Z[omega]:
`f_hat(xi) = sum_x f(x) omega^(xi*x)`. -/
def dft (f : Fin 5 → Int) (ξ : Fin 5) : Q4 :=
  sum5 (fun x => scalar (f x) * wpow (ξ.val * x.val))

/-- The same transform for Z[omega]-valued inputs (needed for the transform of
a time-frequency translate). -/
def dftQ (f : Fin 5 → Q4) (ξ : Fin 5) : Q4 :=
  sum5 (fun x => f x * wpow (ξ.val * x.val))

/-- The witness `f = (1, -1, 0, 0, 0) = delta_0 - delta_1`. -/
def witness (x : Fin 5) : Int :=
  if x = 0 then 1 else if x = 1 then -1 else 0

/-- Support size of an integer-valued function on the five residues. -/
def suppInt (f : Fin 5 → Int) : Nat :=
  (if f 0 = 0 then 0 else 1) + (if f 1 = 0 then 0 else 1) +
  (if f 2 = 0 then 0 else 1) + (if f 3 = 0 then 0 else 1) +
  (if f 4 = 0 then 0 else 1)

/-- Support size of a Z[omega]-valued function on the five residues. -/
def suppQ (g : Fin 5 → Q4) : Nat :=
  (if g 0 = Q4.zero then 0 else 1) + (if g 1 = Q4.zero then 0 else 1) +
  (if g 2 = Q4.zero then 0 else 1) + (if g 3 = Q4.zero then 0 else 1) +
  (if g 4 = Q4.zero then 0 else 1)

/-- `x |-> a*x + b` on Z/5, embedded in Z[omega]. -/
def affineVec (a b : Fin 5) : Fin 5 → Q4 :=
  fun x => scalar (Int.ofNat (a * x + b).val)

/-- Time-frequency translate `x |-> omega^(beta*x) * h(x + alpha)`, the general
"Fourier translate" shape appearing in the conjecture. -/
def tfTrans (h : Fin 5 → Q4) (α β : Fin 5) : Fin 5 → Q4 :=
  fun x => wpow (β.val * x.val) * h (x + α)

-- ---------------------------------------------------------------------------
-- The witness is an equality configuration
-- ---------------------------------------------------------------------------

/-- `#supp(f) = 2` for the witness. -/
theorem witness_supp : suppInt witness = 2 := by decide

/-- `#supp(f_hat) = 4` for the witness: `f_hat(xi) = 1 - omega^xi`, which
vanishes only at `xi = 0`. -/
theorem witness_fhat_supp : suppQ (dft witness) = 4 := by decide

/-- The witness attains equality `#supp(f) + #supp(f_hat) = q + 1 = 6`. -/
theorem witness_equality : suppInt witness + suppQ (dft witness) = 6 := by
  rw [witness_supp, witness_fhat_supp]

/-- The explicit transform values behind `witness_fhat_supp`: `f_hat(0) = 0`
and `f_hat(xi) = 1 - omega^xi != 0` for `xi != 0`. -/
theorem witness_fhat_values :
    dft witness 0 = Q4.zero
    ∧ dft witness 1 = ⟨1, -1, 0, 0⟩
    ∧ dft witness 2 = ⟨1, 0, -1, 0⟩
    ∧ dft witness 3 = ⟨1, 0, 0, -1⟩
    ∧ dft witness 4 = ⟨2, 1, 1, 1⟩ := by decide

-- ---------------------------------------------------------------------------
-- No time-frequency translate of an affine function is the witness
-- ---------------------------------------------------------------------------

/-- For every affine `a*x+b` and every time-frequency translate thereof, the
translate is not (pointwise, as a Z[omega]-valued function) the witness.
This formalises the zero-count refutation: a nonzero affine function on Z/5
has exactly one zero and a nonzero constant has none, while the witness has
three zeros, and translates preserve the zero set. -/
theorem not_tfTrans_affine :
    ∀ (a b α β : Fin 5),
      ¬ (∀ x : Fin 5, tfTrans (affineVec a b) α β x = scalar (witness x)) := by
  decide

/-- The same non-membership for the transform of a time-frequency translate of
an affine function. -/
theorem not_tfTrans_affine_dft :
    ∀ (a b α β : Fin 5),
      ¬ (∀ x : Fin 5, dftQ (tfTrans (affineVec a b) α β) x = scalar (witness x)) := by
  decide

/-- The collected disproof: the witness is an equality configuration and is not
a time-frequency translate of any affine function (nor is the transform of
one). -/
theorem conjecture_00000001075_refuted :
    suppInt witness = 2
    ∧ suppQ (dft witness) = 4
    ∧ suppInt witness + suppQ (dft witness) = 6
    ∧ (∀ (a b α β : Fin 5),
        ¬ (∀ x : Fin 5, tfTrans (affineVec a b) α β x = scalar (witness x)))
    ∧ (∀ (a b α β : Fin 5),
        ¬ (∀ x : Fin 5, dftQ (tfTrans (affineVec a b) α β) x = scalar (witness x))) :=
  ⟨witness_supp, witness_fhat_supp, witness_equality,
   not_tfTrans_affine, not_tfTrans_affine_dft⟩

end Tlmc1075
