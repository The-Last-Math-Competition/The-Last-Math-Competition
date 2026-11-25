/-
  Conjecture 00000007622 — General Finite-Dimensional Clifford Algebras
  Inductive graded construction of `Clifford R sig` over any `CommRingOps R`
  for an arbitrary orthogonal quadratic form `sig : List R`, covering:
  - Both sign conventions `ClPlus` (v² = +Q(v)·1) and `ClMinus` (v² = -Q(v)·1),
  - Arbitrary signatures (positive-definite, indefinite, negative-definite, degenerate),
  - Grade involution `gradeInvol`, reversion `rev`, Clifford conjugation `conj`,
  - Multivector and scalar-part norms,
  - Left/right/two-sided zero divisors, units, isotropic vectors,
  - Left ideals, minimal left ideals, faithful simple modules, and module isomorphisms.
-/

import Conjecture00000007622.Basic

namespace Conjecture00000007622

/-- Orthogonal vector space `R^n` indexed by signature list `sig : List R`. -/
inductive Vec (R : Type) : List R → Type where
  | nil : Vec R []
  | cons {c : R} {cs : List R} (head : R) (tail : Vec R cs) : Vec R (c :: cs)

/-- Negated signature list `[-c₀, -c₁, ...]` relating `v² = +Q(v)` and `v² = -Q(v)`. -/
def negSig {R : Type} [CommRingOps R] : List R → List R
  | [] => []
  | c :: cs => (-c) :: negSig cs

/-- Positive-definite Euclidean signature `[1, 1, ..., 1]` of dimension `n`. -/
def posSig (R : Type) [CommRingOps R] : Nat → List R
  | 0 => []
  | n + 1 => (1 : R) :: posSig R n

/-- Zero (totally degenerate / exterior) signature `[0, 0, ..., 0]` of dimension `n`. -/
def zeroSig (R : Type) [CommRingOps R] : Nat → List R
  | 0 => []
  | n + 1 => (0 : R) :: zeroSig R n

namespace Vec
variable {R : Type} [CommRingOps R]

def zeroVec : (sig : List R) → Vec R sig
  | [] => .nil
  | _ :: cs => .cons 0 (zeroVec cs)

/-- Diagonal quadratic form `Q(v) = ∑ cᵢ vᵢ²`. -/
def quadForm : {sig : List R} → Vec R sig → R
  | [], .nil => 0
  | c :: _, .cons x xs => c * (x * x) + quadForm xs

/-- Canonical coordinate identification `Vec R sig → Vec R (negSig sig)`. -/
def toNeg : {sig : List R} → Vec R sig → Vec R (negSig sig)
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (toNeg xs)

theorem toNeg_eq_zero_iff : {sig : List R} → (v : Vec R sig) →
    toNeg v = zeroVec (negSig sig) ↔ v = zeroVec sig
  | [], .nil => ⟨fun _ => rfl, fun _ => rfl⟩
  | _ :: cs, .cons x xs => by
    simp only [toNeg, negSig, zeroVec, Vec.cons.injEq]
    rw [toNeg_eq_zero_iff xs]

theorem quadForm_toNeg : {sig : List R} → (v : Vec R sig) →
    quadForm (toNeg v) = - quadForm v
  | [], .nil => r_neg_zero.symm
  | c :: _, .cons x xs => by
    simp only [toNeg, quadForm, r_neg_mul, r_neg_add]
    rw [quadForm_toNeg xs]

@[simp] theorem quadForm_zero : (sig : List R) → quadForm (zeroVec sig) = 0
  | [] => rfl
  | _ :: cs => by
    simp only [zeroVec, quadForm, r_mul_zero, r_zero_add]
    exact quadForm_zero cs

end Vec

/-- A nonzero vector `v ∈ V \ {0}` with `Q(v) = 0`. -/
def IsIsotropic {R : Type} [CommRingOps R] {sig : List R} (v : Vec R sig) : Prop :=
  v ≠ Vec.zeroVec sig ∧ Vec.quadForm v = 0

/-- Existence of a nonzero isotropic vector in `(V, Q)`. -/
def HasIsotropicVector {R : Type} [CommRingOps R] (sig : List R) : Prop :=
  ∃ v : Vec R sig, IsIsotropic v

theorem posSig_quadForm_nonneg {F : Type} [OrderedField F] :
    (n : Nat) → (v : Vec F (posSig F n)) → NonnegF (Vec.quadForm v)
  | 0, .nil => nonneg_zero
  | n + 1, .cons x xs => by
    simp only [posSig, Vec.quadForm, r_one_mul]
    exact add_nonneg (sq_nonneg x) (posSig_quadForm_nonneg n xs)

theorem posSig_quadForm_eq_zero {F : Type} [OrderedField F] :
    (n : Nat) → (v : Vec F (posSig F n)) →
    Vec.quadForm v = 0 → v = Vec.zeroVec (posSig F n)
  | 0, .nil, _ => rfl
  | n + 1, .cons x xs, h => by
    simp only [posSig, Vec.quadForm, r_one_mul] at h
    have ⟨hx2, hxs⟩ := add_eq_zero_of_nonneg (sq_nonneg x) (posSig_quadForm_nonneg n xs) h
    have hx : x = 0 := f_sq_eq_zero.mp hx2
    have htail : xs = Vec.zeroVec (posSig F n) := posSig_quadForm_eq_zero n xs hxs
    simp only [posSig, Vec.zeroVec, hx, htail]

/-- Over any ordered field (including ℚ and ℝ), the Euclidean quadratic form
    `Q(v) = ∑ vᵢ²` has NO nonzero isotropic vectors in any dimension `n`. -/
theorem posSig_no_isotropic {F : Type} [OrderedField F] (n : Nat) :
    ¬ HasIsotropicVector (posSig F n) := by
  intro ⟨v, hne, hq⟩
  exact hne (posSig_quadForm_eq_zero n v hq)

/-! ### Recursive Graded Clifford Algebra `Clifford R sig` -/

/-- General `2^n`-dimensional Clifford algebra `Cl(R^n, sig)`.
    `step a b` represents `a + e₀ * b` with `a, b ∈ Clifford R cs` and `e₀² = c`. -/
inductive Clifford (R : Type) : List R → Type where
  | base (val : R) : Clifford R []
  | step {c : R} {cs : List R} (evenPart oddPart : Clifford R cs) : Clifford R (c :: cs)

namespace Clifford

theorem step_congr {R : Type} {c : R} {cs : List R} {a a' b b' : Clifford R cs}
    (ha : a = a') (hb : b = b') : step (c := c) a b = step (c := c) a' b' := by
  rw [ha, hb]

section RingOps
variable {R : Type} [CommRingOps R]

def zero : (sig : List R) → Clifford R sig
  | [] => .base 0
  | _ :: cs => .step (zero cs) (zero cs)

def one : (sig : List R) → Clifford R sig
  | [] => .base 1
  | _ :: cs => .step (one cs) (zero cs)

def add : {sig : List R} → Clifford R sig → Clifford R sig → Clifford R sig
  | [], .base a, .base b => .base (a + b)
  | _ :: _, .step a b, .step u v => .step (add a u) (add b v)

def neg : {sig : List R} → Clifford R sig → Clifford R sig
  | [], .base a => .base (-a)
  | _ :: _, .step a b => .step (neg a) (neg b)

def sub {sig : List R} (x y : Clifford R sig) : Clifford R sig :=
  add x (neg y)

def scalar : (sig : List R) → R → Clifford R sig
  | [], r => .base r
  | _ :: cs, r => .step (scalar cs r) (zero cs)

def smul : {sig : List R} → R → Clifford R sig → Clifford R sig
  | [], r, .base a => .base (r * a)
  | _ :: _, r, .step a b => .step (smul r a) (smul r b)

/-- Scalar (grade-0) projection `⟨x⟩₀ ∈ R`. -/
def scalarPart : {sig : List R} → Clifford R sig → R
  | [], .base a => a
  | _ :: _, .step a _ => scalarPart a

/-- Canonical grade involution `α(x)` sending `v ↦ -v` for `v ∈ V`. -/
def gradeInvol : {sig : List R} → Clifford R sig → Clifford R sig
  | [], .base a => .base a
  | _ :: _, .step a b => .step (gradeInvol a) (neg (gradeInvol b))

/-- Clifford product `(a + e₀ b)(u + e₀ v) = (a u + c α(b) v) + e₀ (α(a) v + b u)`. -/
def mul : {sig : List R} → Clifford R sig → Clifford R sig → Clifford R sig
  | [], .base a, .base u => .base (a * u)
  | c :: _, .step a b, .step u v =>
      .step (add (mul a u) (smul c (mul (gradeInvol b) v)))
            (add (mul (gradeInvol a) v) (mul b u))

/-- Reversion anti-automorphism `x̃` sending `v ↦ v` for `v ∈ V`. -/
def rev : {sig : List R} → Clifford R sig → Clifford R sig
  | [], .base a => .base a
  | _ :: _, .step a b => .step (rev a) (gradeInvol (rev b))

/-- Clifford conjugation anti-automorphism `x̄ = α(x̃)` sending `v ↦ -v` for `v ∈ V`. -/
def conj {sig : List R} (x : Clifford R sig) : Clifford R sig :=
  gradeInvol (rev x)

/-- Embedding of `V = Vec R sig` as grade-1 vectors in `Clifford R sig`. -/
def embed : {sig : List R} → Vec R sig → Clifford R sig
  | [], .nil => .base 0
  | _ :: cs, .cons x xs => .step (embed xs) (scalar cs x)

/-- Top-grade volume blade `ω = e₀ e₁ ⋯ e_{n-1}`. -/
def volume : (sig : List R) → Clifford R sig
  | [] => .base 1
  | _ :: cs => .step (zero cs) (volume cs)

instance (sig : List R) : OfNat (Clifford R sig) 0 := ⟨zero sig⟩
instance (sig : List R) : OfNat (Clifford R sig) 1 := ⟨one sig⟩
instance (sig : List R) : Add (Clifford R sig) := ⟨add⟩
instance (sig : List R) : Neg (Clifford R sig) := ⟨neg⟩
instance (sig : List R) : Sub (Clifford R sig) := ⟨sub⟩
instance (sig : List R) : Mul (Clifford R sig) := ⟨mul⟩

@[simp] theorem zero_def (sig : List R) : zero sig = (0 : Clifford R sig) := rfl
@[simp] theorem one_def (sig : List R) : one sig = (1 : Clifford R sig) := rfl
@[simp] theorem neg_def {sig : List R} (x : Clifford R sig) : neg x = -x := rfl
@[simp] theorem add_def {sig : List R} (x y : Clifford R sig) : add x y = x + y := rfl
@[simp] theorem mul_def {sig : List R} (x y : Clifford R sig) : mul x y = x * y := rfl

/-! ### Additive Abelian Group & Module Laws -/

theorem add_assoc : {sig : List R} → (x y z : Clifford R sig) →
    x + y + z = x + (y + z)
  | [], .base a, .base b, .base c => congrArg base (CommRingOps.add_assoc a b c)
  | _ :: _, .step a b, .step u v, .step p q =>
      step_congr (add_assoc a u p) (add_assoc b v q)

theorem add_comm : {sig : List R} → (x y : Clifford R sig) → x + y = y + x
  | [], .base a, .base b => congrArg base (CommRingOps.add_comm a b)
  | _ :: _, .step a b, .step u v => step_congr (add_comm a u) (add_comm b v)

@[simp] theorem zero_add : {sig : List R} → (x : Clifford R sig) → 0 + x = x
  | [], .base a => congrArg base (r_zero_add a)
  | _ :: _, .step a b => step_congr (zero_add a) (zero_add b)

@[simp] theorem add_zero : {sig : List R} → (x : Clifford R sig) → x + 0 = x
  | [], .base a => congrArg base (r_add_zero a)
  | _ :: _, .step a b => step_congr (add_zero a) (add_zero b)

@[simp] theorem neg_add_cancel : {sig : List R} → (x : Clifford R sig) → -x + x = 0
  | [], .base a => congrArg base (r_neg_add_cancel a)
  | _ :: _, .step a b => step_congr (neg_add_cancel a) (neg_add_cancel b)

@[simp] theorem add_neg_cancel {sig : List R} (x : Clifford R sig) : x + -x = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_comm {sig : List R} (x y z : Clifford R sig) :
    x + (y + z) = y + (x + z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem add_left_cancel {sig : List R} {x y z : Clifford R sig} (h : x + y = x + z) : y = z := by
  have h1 : -x + (x + y) = -x + (x + z) := congrArg (-x + ·) h
  rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h1
  exact h1

@[simp] theorem neg_zero : (sig : List R) → -(0 : Clifford R sig) = 0
  | [] => congrArg base r_neg_zero
  | _ :: cs => step_congr (neg_zero cs) (neg_zero cs)

@[simp] theorem neg_neg : {sig : List R} → (x : Clifford R sig) → - -x = x
  | [], .base a => congrArg base (r_neg_neg a)
  | _ :: _, .step a b => step_congr (neg_neg a) (neg_neg b)

theorem neg_add : {sig : List R} → (x y : Clifford R sig) → -(x + y) = -x + -y
  | [], .base a, .base b => congrArg base (r_neg_add a b)
  | _ :: _, .step a b, .step u v => step_congr (neg_add a u) (neg_add b v)

@[simp] theorem sub_self {sig : List R} (x : Clifford R sig) : x - x = 0 :=
  add_neg_cancel x

@[simp] theorem smul_zero : (sig : List R) → (r : R) → smul r (0 : Clifford R sig) = 0
  | [], r => congrArg base (r_mul_zero r)
  | _ :: cs, r => step_congr (smul_zero cs r) (smul_zero cs r)

@[simp] theorem zero_smul : {sig : List R} → (x : Clifford R sig) → smul 0 x = 0
  | [], .base a => congrArg base (r_zero_mul a)
  | _ :: _, .step a b => step_congr (zero_smul a) (zero_smul b)

@[simp] theorem one_smul : {sig : List R} → (x : Clifford R sig) → smul 1 x = x
  | [], .base a => congrArg base (r_one_mul a)
  | _ :: _, .step a b => step_congr (one_smul a) (one_smul b)

theorem smul_add : {sig : List R} → (r : R) → (x y : Clifford R sig) →
    smul r (x + y) = smul r x + smul r y
  | [], r, .base a, .base b => congrArg base (CommRingOps.left_distrib r a b)
  | _ :: _, r, .step a b, .step u v => step_congr (smul_add r a u) (smul_add r b v)

theorem add_smul : {sig : List R} → (r s : R) → (x : Clifford R sig) →
    smul (r + s) x = smul r x + smul s x
  | [], r, s, .base a => congrArg base (CommRingOps.right_distrib r s a)
  | _ :: _, r, s, .step a b => step_congr (add_smul r s a) (add_smul r s b)

theorem smul_smul : {sig : List R} → (r s : R) → (x : Clifford R sig) →
    smul r (smul s x) = smul (r * s) x
  | [], r, s, .base a => congrArg base (CommRingOps.mul_assoc r s a).symm
  | _ :: _, r, s, .step a b => step_congr (smul_smul r s a) (smul_smul r s b)

theorem smul_neg : {sig : List R} → (r : R) → (x : Clifford R sig) →
    smul r (-x) = - smul r x
  | [], r, .base a => congrArg base (r_mul_neg r a)
  | _ :: _, r, .step a b => step_congr (smul_neg r a) (smul_neg r b)

theorem neg_smul : {sig : List R} → (r : R) → (x : Clifford R sig) →
    smul (-r) x = - smul r x
  | [], r, .base a => congrArg base (r_neg_mul r a)
  | _ :: _, r, .step a b => step_congr (neg_smul r a) (neg_smul r b)

@[simp] theorem scalar_zero : (sig : List R) → scalar sig 0 = 0
  | [] => rfl
  | _ :: cs => step_congr (scalar_zero cs) rfl

@[simp] theorem scalar_one (sig : List R) : scalar sig 1 = 1 := by
  induction sig with
  | nil => rfl
  | cons _ cs ih => exact step_congr ih rfl

theorem scalar_add : (sig : List R) → (r s : R) →
    scalar sig (r + s) = scalar sig r + scalar sig s
  | [], _, _ => rfl
  | _ :: cs, r, s => step_congr (scalar_add cs r s) (zero_add (0 : Clifford R cs)).symm

theorem scalar_neg : (sig : List R) → (r : R) →
    scalar sig (-r) = - scalar sig r
  | [], _ => rfl
  | _ :: cs, r => step_congr (scalar_neg cs r) (neg_zero cs).symm

@[simp] theorem scalarPart_scalar : (sig : List R) → (r : R) →
    scalarPart (scalar sig r) = r
  | [], _ => rfl
  | _ :: cs, r => scalarPart_scalar cs r

@[simp] theorem scalarPart_zero : (sig : List R) → scalarPart (0 : Clifford R sig) = 0
  | [] => rfl
  | _ :: cs => scalarPart_zero cs

@[simp] theorem scalarPart_one : (sig : List R) → scalarPart (1 : Clifford R sig) = 1
  | [] => rfl
  | _ :: cs => scalarPart_one cs

theorem scalarPart_add : {sig : List R} → (x y : Clifford R sig) →
    scalarPart (x + y) = scalarPart x + scalarPart y
  | [], .base _, .base _ => rfl
  | _ :: _, .step a _, .step u _ => scalarPart_add a u

theorem scalarPart_smul : {sig : List R} → (r : R) → (x : Clifford R sig) →
    scalarPart (smul r x) = r * scalarPart x
  | [], _, .base _ => rfl
  | _ :: _, r, .step a _ => scalarPart_smul r a

theorem one_ne_zero (sig : List R) : (1 : Clifford R sig) ≠ 0 := by
  intro h
  have hs := congrArg scalarPart h
  rw [scalarPart_one, scalarPart_zero] at hs
  exact r_one_ne_zero hs

theorem scalar_injective {sig : List R} {r s : R} (h : scalar sig r = scalar sig s) : r = s := by
  have hs := congrArg scalarPart h
  rw [scalarPart_scalar, scalarPart_scalar] at hs
  exact hs

/-! ### Grade Involution, Multiplication, Associativity, and Anti-Automorphisms -/

@[simp] theorem gradeInvol_zero : (sig : List R) → gradeInvol (0 : Clifford R sig) = 0
  | [] => rfl
  | _ :: cs => by
      change step (gradeInvol (0 : Clifford R cs)) (-(gradeInvol (0 : Clifford R cs))) =
             step 0 0
      rw [gradeInvol_zero cs, neg_zero]

@[simp] theorem gradeInvol_one : (sig : List R) → gradeInvol (1 : Clifford R sig) = 1
  | [] => rfl
  | _ :: cs => by
      change step (gradeInvol (1 : Clifford R cs)) (-(gradeInvol (0 : Clifford R cs))) =
             step 1 0
      rw [gradeInvol_one cs, gradeInvol_zero cs, neg_zero]

theorem gradeInvol_add : {sig : List R} → (x y : Clifford R sig) →
    gradeInvol (x + y) = gradeInvol x + gradeInvol y
  | [], .base _, .base _ => rfl
  | _ :: _, .step a b, .step u v => by
      change step (gradeInvol (a + u)) (-(gradeInvol (b + v))) =
             step (gradeInvol a + gradeInvol u) (- gradeInvol b + - gradeInvol v)
      rw [gradeInvol_add a u, gradeInvol_add b v, neg_add]

theorem gradeInvol_neg : {sig : List R} → (x : Clifford R sig) →
    gradeInvol (-x) = - gradeInvol x
  | [], .base _ => rfl
  | _ :: _, .step a b => by
      change step (gradeInvol (-a)) (-(gradeInvol (-b))) =
             step (- gradeInvol a) (- (- gradeInvol b))
      rw [gradeInvol_neg a, gradeInvol_neg b]

theorem gradeInvol_smul : {sig : List R} → (r : R) → (x : Clifford R sig) →
    gradeInvol (smul r x) = smul r (gradeInvol x)
  | [], _, .base _ => rfl
  | _ :: _, r, .step a b => by
      change step (gradeInvol (smul r a)) (-(gradeInvol (smul r b))) =
             step (smul r (gradeInvol a)) (smul r (- gradeInvol b))
      rw [gradeInvol_smul r a, gradeInvol_smul r b, smul_neg]

@[simp] theorem gradeInvol_scalar : (sig : List R) → (r : R) →
    gradeInvol (scalar sig r) = scalar sig r
  | [], _ => rfl
  | _ :: cs, r => by
      change step (gradeInvol (scalar cs r)) (-(gradeInvol (0 : Clifford R cs))) =
             step (scalar cs r) 0
      rw [gradeInvol_scalar cs r, gradeInvol_zero cs, neg_zero]

@[simp] theorem gradeInvol_gradeInvol : {sig : List R} → (x : Clifford R sig) →
    gradeInvol (gradeInvol x) = x
  | [], .base _ => rfl
  | _ :: _, .step a b => by
      change step (gradeInvol (gradeInvol a)) (-(gradeInvol (- gradeInvol b))) =
             step a b
      rw [gradeInvol_gradeInvol a, gradeInvol_neg, gradeInvol_gradeInvol b, neg_neg]

@[simp] theorem mul_zero : {sig : List R} → (x : Clifford R sig) → x * 0 = 0
  | [], .base a => congrArg base (r_mul_zero a)
  | c :: _, .step a b => by
      change step (a * 0 + smul c (gradeInvol b * 0)) (gradeInvol a * 0 + b * 0) = step 0 0
      rw [mul_zero a, mul_zero (gradeInvol b), mul_zero (gradeInvol a), mul_zero b,
          smul_zero, add_zero]

@[simp] theorem zero_mul : {sig : List R} → (x : Clifford R sig) → 0 * x = 0
  | [], .base a => congrArg base (r_zero_mul a)
  | c :: cs, .step u v => by
      change step (0 * u + smul c (gradeInvol (0 : Clifford R cs) * v))
                  (gradeInvol (0 : Clifford R cs) * v + 0 * u) = step 0 0
      rw [gradeInvol_zero cs, zero_mul u, zero_mul v, smul_zero, add_zero]

@[simp] theorem one_mul : {sig : List R} → (x : Clifford R sig) → 1 * x = x
  | [], .base a => congrArg base (r_one_mul a)
  | c :: cs, .step u v => by
      change step (1 * u + smul c (gradeInvol (0 : Clifford R cs) * v))
                  (gradeInvol (1 : Clifford R cs) * v + 0 * u) = step u v
      rw [gradeInvol_zero cs, gradeInvol_one cs, one_mul u, one_mul v,
          zero_mul v, zero_mul u, smul_zero, add_zero, add_zero]

@[simp] theorem mul_one : {sig : List R} → (x : Clifford R sig) → x * 1 = x
  | [], .base a => congrArg base (r_mul_one a)
  | c :: _, .step a b => by
      change step (a * 1 + smul c (gradeInvol b * 0))
                  (gradeInvol a * 0 + b * 1) = step a b
      rw [mul_one a, mul_one b, mul_zero, mul_zero, smul_zero, add_zero, zero_add]

theorem left_distrib : {sig : List R} → (x y z : Clifford R sig) →
    x * (y + z) = x * y + x * z
  | [], .base a, .base b, .base c => congrArg base (CommRingOps.left_distrib a b c)
  | c :: _, .step a b, .step u v, .step p q => by
      change step (a * (u + p) + smul c (gradeInvol b * (v + q)))
                  (gradeInvol a * (v + q) + b * (u + p)) =
             step ((a * u + smul c (gradeInvol b * v)) + (a * p + smul c (gradeInvol b * q)))
                  ((gradeInvol a * v + b * u) + (gradeInvol a * q + b * p))
      rw [left_distrib a u p, left_distrib (gradeInvol b) v q,
          left_distrib (gradeInvol a) v q, left_distrib b u p, smul_add]
      apply step_congr
      · rw [add_assoc (a * u), add_assoc (a * u),
            add_left_comm (a * p) (smul c (gradeInvol b * v)) (smul c (gradeInvol b * q))]
      · rw [add_assoc (gradeInvol a * v), add_assoc (gradeInvol a * v),
            add_left_comm (gradeInvol a * q) (b * u) (b * p)]

theorem right_distrib : {sig : List R} → (x y z : Clifford R sig) →
    (x + y) * z = x * z + y * z
  | [], .base a, .base b, .base c => congrArg base (CommRingOps.right_distrib a b c)
  | c :: _, .step a b, .step u v, .step p q => by
      change step ((a + u) * p + smul c (gradeInvol (b + v) * q))
                  (gradeInvol (a + u) * q + (b + v) * p) =
             step ((a * p + smul c (gradeInvol b * q)) + (u * p + smul c (gradeInvol v * q)))
                  ((gradeInvol a * q + b * p) + (gradeInvol u * q + v * p))
      rw [gradeInvol_add, gradeInvol_add, right_distrib a u p, right_distrib (gradeInvol b) _ q,
          right_distrib (gradeInvol a) _ q, right_distrib b v p, smul_add]
      apply step_congr
      · rw [add_assoc (a * p), add_assoc (a * p),
            add_left_comm (u * p) (smul c (gradeInvol b * q)) (smul c (gradeInvol v * q))]
      · rw [add_assoc (gradeInvol a * q), add_assoc (gradeInvol a * q),
            add_left_comm (gradeInvol u * q) (b * p) (v * p)]

theorem smul_mul : {sig : List R} → (r : R) → (x y : Clifford R sig) →
    smul r x * y = smul r (x * y)
  | [], r, .base a, .base b => congrArg base (CommRingOps.mul_assoc r a b)
  | c :: _, r, .step a b, .step u v => by
      change step (smul r a * u + smul c (gradeInvol (smul r b) * v))
                  (gradeInvol (smul r a) * v + smul r b * u) =
             step (smul r (a * u + smul c (gradeInvol b * v)))
                  (smul r (gradeInvol a * v + b * u))
      rw [gradeInvol_smul, gradeInvol_smul, smul_mul r a u, smul_mul r (gradeInvol b) v,
          smul_mul r (gradeInvol a) v, smul_mul r b u, smul_add, smul_add,
          smul_smul, smul_smul, CommRingOps.mul_comm c r]

theorem mul_smul : {sig : List R} → (r : R) → (x y : Clifford R sig) →
    x * smul r y = smul r (x * y)
  | [], r, .base a, .base b => congrArg base (r_mul_left_comm a r b)
  | c :: _, r, .step a b, .step u v => by
      change step (a * smul r u + smul c (gradeInvol b * smul r v))
                  (gradeInvol a * smul r v + b * smul r u) =
             step (smul r (a * u + smul c (gradeInvol b * v)))
                  (smul r (gradeInvol a * v + b * u))
      rw [mul_smul r a u, mul_smul r (gradeInvol b) v, mul_smul r (gradeInvol a) v,
          mul_smul r b u, smul_add, smul_add, smul_smul, smul_smul, CommRingOps.mul_comm c r]

theorem neg_mul : {sig : List R} → (x y : Clifford R sig) → (-x) * y = -(x * y)
  | [], .base a, .base b => congrArg base (r_neg_mul a b)
  | c :: _, .step a b, .step u v => by
      change step ((-a) * u + smul c (gradeInvol (-b) * v))
                  (gradeInvol (-a) * v + (-b) * u) =
             step (-(a * u + smul c (gradeInvol b * v)))
                  (-(gradeInvol a * v + b * u))
      rw [gradeInvol_neg, gradeInvol_neg, neg_mul a u, neg_mul (gradeInvol b) v,
          neg_mul (gradeInvol a) v, neg_mul b u, smul_neg, neg_add, neg_add]

theorem mul_neg : {sig : List R} → (x y : Clifford R sig) → x * (-y) = -(x * y)
  | [], .base a, .base b => congrArg base (r_mul_neg a b)
  | c :: _, .step a b, .step u v => by
      change step (a * (-u) + smul c (gradeInvol b * (-v)))
                  (gradeInvol a * (-v) + b * (-u)) =
             step (-(a * u + smul c (gradeInvol b * v)))
                  (-(gradeInvol a * v + b * u))
      rw [mul_neg a u, mul_neg (gradeInvol b) v, mul_neg (gradeInvol a) v,
          mul_neg b u, smul_neg, neg_add, neg_add]

theorem scalar_mul : {sig : List R} → (r : R) → (x : Clifford R sig) →
    scalar sig r * x = smul r x
  | [], r, .base a => rfl
  | c :: cs, r, .step u v => by
      change step (scalar cs r * u + smul c (gradeInvol (0 : Clifford R cs) * v))
                  (gradeInvol (scalar cs r) * v + 0 * u) =
             step (smul r u) (smul r v)
      rw [gradeInvol_zero cs, gradeInvol_scalar cs r, scalar_mul r u, scalar_mul r v,
          zero_mul, zero_mul, smul_zero, add_zero, add_zero]

theorem mul_scalar : {sig : List R} → (x : Clifford R sig) → (r : R) →
    x * scalar sig r = smul r x
  | [], .base a, r => congrArg base (CommRingOps.mul_comm a r)
  | c :: cs, .step a b, r => by
      change step (a * scalar cs r + smul c (gradeInvol b * (0 : Clifford R cs)))
                  (gradeInvol a * (0 : Clifford R cs) + b * scalar cs r) =
             step (smul r a) (smul r b)
      rw [mul_scalar a r, mul_scalar b r, mul_zero, mul_zero, smul_zero, add_zero, zero_add]

theorem gradeInvol_mul : {sig : List R} → (x y : Clifford R sig) →
    gradeInvol (x * y) = gradeInvol x * gradeInvol y
  | [], .base _, .base _ => rfl
  | c :: _, .step a b, .step u v => by
      change step (gradeInvol (a * u + smul c (gradeInvol b * v)))
                  (-(gradeInvol (gradeInvol a * v + b * u))) =
             step (gradeInvol a * gradeInvol u + smul c (gradeInvol (- gradeInvol b) * (- gradeInvol v)))
                  (gradeInvol (gradeInvol a) * (- gradeInvol v) + (- gradeInvol b) * gradeInvol u)
      rw [gradeInvol_add, gradeInvol_add, gradeInvol_smul,
          gradeInvol_mul a u, gradeInvol_mul (gradeInvol b) v,
          gradeInvol_mul (gradeInvol a) v, gradeInvol_mul b u,
          gradeInvol_neg, gradeInvol_gradeInvol b, gradeInvol_gradeInvol a,
          neg_mul, mul_neg, neg_neg, mul_neg, neg_mul, neg_add]

/-- Associativity of the general `2^n`-dimensional Clifford product. -/
theorem mul_assoc : {sig : List R} → (x y z : Clifford R sig) →
    x * y * z = x * (y * z)
  | [], .base a, .base b, .base c => congrArg base (CommRingOps.mul_assoc a b c)
  | c :: _, .step a b, .step u v, .step p q => by
      change step ((a * u + smul c (gradeInvol b * v)) * p +
                   smul c (gradeInvol (gradeInvol a * v + b * u) * q))
                  (gradeInvol (a * u + smul c (gradeInvol b * v)) * q +
                   (gradeInvol a * v + b * u) * p) =
             step (a * (u * p + smul c (gradeInvol v * q)) +
                   smul c (gradeInvol b * (gradeInvol u * q + v * p)))
                  (gradeInvol a * (gradeInvol u * q + v * p) +
                   b * (u * p + smul c (gradeInvol v * q)))
      rw [right_distrib, right_distrib, left_distrib, left_distrib,
          left_distrib, left_distrib,
          gradeInvol_add, gradeInvol_add, gradeInvol_smul,
          gradeInvol_mul, gradeInvol_mul, gradeInvol_mul, gradeInvol_mul,
          gradeInvol_gradeInvol a, gradeInvol_gradeInvol b,
          right_distrib, right_distrib,
          smul_mul, smul_mul, mul_smul, mul_smul,
          smul_add, smul_add,
          mul_assoc a u p, mul_assoc (gradeInvol b) v p,
          mul_assoc a (gradeInvol v) q, mul_assoc (gradeInvol b) (gradeInvol u) q,
          mul_assoc (gradeInvol a) (gradeInvol u) q, mul_assoc b (gradeInvol v) q,
          mul_assoc (gradeInvol a) v p, mul_assoc b u p]
      apply step_congr
      · rw [add_assoc (a * (u * p)), add_assoc (a * (u * p)),
            add_left_comm (smul c (gradeInvol b * (v * p))) (smul c (a * (gradeInvol v * q))),
            add_comm (smul c (gradeInvol b * (v * p))) (smul c (gradeInvol b * (gradeInvol u * q)))]
      · rw [add_assoc (gradeInvol a * (gradeInvol u * q)),
            add_assoc (gradeInvol a * (gradeInvol u * q)),
            add_left_comm (smul c (b * (gradeInvol v * q))) (gradeInvol a * (v * p)),
            add_comm (smul c (b * (gradeInvol v * q))) (b * (u * p))]

/-! ### Reversion and Clifford Conjugation Anti-Automorphisms -/

@[simp] theorem rev_zero : (sig : List R) → rev (0 : Clifford R sig) = 0
  | [] => rfl
  | _ :: cs => by
      change step (rev (0 : Clifford R cs)) (gradeInvol (rev (0 : Clifford R cs))) = step 0 0
      rw [rev_zero cs, gradeInvol_zero cs]

@[simp] theorem rev_one : (sig : List R) → rev (1 : Clifford R sig) = 1
  | [] => rfl
  | _ :: cs => by
      change step (rev (1 : Clifford R cs)) (gradeInvol (rev (0 : Clifford R cs))) = step 1 0
      rw [rev_one cs, rev_zero cs, gradeInvol_zero cs]

theorem rev_add : {sig : List R} → (x y : Clifford R sig) → rev (x + y) = rev x + rev y
  | [], .base _, .base _ => rfl
  | _ :: _, .step a b, .step u v => by
      change step (rev (a + u)) (gradeInvol (rev (b + v))) =
             step (rev a + rev u) (gradeInvol (rev b) + gradeInvol (rev v))
      rw [rev_add a u, rev_add b v, gradeInvol_add]

theorem rev_neg : {sig : List R} → (x : Clifford R sig) → rev (-x) = - rev x
  | [], .base _ => rfl
  | _ :: _, .step a b => by
      change step (rev (-a)) (gradeInvol (rev (-b))) =
             step (- rev a) (- gradeInvol (rev b))
      rw [rev_neg a, rev_neg b, gradeInvol_neg]

theorem rev_smul : {sig : List R} → (r : R) → (x : Clifford R sig) →
    rev (smul r x) = smul r (rev x)
  | [], _, .base _ => rfl
  | _ :: _, r, .step a b => by
      change step (rev (smul r a)) (gradeInvol (rev (smul r b))) =
             step (smul r (rev a)) (smul r (gradeInvol (rev b)))
      rw [rev_smul r a, rev_smul r b, gradeInvol_smul]

@[simp] theorem rev_scalar : (sig : List R) → (r : R) → rev (scalar sig r) = scalar sig r
  | [], _ => rfl
  | _ :: cs, r => by
      change step (rev (scalar cs r)) (gradeInvol (rev (0 : Clifford R cs))) =
             step (scalar cs r) 0
      rw [rev_scalar cs r, rev_zero cs, gradeInvol_zero cs]

theorem rev_gradeInvol : {sig : List R} → (x : Clifford R sig) →
    rev (gradeInvol x) = gradeInvol (rev x)
  | [], .base _ => rfl
  | _ :: _, .step a b => by
      change step (rev (gradeInvol a)) (gradeInvol (rev (- gradeInvol b))) =
             step (gradeInvol (rev a)) (- gradeInvol (gradeInvol (rev b)))
      rw [rev_gradeInvol a, rev_neg, rev_gradeInvol b, gradeInvol_neg]

@[simp] theorem rev_rev : {sig : List R} → (x : Clifford R sig) → rev (rev x) = x
  | [], .base _ => rfl
  | _ :: _, .step a b => by
      change step (rev (rev a)) (gradeInvol (rev (gradeInvol (rev b)))) = step a b
      rw [rev_rev a, rev_gradeInvol, rev_rev b, gradeInvol_gradeInvol]

/-- Reversion is an algebra anti-automorphism: `rev (x * y) = rev y * rev x`. -/
theorem rev_mul : {sig : List R} → (x y : Clifford R sig) →
    rev (x * y) = rev y * rev x
  | [], .base a, .base b => congrArg base (CommRingOps.mul_comm a b)
  | c :: _, .step a b, .step u v => by
      change step (rev (a * u + smul c (gradeInvol b * v)))
                  (gradeInvol (rev (gradeInvol a * v + b * u))) =
             step (rev u * rev a + smul c (gradeInvol (gradeInvol (rev v)) * gradeInvol (rev b)))
                  (gradeInvol (rev u) * gradeInvol (rev b) + gradeInvol (rev v) * rev a)
      rw [rev_add, rev_add, rev_smul,
          rev_mul a u, rev_mul (gradeInvol b) v,
          rev_mul (gradeInvol a) v, rev_mul b u,
          rev_gradeInvol, rev_gradeInvol,
          gradeInvol_add, gradeInvol_mul, gradeInvol_mul,
          gradeInvol_gradeInvol (rev v), gradeInvol_gradeInvol (rev a),
          add_comm (gradeInvol (rev v) * rev a)]

@[simp] theorem conj_zero (sig : List R) : conj (0 : Clifford R sig) = 0 := by
  unfold conj; rw [rev_zero, gradeInvol_zero]

@[simp] theorem conj_one (sig : List R) : conj (1 : Clifford R sig) = 1 := by
  unfold conj; rw [rev_one, gradeInvol_one]

theorem conj_add {sig : List R} (x y : Clifford R sig) :
    conj (x + y) = conj x + conj y := by
  unfold conj; rw [rev_add, gradeInvol_add]

theorem conj_neg {sig : List R} (x : Clifford R sig) :
    conj (-x) = - conj x := by
  unfold conj; rw [rev_neg, gradeInvol_neg]

theorem conj_smul {sig : List R} (r : R) (x : Clifford R sig) :
    conj (smul r x) = smul r (conj x) := by
  unfold conj; rw [rev_smul, gradeInvol_smul]

@[simp] theorem conj_scalar (sig : List R) (r : R) :
    conj (scalar sig r) = scalar sig r := by
  unfold conj; rw [rev_scalar, gradeInvol_scalar]

@[simp] theorem conj_conj {sig : List R} (x : Clifford R sig) :
    conj (conj x) = x := by
  unfold conj; rw [rev_gradeInvol, gradeInvol_gradeInvol, rev_rev]

/-- Clifford conjugation is an algebra anti-automorphism: `conj (x * y) = conj y * conj x`. -/
theorem conj_mul {sig : List R} (x y : Clifford R sig) :
    conj (x * y) = conj y * conj x := by
  unfold conj; rw [rev_mul, gradeInvol_mul]

/-! ### Universal Clifford Defining Relations (`v² = +Q(v)·1` and `v² = -Q(v)·1`) -/

@[simp] theorem embed_zero : (sig : List R) → embed (Vec.zeroVec sig) = 0
  | [] => rfl
  | _ :: cs => step_congr (embed_zero cs) (scalar_zero cs)

theorem embed_injective : {sig : List R} → {u v : Vec R sig} →
    embed u = embed v → u = v
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x xs, .cons y ys, h => by
      injection h with _ _ hxs hsc
      rw [embed_injective hxs, scalar_injective hsc]

theorem gradeInvol_embed : {sig : List R} → (v : Vec R sig) →
    gradeInvol (embed v) = - embed v
  | [], .nil => congrArg base r_neg_zero.symm
  | _ :: cs, .cons x xs => by
      change step (gradeInvol (embed xs)) (-(gradeInvol (scalar cs x))) =
             step (- embed xs) (- scalar cs x)
      rw [gradeInvol_embed xs, gradeInvol_scalar cs x]

theorem rev_embed : {sig : List R} → (v : Vec R sig) → rev (embed v) = embed v
  | [], .nil => rfl
  | _ :: cs, .cons x xs => by
      change step (rev (embed xs)) (gradeInvol (rev (scalar cs x))) =
             step (embed xs) (scalar cs x)
      rw [rev_embed xs, rev_scalar cs x, gradeInvol_scalar cs x]

theorem conj_embed {sig : List R} (v : Vec R sig) : conj (embed v) = - embed v := by
  unfold conj; rw [rev_embed, gradeInvol_embed]

theorem smul_scalar : (sig : List R) → (r s : R) →
    smul r (scalar sig s) = scalar sig (r * s)
  | [], _, _ => rfl
  | _ :: cs, r, s => step_congr (smul_scalar cs r s) (smul_zero cs r)

/-- Defining Clifford relation under the `+Q` convention (`v² = +Q(v)·1`). -/
theorem embed_sq : {sig : List R} → (v : Vec R sig) →
    embed v * embed v = scalar sig (Vec.quadForm v)
  | [], .nil => congrArg base (r_mul_zero 0)
  | c :: cs, .cons x xs => by
      change step (embed xs * embed xs + smul c (gradeInvol (scalar cs x) * scalar cs x))
                  (gradeInvol (embed xs) * scalar cs x + scalar cs x * embed xs) =
             scalar (c :: cs) (c * (x * x) + Vec.quadForm xs)
      rw [embed_sq xs, gradeInvol_scalar cs x, gradeInvol_embed xs,
          mul_scalar (- embed xs) x, scalar_mul x (embed xs), smul_neg, neg_add_cancel,
          scalar_mul, smul_smul, smul_scalar, CommRingOps.mul_assoc c x x, add_comm,
          ← scalar_add cs]
      rfl

/-- Embedding of `v ∈ Vec R sig` into `ClMinus R sig := Clifford R (negSig sig)`. -/
def embedMinus {sig : List R} (v : Vec R sig) : Clifford R (negSig sig) :=
  embed (Vec.toNeg v)

/-- Defining Clifford relation under the `-Q` convention (`v² = -Q(v)·1`). -/
theorem embedMinus_sq {sig : List R} (v : Vec R sig) :
    embedMinus v * embedMinus v = - scalar (negSig sig) (Vec.quadForm v) := by
  unfold embedMinus
  rw [embed_sq, Vec.quadForm_toNeg, scalar_neg]

/-! ### Norms, Zero Divisors, Units, and Left Ideals -/

def cliffordNormElem {sig : List R} (x : Clifford R sig) : Clifford R sig := x * conj x
def reversionNormElem {sig : List R} (x : Clifford R sig) : Clifford R sig := x * rev x
def gradeNormElem {sig : List R} (x : Clifford R sig) : Clifford R sig := x * gradeInvol x

def cliffordScalarNorm {sig : List R} (x : Clifford R sig) : R := scalarPart (x * conj x)
def reversionScalarNorm {sig : List R} (x : Clifford R sig) : R := scalarPart (x * rev x)

def IsLeftZeroDivisor {sig : List R} (x : Clifford R sig) : Prop :=
  x ≠ 0 ∧ ∃ y : Clifford R sig, y ≠ 0 ∧ x * y = 0

def IsRightZeroDivisor {sig : List R} (x : Clifford R sig) : Prop :=
  x ≠ 0 ∧ ∃ y : Clifford R sig, y ≠ 0 ∧ y * x = 0

def IsZeroDivisor {sig : List R} (x : Clifford R sig) : Prop :=
  x ≠ 0 ∧ ∃ y : Clifford R sig, y ≠ 0 ∧ (x * y = 0 ∨ y * x = 0)

def IsUnitElem {sig : List R} (x : Clifford R sig) : Prop :=
  ∃ y : Clifford R sig, x * y = 1 ∧ y * x = 1

theorem leftZD_to_ZD {sig : List R} {x : Clifford R sig} (h : IsLeftZeroDivisor x) :
    IsZeroDivisor x :=
  ⟨h.1, let ⟨y, hy, hxy⟩ := h.2; ⟨y, hy, Or.inl hxy⟩⟩

theorem rightZD_to_ZD {sig : List R} {x : Clifford R sig} (h : IsRightZeroDivisor x) :
    IsZeroDivisor x :=
  ⟨h.1, let ⟨y, hy, hyx⟩ := h.2; ⟨y, hy, Or.inr hyx⟩⟩

theorem unit_not_zeroDivisor {sig : List R} {x : Clifford R sig} (hu : IsUnitElem x) :
    ¬ IsZeroDivisor x := by
  rcases hu with ⟨invx, hxi, hix⟩
  intro ⟨_, y, hy, hmul⟩
  cases hmul with
  | inl hxy =>
    apply hy
    calc
      y = 1 * y := (one_mul y).symm
      _ = (invx * x) * y := by rw [hix]
      _ = invx * (x * y) := mul_assoc invx x y
      _ = invx * 0 := by rw [hxy]
      _ = 0 := mul_zero invx
  | inr hyx =>
    apply hy
    calc
      y = y * 1 := (mul_one y).symm
      _ = y * (x * invx) := by rw [hxi]
      _ = (y * x) * invx := (mul_assoc y x invx).symm
      _ = 0 * invx := by rw [hyx]
      _ = 0 := zero_mul invx

theorem unit_not_leftZeroDivisor {sig : List R} {x : Clifford R sig} (hu : IsUnitElem x) :
    ¬ IsLeftZeroDivisor x :=
  fun h => unit_not_zeroDivisor hu (leftZD_to_ZD h)

theorem one_isUnit (sig : List R) : IsUnitElem (1 : Clifford R sig) :=
  ⟨1, mul_one 1, mul_one 1⟩

theorem conj_ne_zero {sig : List R} {x : Clifford R sig} (hx : x ≠ 0) : conj x ≠ 0 := by
  intro hc
  apply hx
  rw [← conj_conj x, hc, conj_zero]

/-- Left ideal of `Clifford R sig`. -/
structure LeftIdeal (sig : List R) where
  carrier : Clifford R sig → Prop
  zero_mem : carrier 0
  add_mem : ∀ {x y}, carrier x → carrier y → carrier (x + y)
  mul_left_mem : ∀ (a : Clifford R sig) {x}, carrier x → carrier (a * x)

/-- Principal left ideal `Cl · g` generated by `g`. -/
def principalLeftIdeal {sig : List R} (g : Clifford R sig) : LeftIdeal sig where
  carrier x := ∃ a : Clifford R sig, x = a * g
  zero_mem := ⟨0, (zero_mul g).symm⟩
  add_mem := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [ha, hb, right_distrib]⟩
  mul_left_mem := fun c {_} ⟨a, ha⟩ => ⟨c * a, by rw [ha, mul_assoc]⟩

def LeftIdeal.IsNonzero {sig : List R} (I : LeftIdeal sig) : Prop :=
  ∃ x : Clifford R sig, x ≠ 0 ∧ I.carrier x

def LeftIdeal.IsMinimal {sig : List R} (I : LeftIdeal sig) : Prop :=
  I.IsNonzero ∧
  ∀ J : LeftIdeal sig, J.IsNonzero →
    (∀ x, J.carrier x → I.carrier x) →
    (∀ x, I.carrier x → J.carrier x)

def LeftIdeal.ConsistsOfZeroDivisors {sig : List R} (I : LeftIdeal sig) : Prop :=
  ∀ x : Clifford R sig, I.carrier x → x ≠ 0 → IsLeftZeroDivisor x

def LeftIdeal.IsFaithful {sig : List R} (I : LeftIdeal sig) : Prop :=
  ∀ a : Clifford R sig, (∀ x : Clifford R sig, I.carrier x → a * x = 0) → a = 0

/-- Left `Clifford R sig`-module isomorphism between two left ideals `I` and `J`. -/
structure LeftModuleIso {sig : List R} (I J : LeftIdeal sig) where
  toFun : Clifford R sig → Clifford R sig
  invFun : Clifford R sig → Clifford R sig
  map_mem : ∀ {x}, I.carrier x → J.carrier (toFun x)
  inv_mem : ∀ {y}, J.carrier y → I.carrier (invFun y)
  left_inv : ∀ {x}, I.carrier x → invFun (toFun x) = x
  right_inv : ∀ {y}, J.carrier y → toFun (invFun y) = y
  map_add : ∀ {x y}, I.carrier x → I.carrier y → toFun (x + y) = toFun x + toFun y
  map_mul_left : ∀ (a : Clifford R sig) {x}, I.carrier x → toFun (a * x) = a * toFun x

end RingOps
end Clifford

end Conjecture00000007622
