import Std
namespace TLMC523
/-- F₂ is represented by Bool; addition is xor and multiplication is and. -/
abbrev F2 := Bool
/-- A Laurent polynomial is a finitely supported coefficient function on Z. -/
structure Laurent where
  coeff : Int → F2
  bounded : ∃ N : Nat, ∀ k : Int, (N : Int) < k ∨ k < -(N : Int) → coeff k = false
@[ext] theorem Laurent.ext {a b : Laurent} (h : ∀ k, a.coeff k = b.coeff k) : a = b := by
  cases a; cases b; simp_all; exact funext h

def zero : Laurent := ⟨fun _ => false, ⟨0, by simp⟩⟩
def add (a b : Laurent) : Laurent := ⟨fun k => a.coeff k ^^ b.coeff k, by
  obtain ⟨N,hN⟩ := a.bounded
  obtain ⟨M,hM⟩ := b.bounded
  refine ⟨N+M, ?_⟩
  intro k hk
  have ha := hN k (by omega)
  have hb := hM k (by omega)
  simp [ha,hb]⟩
def scale (c : F2) (a : Laurent) : Laurent := ⟨fun k => c && a.coeff k, by
  obtain ⟨N,hN⟩ := a.bounded
  exact ⟨N, fun k hk => by simp [hN k hk]⟩⟩
def monomial (j : Int) : Laurent := ⟨fun k => decide (k=j), by
  refine ⟨j.natAbs, ?_⟩
  intro k hk
  have hj : -(j.natAbs : Int) ≤ j ∧ j ≤ (j.natAbs : Int) := by omega
  apply decide_eq_false
  omega⟩
/-- Multiplication by t^j on Laurent coefficients. -/
def shift (j : Int) (a : Laurent) : Laurent := ⟨fun k => a.coeff (k-j), by
  obtain ⟨N,hN⟩ := a.bounded
  refine ⟨N+j.natAbs, ?_⟩
  intro k hk
  apply hN
  have hj : -(j.natAbs : Int) ≤ j ∧ j ≤ (j.natAbs : Int) := by omega
  omega⟩

/-- The polynomial subspace F₂[t] consists exactly of Laurent polynomials
with no negative coefficients. -/
def Polynomial (a : Laurent) : Prop := ∀ k : Int, k < 0 → a.coeff k = false

/-- Every Laurent polynomial is a polynomial divided by a power of t.
This verifies the concrete denominator-clearing identification with R[1/t]. -/
theorem clear_denominators (a : Laurent) :
    ∃ N : Nat, Polynomial (shift (N:Int) a) ∧ shift (-(N:Int)) (shift (N:Int) a) = a := by
  obtain ⟨N,hN⟩ := a.bounded
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    change a.coeff (k-(N:Int)) = false
    apply hN; omega
  · apply Laurent.ext
    intro k
    change a.coeff ((k-(-(N:Int)))-(N:Int)) = a.coeff k
    congr 1; omega

/-- Boolean arithmetic really satisfies the field identities of F₂. -/
theorem binary_field_identities :
    false ≠ true ∧
    (∀ a : F2, (a ^^ false) = a ∧ (a ^^ a) = false ∧ (a && true) = a) ∧
    (∀ a b : F2, (a ^^ b) = (b ^^ a) ∧ (a && b) = (b && a)) ∧
    (∀ a b c : F2, ((a ^^ b) ^^ c) = (a ^^ (b ^^ c)) ∧
       ((a && b) && c) = (a && (b && c)) ∧
       (a && (b ^^ c)) = ((a && b) ^^ (a && c))) ∧
    (∀ a : F2, a ≠ false → ∃ b : F2, (a && b) = true) := by decide

def cechSetoid : Setoid Laurent where
  r a b := ∀ k : Int, k < 0 → a.coeff k = b.coeff k
  iseqv := ⟨fun _ _ _ => rfl, fun h _ hk => (h _ hk).symm,
    fun h g k hk => (h k hk).trans (g k hk)⟩
/-- Degree-one cohomology of the principal Čech complex R → R[1/t]. -/
abbrev H1 := Quotient cechSetoid

def classOf (a : Laurent) : H1 := Quotient.mk cechSetoid a

theorem relation_iff_difference_polynomial (a b : Laurent) :
    cechSetoid.r a b ↔ Polynomial (add a b) := by
  constructor
  · intro h k hk; simp [add,h k hk]
  · intro h k hk
    have hh := h k hk
    change (a.coeff k ^^ b.coeff k) = false at hh
    cases ha : a.coeff k <;> cases hb : b.coeff k <;> simp_all

def hzero : H1 := classOf zero

def negativeCoeff (k : Int) (hk : k < 0) : H1 → F2 :=
  Quotient.lift (fun a => a.coeff k) (fun _ _ h => h k hk)

def hadd : H1 → H1 → H1 := Quotient.lift₂ (fun a b => classOf (add a b)) (by
  intro a b c d hac hbd
  apply Quotient.sound
  intro k hk
  simp only [add]
  rw [hac k hk,hbd k hk])
def hscale (c : F2) : H1 → H1 := Quotient.lift (fun a => classOf (scale c a)) (by
  intro a b h
  apply Quotient.sound
  intro k hk
  simp [scale,h k hk])

/-- In characteristic two the square of Σ a_i t^i is Σ a_i t^(2i).
This coefficient formula defines Frobenius on F₂[t,t⁻¹]. -/
def frobenius (a : Laurent) : Laurent := ⟨fun k => if k % 2 = 0 then a.coeff (k / 2) else false, by
  obtain ⟨N,hN⟩ := a.bounded
  refine ⟨2*N+1, ?_⟩
  intro k hk
  split
  · apply hN; omega
  · rfl⟩

theorem frobenius_polynomial (a : Laurent) (ha : Polynomial a) : Polynomial (frobenius a) := by
  intro k hk
  simp only [frobenius]
  split
  · apply ha; omega
  · rfl

def F : H1 → H1 := Quotient.lift (fun a => classOf (frobenius a)) (by
  intro a b h
  apply Quotient.sound
  intro k hk
  simp only [frobenius]
  split
  · apply h; omega
  · rfl)

theorem frobenius_add (a b : Laurent) : frobenius (add a b) = add (frobenius a) (frobenius b) := by
  apply Laurent.ext
  intro k
  simp only [frobenius,add]
  split <;> simp_all

theorem frobenius_scale (c : F2) (a : Laurent) : frobenius (scale c a) = scale c (frobenius a) := by
  apply Laurent.ext
  intro k
  simp only [frobenius,scale]
  split <;> simp_all

theorem F_add (a b : H1) : F (hadd a b) = hadd (F a) (F b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change classOf (frobenius (add x y)) = classOf (add (frobenius x) (frobenius y))
  rw [frobenius_add]

theorem F_scale (c : F2) (a : H1) : F (hscale c a) = hscale c (F a) := by
  refine Quotient.inductionOn a ?_
  intro x
  change classOf (frobenius (scale c x)) = classOf (scale c (frobenius x))
  rw [frobenius_scale]

def e1 : H1 := classOf (monomial (-1))
def e2 : H1 := classOf (monomial (-2))

theorem F_e1 : F e1 = e2 := by
  apply Quotient.sound
  intro k hk
  simp only [frobenius,monomial]
  split <;> rename_i h
  · have he : (k / 2 = -1) ↔ (k = -2) := by omega
    simp only [he]
  · symm
    apply decide_eq_false
    omega

theorem e1_nonzero : e1 ≠ hzero := by
  intro h
  have hh := congrArg (negativeCoeff (-1) (by decide)) h
  change true = false at hh
  contradiction

theorem e2_nonzero : e2 ≠ hzero := by
  intro h
  have hh := congrArg (negativeCoeff (-2) (by decide)) h
  change true = false at hh
  contradiction

theorem e2_ne_e1 : e2 ≠ e1 := by
  intro h
  have hh := congrArg (negativeCoeff (-2) (by decide)) h
  change true = false at hh
  contradiction

/-- Apply every possible monic degree-one polynomial X+c over F₂. -/
def degreeOneEval (c : F2) (v : H1) : H1 := hadd (F v) (hscale c v)

theorem no_degree_one_annihilator (c : F2) : ¬ ∀ v : H1, degreeOneEval c v = hzero := by
  intro h
  have hh := congrArg (negativeCoeff (-2) (by decide)) (h e1)
  change (true ^^ (c && false)) = false at hh
  simp at hh

/-- The numerical semigroup generated by 1, including 0. -/
def semigroupN (_ : Nat) : Prop := True

def NumericalSemigroup (S : Nat → Prop) : Prop :=
  S 0 ∧ (∀ a b, S a → S b → S (a+b)) ∧ ∃ bound, ∀ n, bound ≤ n → S n

def Multiplicity (S : Nat → Prop) (m : Nat) : Prop :=
  0 < m ∧ S m ∧ ∀ n, 0 < n → S n → m ≤ n

theorem N_numerical : NumericalSemigroup semigroupN := by
  exact ⟨True.intro, fun _ _ _ _ => True.intro, ⟨0, fun _ _ => True.intro⟩⟩
theorem N_multiplicity_one : Multiplicity semigroupN 1 := by
  exact ⟨by decide, True.intro, fun n hn _ => hn⟩

/-- No monic linear annihilator exists, hence no minimal polynomial of
 degree one, although this numerical semigroup has multiplicity one. -/
theorem counterexample : NumericalSemigroup semigroupN ∧ Multiplicity semigroupN 1 ∧
    ¬ ∃ c : F2, ∀ v : H1, degreeOneEval c v = hzero := by
  exact ⟨N_numerical,N_multiplicity_one,fun ⟨c,h⟩ => no_degree_one_annihilator c h⟩

def powCoeff (n : Nat) : H1 → F2 := negativeCoeff (-((2:Int)^n)) (by
  have h : (0:Int) < 2^n := Int.pow_pos (by decide)
  omega)

theorem powCoeff_zero (n : Nat) : powCoeff n hzero = false := rfl

theorem powCoeff_add (n : Nat) (u v : H1) :
    powCoeff n (hadd u v) = (powCoeff n u ^^ powCoeff n v) := by
  refine Quotient.inductionOn₂ u v ?_
  intro a b; rfl

theorem powCoeff_scale (n : Nat) (c : F2) (v : H1) :
    powCoeff n (hscale c v) = (c && powCoeff n v) := by
  refine Quotient.inductionOn v ?_
  intro a; rfl

theorem powCoeff_F_zero (v : H1) : powCoeff 0 (F v) = false := by
  refine Quotient.inductionOn v ?_
  intro a; rfl

theorem powCoeff_F_succ (n : Nat) (v : H1) : powCoeff (n+1) (F v) = powCoeff n v := by
  refine Quotient.inductionOn v ?_
  intro a
  change (if (-(2:Int)^(n+1)) % 2 = 0 then a.coeff ((-(2:Int)^(n+1))/2) else false) = _
  rw [Int.pow_succ]
  have hm : (-((2:Int)^n * 2)) % 2 = 0 := by omega
  have hd : (-((2:Int)^n * 2)) / 2 = -((2:Int)^n) := by omega
  simp only [hm,ite_true,hd]
  rfl

theorem powCoeff_e1_zero : powCoeff 0 e1 = true := rfl

theorem powCoeff_e1_succ (n : Nat) : powCoeff (n+1) e1 = false := by
  change decide (-((2:Int)^(n+1)) = -1) = false
  apply decide_eq_false
  rw [Int.pow_succ]
  have hp : (0:Int) < 2^n := Int.pow_pos (by decide)
  omega

/-- Coefficients are stored in increasing order, trailing zeroes permitted.
Horner evaluation is genuine evaluation at the F₂-linear map F. -/
def polyEval : List F2 → H1 → H1
  | [], _ => hzero
  | c::cs, v => hadd (hscale c v) (F (polyEval cs v))

theorem polyEval_coefficient (cs : List F2) (n : Nat) :
    powCoeff n (polyEval cs e1) = cs[n]?.getD false := by
  induction cs generalizing n with
  | nil => simp [polyEval,powCoeff_zero]
  | cons c cs ih =>
    cases n with
    | zero => simp [polyEval,powCoeff_add,powCoeff_scale,powCoeff_e1_zero,powCoeff_F_zero]
    | succ n =>
      simp [polyEval,powCoeff_add,powCoeff_scale,powCoeff_e1_succ,powCoeff_F_succ,ih]

/-- Every nonzero coefficient polynomial fails already on [t⁻¹]. -/
theorem no_nonzero_annihilator (cs : List F2) (h : ∃ n : Nat, cs[n]?.getD false = true) :
    ¬ ∀ v : H1, polyEval cs v = hzero := by
  intro hh
  obtain ⟨n,hn⟩ := h
  have hc := congrArg (powCoeff n) (hh e1)
  rw [polyEval_coefficient,powCoeff_zero,hn] at hc
  contradiction
end TLMC523
