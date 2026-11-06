import Std
namespace TLMC506
namespace Raw
abbrev Monomial := Nat × Nat
abbrev Poly := List Monomial

def coeff : Poly → Nat → Nat → Bool
  | [], _, _ => false
  | (a,b)::l, i, j => ((a == i) && (b == j)) ^^ coeff l i j

def shift (a b : Nat) (l : Poly) : Poly := l.map fun m => (a + m.1, b + m.2)

def mul : Poly → Poly → Poly
  | [], _ => []
  | (a,b)::l, q => shift a b q ++ mul l q

@[simp] theorem coeff_nil (i j : Nat) : coeff [] i j = false := rfl
@[simp] theorem coeff_cons (a b i j : Nat) (l : Poly) :
    coeff ((a,b)::l) i j = (((a == i) && (b == j)) ^^ coeff l i j) := rfl
@[simp] theorem coeff_append (l k : Poly) (i j : Nat) :
    coeff (l ++ k) i j = (coeff l i j ^^ coeff k i j) := by
  induction l with
  | nil => simp [coeff]
  | cons m l ih => cases m; simp [coeff, ih]

@[simp] theorem shift_nil (a b : Nat) : shift a b [] = [] := rfl
@[simp] theorem shift_cons (a b c d : Nat) (l : Poly) :
    shift a b ((c,d)::l) = (a+c,b+d)::shift a b l := rfl
@[simp] theorem shift_append (a b : Nat) (l k : Poly) :
    shift a b (l ++ k) = shift a b l ++ shift a b k := by simp [shift]
@[simp] theorem shift_shift (a b c d : Nat) (l : Poly) :
    shift a b (shift c d l) = shift (a+c) (b+d) l := by
  simp [shift, List.map_map, Function.comp_def, Nat.add_assoc]
@[simp] theorem shift_zero (l : Poly) : shift 0 0 l = l := by simp [shift]

theorem coeff_shift (a b i j : Nat) (l : Poly) :
    coeff (shift a b l) i j =
      if a ≤ i ∧ b ≤ j then coeff l (i-a) (j-b) else false := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rcases m with ⟨c,d⟩
    rw [shift_cons, coeff_cons, ih]
    by_cases h : a ≤ i ∧ b ≤ j
    · rw [if_pos h, if_pos h, coeff_cons]
      have hx : (a+c == i) = (c == i-a) := by apply Bool.eq_iff_iff.mpr; simp; omega
      have hy : (b+d == j) = (d == j-b) := by apply Bool.eq_iff_iff.mpr; simp; omega
      rw [hx,hy]
    · rw [if_neg h, if_neg h]
      have he : ((a+c == i) && (b+d == j)) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        omega
      simp [he]

def Equiv (p q : Poly) : Prop := ∀ i j, coeff p i j = coeff q i j

theorem equiv_refl (p : Poly) : Equiv p p := by intro i j; rfl

theorem equiv_append {p q r s : Poly} (h : Equiv p q) (k : Equiv r s) :
    Equiv (p ++ r) (q ++ s) := by intro i j; simp [h i j, k i j]

theorem equiv_shift {p q : Poly} (h : Equiv p q) (a b : Nat) :
    Equiv (shift a b p) (shift a b q) := by intro i j; simp only [coeff_shift]; rw [h]

@[simp] theorem mul_nil (p : Poly) : mul p [] = [] := by
  induction p with
  | nil => rfl
  | cons m p ih => cases m; simp [mul, ih]
@[simp] theorem mul_append_left (p q r : Poly) : mul (p ++ q) r = mul p r ++ mul q r := by
  induction p with
  | nil => rfl
  | cons m p ih => cases m; simp [mul, ih, List.append_assoc]

theorem mul_congr_right (p : Poly) {q r : Poly} (h : Equiv q r) :
    Equiv (mul p q) (mul p r) := by
  induction p with
  | nil => exact equiv_refl []
  | cons m p ih => cases m; exact equiv_append (equiv_shift h _ _) ih

theorem coeff_mul_append_right (p q r : Poly) (i j : Nat) :
    coeff (mul p (q ++ r)) i j = (coeff (mul p q) i j ^^ coeff (mul p r) i j) := by
  induction p with
  | nil => simp [mul]
  | cons m p ih =>
    rcases m with ⟨a,b⟩
    simp only [mul, shift_append, coeff_append, ih]
    generalize coeff (shift a b q) i j = A
    generalize coeff (shift a b r) i j = B
    generalize coeff (mul p q) i j = C
    generalize coeff (mul p r) i j = D
    cases A <;> cases B <;> cases C <;> cases D <;> rfl

@[simp] theorem mul_singleton_right (p : Poly) (a b : Nat) :
    mul p [(a,b)] = shift a b p := by
  induction p with
  | nil => rfl
  | cons m p ih => cases m; simp [mul, shift, ih, Nat.add_comm]

@[simp] theorem mul_singleton_left (p : Poly) (a b : Nat) :
    mul [(a,b)] p = shift a b p := by simp [mul]

theorem mul_comm (p q : Poly) : Equiv (mul p q) (mul q p) := by
  induction p with
  | nil => simp [mul, Equiv]
  | cons m p ih =>
    rcases m with ⟨a,b⟩
    intro i j
    rw [show (a,b)::p = [(a,b)] ++ p from rfl]
    simp only [mul_append_left, coeff_append, coeff_mul_append_right,
      mul_singleton_left, mul_singleton_right, ih i j]

theorem mul_congr_left {p q : Poly} (h : Equiv p q) (r : Poly) :
    Equiv (mul p r) (mul q r) := by
  intro i j
  rw [mul_comm p r i j, mul_comm q r i j]
  exact mul_congr_right r h i j

theorem shift_mul_left (a b : Nat) (p q : Poly) :
    mul (shift a b p) q = shift a b (mul p q) := by
  induction p with
  | nil => rfl
  | cons m p ih => cases m; simp [mul, ih]

theorem mul_assoc (p q r : Poly) : mul (mul p q) r = mul p (mul q r) := by
  induction p with
  | nil => rfl
  | cons m p ih => cases m; simp [mul, shift_mul_left, ih]


-- A finite coefficient rectangle enumerates a genuine finite monomial list.
def row (f : Nat → Bool) (a : Nat) : Nat → Poly
  | 0 => []
  | n+1 => (if f n then [(a,n)] else []) ++ row f a n

def box (f : Nat → Nat → Bool) (m : Nat) : Nat → Poly
  | 0 => []
  | n+1 => row (f n) n m ++ box f m n

theorem coeff_row (f : Nat → Bool) (a n i j : Nat) :
    coeff (row f a n) i j = if i=a ∧ j<n then f j else false := by
  induction n with
  | zero => simp [row]
  | succ n ih =>
    rw [row, coeff_append, ih]
    have hs : coeff (if f n then [(a,n)] else []) i j =
        if i=a ∧ j=n then f n else false := by
      cases hf : f n
      · simp
      · by_cases hi : i=a
        · subst i
          by_cases hj : j=n
          · subst j; simp [coeff]
          · have hn : n ≠ j := Ne.symm hj
            simp [coeff, hj, hn]
        · have ha : a ≠ i := Ne.symm hi
          simp [coeff, hi, ha]
    rw [hs]
    by_cases hi : i=a
    · subst i
      by_cases hj : j=n
      · subst j; simp
      · by_cases hl : j<n
        · have hl' : j<n+1 := by omega
          simp [hj, hl, hl']
        · have hl' : ¬j<n+1 := by omega
          simp [hj, hl, hl']
    · simp [hi]

theorem coeff_box (f : Nat → Nat → Bool) (n m i j : Nat) :
    coeff (box f m n) i j = if i<n ∧ j<m then f i j else false := by
  induction n with
  | zero => simp [box]
  | succ n ih =>
    rw [box, coeff_append, coeff_row, ih]
    by_cases hj : j<m
    · by_cases hi : i=n
      · subst i; simp [hj]
      · by_cases hl : i<n
        · have hl' : i<n+1 := by omega
          simp [hj, hi, hl, hl']
        · have hl' : ¬i<n+1 := by omega
          simp [hj, hi, hl, hl']
    · simp [hj]

theorem finite (p : Poly) : ∃ N, ∀ i j, N ≤ i+j → coeff p i j=false := by
  induction p with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons m p ih =>
    rcases m with ⟨a,b⟩
    obtain ⟨N,hN⟩ := ih
    refine ⟨max N (a+b+1), ?_⟩
    intro i j hij
    have hNi : N ≤ i+j := Nat.le_trans (Nat.le_max_left _ _) hij
    have hneq : a≠i ∨ b≠j := by
      have hlt := Nat.le_trans (Nat.le_max_right N (a+b+1)) hij
      omega
    rw [coeff_cons, hN i j hNi]
    rcases hneq with h | h <;> simp [h]

end Raw
end TLMC506
