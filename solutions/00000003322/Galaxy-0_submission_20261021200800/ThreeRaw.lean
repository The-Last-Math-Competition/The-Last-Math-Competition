import Std
namespace ThreePoly.Raw
abbrev Monomial := Nat × Nat × Nat
abbrev Poly := List Monomial

def coeff : Poly → Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | (a,b,c)::l, i, j, k => (((a == i) && (b == j) && (c == k))) ^^ coeff l i j k

def shift (a b c : Nat) (l : Poly) : Poly :=
  l.map fun m => (a + m.1, b + m.2.1, c + m.2.2)

def mul : Poly → Poly → Poly
  | [], _ => []
  | (a,b,c)::l, q => shift a b c q ++ mul l q

@[simp] theorem coeff_nil (i j k : Nat) : coeff [] i j k = false := rfl
@[simp] theorem coeff_cons (a b c i j k : Nat) (l : Poly) :
    coeff ((a,b,c)::l) i j k = (((a == i) && (b == j) && (c == k)) ^^ coeff l i j k) := rfl
@[simp] theorem coeff_append (l n : Poly) (i j k : Nat) :
    coeff (l ++ n) i j k = (coeff l i j k ^^ coeff n i j k) := by
  induction l with
  | nil => simp [coeff]
  | cons m l ih => rcases m with ⟨a,b,c⟩; simp [coeff, ih]

@[simp] theorem shift_nil (a b c : Nat) : shift a b c [] = [] := rfl
@[simp] theorem shift_cons (a b c d e f : Nat) (l : Poly) :
    shift a b c ((d,e,f)::l) = (a+d,b+e,c+f)::shift a b c l := rfl
@[simp] theorem shift_append (a b c : Nat) (l n : Poly) :
    shift a b c (l ++ n) = shift a b c l ++ shift a b c n := by simp [shift]
@[simp] theorem shift_shift (a b c d e f : Nat) (l : Poly) :
    shift a b c (shift d e f l) = shift (a+d) (b+e) (c+f) l := by
  simp [shift, List.map_map, Function.comp_def, Nat.add_assoc]
@[simp] theorem shift_zero (l : Poly) : shift 0 0 0 l = l := by simp [shift]

theorem coeff_shift (a b c i j k : Nat) (l : Poly) :
    coeff (shift a b c l) i j k =
      if a ≤ i ∧ b ≤ j ∧ c ≤ k then coeff l (i-a) (j-b) (k-c) else false := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rcases m with ⟨d,e,f⟩
    rw [shift_cons, coeff_cons, ih]
    by_cases h : a ≤ i ∧ b ≤ j ∧ c ≤ k
    · rw [if_pos h, if_pos h, coeff_cons]
      have hx : (a+d == i) = (d == i-a) := by apply Bool.eq_iff_iff.mpr; simp; omega
      have hy : (b+e == j) = (e == j-b) := by apply Bool.eq_iff_iff.mpr; simp; omega
      have hz : (c+f == k) = (f == k-c) := by apply Bool.eq_iff_iff.mpr; simp; omega
      rw [hx,hy,hz]
    · rw [if_neg h, if_neg h]
      have he : ((a+d == i) && (b+e == j) && (c+f == k)) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        omega
      simp [he]

def Equiv (p q : Poly) : Prop := ∀ i j k, coeff p i j k = coeff q i j k

theorem equiv_refl (p : Poly) : Equiv p p := by intro i j k; rfl

theorem equiv_append {p q r s : Poly} (h : Equiv p q) (g : Equiv r s) :
    Equiv (p ++ r) (q ++ s) := by intro i j k; simp [h i j k, g i j k]

theorem equiv_shift {p q : Poly} (h : Equiv p q) (a b c : Nat) :
    Equiv (shift a b c p) (shift a b c q) := by intro i j k; simp only [coeff_shift]; rw [h]

@[simp] theorem mul_nil (p : Poly) : mul p [] = [] := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with ⟨a,b,c⟩; simp [mul, ih]
@[simp] theorem mul_append_left (p q r : Poly) : mul (p ++ q) r = mul p r ++ mul q r := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with ⟨a,b,c⟩; simp [mul, ih, List.append_assoc]

theorem mul_congr_right (p : Poly) {q r : Poly} (h : Equiv q r) :
    Equiv (mul p q) (mul p r) := by
  induction p with
  | nil => exact equiv_refl []
  | cons m p ih => rcases m with ⟨a,b,c⟩; exact equiv_append (equiv_shift h _ _ _) ih

theorem coeff_mul_append_right (p q r : Poly) (i j k : Nat) :
    coeff (mul p (q ++ r)) i j k = (coeff (mul p q) i j k ^^ coeff (mul p r) i j k) := by
  induction p with
  | nil => simp [mul]
  | cons m p ih =>
    rcases m with ⟨a,b,c⟩
    simp only [mul, shift_append, coeff_append, ih]
    generalize coeff (shift a b c q) i j k = A
    generalize coeff (shift a b c r) i j k = B
    generalize coeff (mul p q) i j k = C
    generalize coeff (mul p r) i j k = D
    cases A <;> cases B <;> cases C <;> cases D <;> rfl

@[simp] theorem mul_singleton_right (p : Poly) (a b c : Nat) :
    mul p [(a,b,c)] = shift a b c p := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with ⟨d,e,f⟩; simp [mul, shift, ih, Nat.add_comm]

@[simp] theorem mul_singleton_left (p : Poly) (a b c : Nat) :
    mul [(a,b,c)] p = shift a b c p := by simp [mul]

theorem mul_comm (p q : Poly) : Equiv (mul p q) (mul q p) := by
  induction p with
  | nil => simp [mul, Equiv]
  | cons m p ih =>
    rcases m with ⟨a,b,c⟩
    intro i j k
    rw [show (a,b,c)::p = [(a,b,c)] ++ p from rfl]
    simp only [mul_append_left, coeff_append, coeff_mul_append_right,
      mul_singleton_left, mul_singleton_right, ih i j k]

theorem mul_congr_left {p q : Poly} (h : Equiv p q) (r : Poly) :
    Equiv (mul p r) (mul q r) := by
  intro i j k
  rw [mul_comm p r i j k, mul_comm q r i j k]
  exact mul_congr_right r h i j k

theorem shift_mul_left (a b c : Nat) (p q : Poly) :
    mul (shift a b c p) q = shift a b c (mul p q) := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with ⟨d,e,f⟩; simp [mul, ih]

theorem mul_assoc (p q r : Poly) : mul (mul p q) r = mul p (mul q r) := by
  induction p with
  | nil => rfl
  | cons m p ih => rcases m with ⟨a,b,c⟩; simp [mul, shift_mul_left, ih]

/-- A finite coefficient cube enumerates a genuine finite monomial list. -/
def row (f : Nat → Bool) (a b : Nat) : Nat → Poly
  | 0 => []
  | n+1 => (if f n then [(a,b,n)] else []) ++ row f a b n

def plane (f : Nat → Nat → Bool) (a m : Nat) : Nat → Poly
  | 0 => []
  | n+1 => row (f n) a n m ++ plane f a m n

def box (f : Nat → Nat → Nat → Bool) (l m : Nat) : Nat → Poly
  | 0 => []
  | n+1 => plane (f n) n l m ++ box f l m n

theorem coeff_row (f : Nat → Bool) (a b n i j k : Nat) :
    coeff (row f a b n) i j k = if i=a ∧ j=b ∧ k<n then f k else false := by
  induction n with
  | zero => simp [row]
  | succ n ih =>
    rw [row, coeff_append, ih]
    have hs : coeff (if f n then [(a,b,n)] else []) i j k =
        if i=a ∧ j=b ∧ k=n then f n else false := by
      cases hf : f n
      · simp
      · by_cases hi : i=a
        · subst i
          by_cases hj : j=b
          · subst j
            by_cases hk : k=n
            · subst k; simp [coeff]
            · have hn : n ≠ k := Ne.symm hk
              simp [coeff, hk, hn]
          · have hb : b ≠ j := Ne.symm hj
            simp [coeff, hj, hb]
        · have ha : a ≠ i := Ne.symm hi
          simp [coeff, hi, ha]
    rw [hs]
    by_cases hi : i=a
    · subst i
      by_cases hj : j=b
      · subst j
        by_cases hk : k=n
        · subst k; simp
        · by_cases hl : k<n
          · have hl' : k<n+1 := by omega
            simp [hk, hl, hl']
          · have hl' : ¬k<n+1 := by omega
            simp [hk, hl, hl']
      · simp [hj]
    · simp [hi]

theorem coeff_plane (f : Nat → Nat → Bool) (a n m i j k : Nat) :
    coeff (plane f a m n) i j k = if i=a ∧ j<n ∧ k<m then f j k else false := by
  induction n with
  | zero => simp [plane]
  | succ n ih =>
    rw [plane, coeff_append, coeff_row, ih]
    by_cases hi : i=a
    · by_cases hk : k<m
      · by_cases hj : j=n
        · subst j; simp [hi, hk]
        · by_cases hl : j<n
          · have hl' : j<n+1 := by omega
            simp [hi, hk, hj, hl, hl']
          · have hl' : ¬j<n+1 := by omega
            simp [hi, hk, hj, hl, hl']
      · simp [hi, hk]
    · simp [hi]

theorem coeff_box (f : Nat → Nat → Nat → Bool) (l m n i j k : Nat) :
    coeff (box f l m n) i j k = if i<n ∧ j<m ∧ k<l then f i j k else false := by
  induction n with
  | zero => simp [box]
  | succ n ih =>
    rw [box, coeff_append, coeff_plane, ih]
    by_cases hj : j<m
    · by_cases hk : k<l
      · by_cases hi : i=n
        · subst i; simp [hj, hk]
        · by_cases hl : i<n
          · have hl' : i<n+1 := by omega
            simp [hj, hk, hi, hl, hl']
          · have hl' : ¬i<n+1 := by omega
            simp [hj, hk, hi, hl, hl']
      · simp [hj, hk]
    · simp [hj]

theorem finite (p : Poly) : ∃ N, ∀ i j k, N ≤ i+j+k → coeff p i j k=false := by
  induction p with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons m p ih =>
    rcases m with ⟨a,b,c⟩
    obtain ⟨N,hN⟩ := ih
    refine ⟨max N (a+b+c+1), ?_⟩
    intro i j k h
    have hNi : N ≤ i+j+k := Nat.le_trans (Nat.le_max_left _ _) h
    have hneq : a≠i ∨ b≠j ∨ c≠k := by
      have hlt := Nat.le_trans (Nat.le_max_right N (a+b+c+1)) h
      omega
    rw [coeff_cons, hN i j k hNi]
    rcases hneq with h | h | h <;> simp [h]

end ThreePoly.Raw
