import Rates
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PIR

def total : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f ⟨0, by omega⟩ + total n (fun i => f i.succ)

def count (n : Nat) (p : Fin n → Bool) : Nat :=
  total n (fun i => if p i then 1 else 0)

theorem total_add (n : Nat) (f g : Fin n → Nat) :
    total n (fun i => f i + g i) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total]; rw [ih]; omega

theorem total_mono (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    total n f ≤ total n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [total]
    have ht := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
    have h0 := h ⟨0, by omega⟩
    omega

theorem total_const (n k : Nat) : total n (fun _ => k) = n*k := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih, Nat.succ_mul]; omega

theorem total_ext (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i = g i) :
    total n f = total n g := by
  apply Nat.le_antisymm
  · exact total_mono n f g (fun i => Nat.le_of_eq (h i))
  · exact total_mono n g f (fun i => Nat.le_of_eq (h i).symm)

theorem count_injection_bound {n m : Nat} (p : Fin n → Bool) (f : Fin n → Fin m)
    (hf : ∀ a b, p a = true → p b = true → f a = f b → a = b) :
    count n p ≤ m := by
  induction n generalizing m with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    let z : Fin (n+1) := ⟨0, by omega⟩
    cases hp : p z with
    | false =>
      have ht := ih (fun i => p i.succ) (fun i => f i.succ) (by
        intro a b ha hb he
        have hh := hf a.succ b.succ ha hb he
        exact Fin.ext (by have hv := congrArg (fun x : Fin (n+1) => x.val) hh; simp at hv; exact hv))
      have hp0 : p 0 = false := hp
      simpa [count,total,hp0] using ht
    | true =>
      cases m with
      | zero => exact Fin.elim0 (f z)
      | succ m =>
        let pivot := (f z).val
        have hne (a : Fin n) (ha : p a.succ = true) : (f a.succ).val ≠ pivot := by
          intro he
          have hh := hf a.succ z ha hp (Fin.ext he)
          have hv := congrArg (fun x : Fin (n+1) => x.val) hh
          simp [z] at hv
        by_cases hm : m = 0
        · subst m
          have hn (a : Fin n) : p a.succ = false := by
            cases he : p a.succ with
            | false => rfl
            | true =>
              have hne' := hne a he
              have hv := (f a.succ).isLt
              have hpiv := (f z).isLt
              change (f a.succ).val ≠ (f z).val at hne'
              omega
          have ht : count n (fun i => p i.succ) = 0 := by
            unfold count
            calc
              total n (fun i => if p i.succ then 1 else 0) = total n (fun _ => 0) :=
                total_ext _ _ _ (by intro i; simp [hn i])
              _ = 0 := by rw [total_const]; omega
          have hp0 : p 0 = true := hp
          simpa [count, total, hp0, Nat.add_comm] using Nat.succ_le_succ (Nat.le_of_eq ht)
        · let g : Fin n → Fin m := fun a =>
            if ha : p a.succ = true then
              ⟨shrink (f a.succ).val pivot, by
                have hv := (f a.succ).isLt
                have hpiv : pivot < m+1 := (f z).isLt
                have hne' := hne a ha
                unfold shrink
                split <;> omega⟩
            else ⟨0, by omega⟩
          have hg : ∀ a b, p a.succ = true → p b.succ = true → g a = g b → a = b := by
            intro a b ha hb he
            have hv := congrArg Fin.val he
            simp only [g,ha,hb,dif_pos] at hv
            have heq := shrink_inj _ _ _ (hne a ha) (hne b hb) hv
            have hh := hf a.succ b.succ ha hb (Fin.ext heq)
            exact Fin.ext (by have hv := congrArg (fun x : Fin (n+1) => x.val) hh; simp at hv; exact hv)
          have ht := ih (fun i => p i.succ) g hg
          have hp0 : p 0 = true := hp
          simpa [count,total,hp0,Nat.add_comm] using Nat.succ_le_succ ht


theorem count_le (n : Nat) (p : Fin n → Bool) : count n p ≤ n := by
  have h := total_mono n (fun i => if p i then 1 else 0) (fun _ => 1)
    (by intro i; split <;> omega)
  simpa [count, total_const] using h

theorem total_mul_left (n k : Nat) (f : Fin n → Nat) :
    total n (fun i => k * f i) = k * total n f := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih, Nat.mul_add]

theorem total_mul_right (n k : Nat) (f : Fin n → Nat) :
    total n (fun i => f i * k) = total n f * k := by
  simpa [Nat.mul_comm] using total_mul_left n k f

-- Each seed fixes the same query for all desired indices. The three decoders
-- may differ, including their coupled private randomness. Download length is
-- query-dependent, so its average rather than its maximum is bounded below.
structure CoupledScheme (B R : Nat) (Query : Type) where
  query : Fin R → Query
  length : Query → Nat
  answer : (q : Query) → Database B → Fin (2 ^ length q)
  decode : (r : Fin R) → Fin 3 → Fin (2 ^ length (query r)) → Fin B

def errorAt {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) (r : Fin R) (i : Fin 3)
    (x : Fin (B * (B * B))) : Bool :=
  decide (p.decode r i (p.answer (p.query r) (unpack B hB x)) ≠ item (unpack B hB x) i)

def goodAt {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) (r : Fin R) (x : Fin (B * (B * B))) : Bool :=
  !(errorAt hB p r 0 x || errorAt hB p r 1 x || errorAt hB p r 2 x)

theorem good_implies_correct {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) (r : Fin R) (x : Fin (B * (B * B)))
    (h : goodAt hB p r x = true) (i : Fin 3) :
    p.decode r i (p.answer (p.query r) (unpack B hB x)) = item (unpack B hB x) i := by
  have hi := i.isLt
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hv with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hcases with rfl | rfl | rfl <;> simp_all [goodAt, errorAt]

theorem good_count_bound {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) (r : Fin R) :
    count (B * (B * B)) (goodAt hB p r) ≤ 2 ^ p.length (p.query r) := by
  apply count_injection_bound _ (fun x => p.answer (p.query r) (unpack B hB x))
  intro x y hx hy he
  apply unpack_injective B hB x y
  apply item_ext
  intro i
  rw [← good_implies_correct hB p r x hx i,
      ← good_implies_correct hB p r y hy i, he]

theorem bool_union_bound (a b c : Bool) :
    1 ≤ (if !(a || b || c) then 1 else 0) +
      ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem per_seed_union_bound {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) (r : Fin R) :
    B * (B * B) ≤ count (B * (B * B)) (goodAt hB p r) +
      (count (B * (B * B)) (errorAt hB p r 0) +
       count (B * (B * B)) (errorAt hB p r 1) +
       count (B * (B * B)) (errorAt hB p r 2)) := by
  have h := total_mono (B * (B * B)) (fun _ => 1)
    (fun x => (if goodAt hB p r x then 1 else 0) +
     ((if errorAt hB p r 0 x then 1 else 0) +
      (if errorAt hB p r 1 x then 1 else 0) +
      (if errorAt hB p r 2 x then 1 else 0)))
    (by intro x; exact bool_union_bound _ _ _)
  simpa only [total_const, Nat.mul_one, total_add, count] using h


theorem good_information_bound (n d g : Nat) (hg : g ≤ 2^n) (ha : g ≤ 2^d) :
    n*g ≤ 2^n*(d+1) := by
  by_cases h : d ≤ n
  · exact Nat.le_trans (Nat.mul_le_mul_left n ha) (power_information_bound n d h)
  · calc
      n*g ≤ n*2^n := Nat.mul_le_mul_left n hg
      _ ≤ (d+1)*2^n := Nat.mul_le_mul_right (2^n) (by omega)
      _ = 2^n*(d+1) := Nat.mul_comm _ _

def goodTotal {B R : Nat} {Q : Type} (hB : 0 < B) (p : CoupledScheme B R Q) : Nat :=
  total R (fun r => count (B * (B * B)) (goodAt hB p r))
def errorTotal {B R : Nat} {Q : Type} (hB : 0 < B) (p : CoupledScheme B R Q) : Nat :=
  total R (fun r => count (B * (B * B)) (errorAt hB p r 0) +
    count (B * (B * B)) (errorAt hB p r 1) + count (B * (B * B)) (errorAt hB p r 2))
def downloadTotal {B R : Nat} {Q : Type} (p : CoupledScheme B R Q) : Nat :=
  total R (fun r => p.length (p.query r))

theorem total_union_bound {B R : Nat} {Q : Type} (hB : 0 < B)
    (p : CoupledScheme B R Q) : R*(B*(B*B)) ≤ goodTotal hB p + errorTotal hB p := by
  have h := total_mono R (fun _ => B*(B*B)) _ (fun r => per_seed_union_bound hB p r)
  simpa only [total_const, total_add, goodTotal, errorTotal] using h

theorem binary_database_card (L : Nat) : 2^L*(2^L*2^L) = 2^(3*L) := by
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

theorem expected_information_bound {L R : Nat} {Q : Type}
    (p : CoupledScheme (2^L) R Q) :
    (3*L)*goodTotal (Nat.two_pow_pos L) p ≤ 2^(3*L)*(downloadTotal p + R) := by
  let hB : 0 < 2^L := Nat.two_pow_pos L
  have point (r : Fin R) :
      (3*L)*count (2^L*(2^L*2^L)) (goodAt hB p r) ≤
      2^(3*L)*(p.length (p.query r)+1) := by
    apply good_information_bound
    · simpa only [binary_database_card] using count_le _ (goodAt hB p r)
    · exact good_count_bound hB p r
  have h := total_mono R _ _ point
  simpa only [total_mul_left, total_add, total_const, Nat.mul_one, goodTotal, downloadTotal] using h

end PIR
