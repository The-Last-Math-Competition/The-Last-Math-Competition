import Conjecture00000000505.Ring

namespace Conjecture00000000505

open Classical

section FinSum
variable {R : Type u} [CAlgRing R]

/-- Finite sum `∑_{i=0}^{n-1} f(i)` in a commutative ring `R`. -/
def finSum : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => finSum n f + f n

theorem finSum_zero_fn : ∀ (n : Nat) (f : Nat → R),
    (∀ i : Nat, i < n → f i = 0) → finSum n f = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
    change finSum n f + f n = 0
    rw [finSum_zero_fn n f (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h n (Nat.lt_succ_self n), r_add_zero]

theorem finSum_congr : ∀ (n : Nat) {f g : Nat → R},
    (∀ i : Nat, i < n → f i = g i) → finSum n f = finSum n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    change finSum n f + f n = finSum n g + g n
    rw [finSum_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem finSum_add : ∀ (n : Nat) (f g : Nat → R),
    finSum n (fun i => f i + g i) = finSum n f + finSum n g
  | 0, _, _ => (r_add_zero 0).symm
  | n + 1, f, g => by
    change finSum n (fun i => f i + g i) + (f n + g n) =
      (finSum n f + f n) + (finSum n g + g n)
    rw [finSum_add n f g]
    calc
      (finSum n f + finSum n g) + (f n + g n)
        = finSum n f + (finSum n g + (f n + g n)) := by rw [r_add_assoc]
      _ = finSum n f + ((f n + g n) + finSum n g) := by rw [r_add_comm (finSum n g)]
      _ = finSum n f + (f n + (g n + finSum n g)) := by rw [r_add_assoc (f n)]
      _ = (finSum n f + f n) + (finSum n g + g n) := by
          rw [← r_add_assoc (finSum n f), r_add_comm (g n) (finSum n g)]

theorem finSum_mul_left (c : R) : ∀ (n : Nat) (f : Nat → R),
    c * finSum n f = finSum n (fun i => c * f i)
  | 0, _ => r_mul_zero c
  | n + 1, f => by
    change c * (finSum n f + f n) = finSum n (fun i => c * f i) + c * f n
    rw [r_left_distrib, finSum_mul_left c n f]

theorem finSum_mul_right (c : R) (n : Nat) (f : Nat → R) :
    finSum n f * c = finSum n (fun i => f i * c) := by
  rw [r_mul_comm, finSum_mul_left]
  exact finSum_congr n (fun i _ => r_mul_comm c (f i))

theorem finSum_succ_left : ∀ (n : Nat) (f : Nat → R),
    finSum (n + 1) f = f 0 + finSum n (fun i => f (i + 1))
  | 0, f => by
    change (0 : R) + f 0 = f 0 + 0
    rw [r_zero_add, r_add_zero]
  | n + 1, f => by
    change finSum (n + 1) f + f (n + 1) = f 0 + (finSum n (fun i => f (i + 1)) + f (n + 1))
    rw [finSum_succ_left n f, r_add_assoc]

theorem finSum_flip : ∀ (d : Nat) (f : Nat → R),
    finSum (d + 1) f = finSum (d + 1) (fun i => f (d - i))
  | 0, f => rfl
  | d + 1, f => by
    rw [finSum_succ_left (d + 1) (fun i => f (d + 1 - i))]
    have hsub : finSum (d + 1) (fun i => f (d + 1 - (i + 1))) =
        finSum (d + 1) (fun i => f (d - i)) :=
      finSum_congr (d + 1) (fun i _ => by
        have heq : d + 1 - (i + 1) = d - i := by omega
        rw [heq])
    rw [hsub, ← finSum_flip d f]
    change finSum (d + 1) f + f (d + 1) = f (d + 1 - 0) + finSum (d + 1) f
    have hz : d + 1 - 0 = d + 1 := by omega
    rw [hz, r_add_comm]

theorem finSum_split (k : Nat) : ∀ (m : Nat) (f : Nat → R),
    finSum (k + m) f = finSum k f + finSum m (fun j => f (k + j))
  | 0, f => by
    have hz : k + 0 = k := by omega
    rw [hz]
    exact (r_add_zero (finSum k f)).symm
  | m + 1, f => by
    have hs : k + (m + 1) = (k + m) + 1 := by omega
    rw [hs]
    change finSum (k + m) f + f (k + m) = finSum k f + (finSum m (fun j => f (k + j)) + f (k + m))
    rw [finSum_split k m f, r_add_assoc]

theorem finSum_single : ∀ (n k : Nat) (f : Nat → R),
    k < n → (∀ i : Nat, i < n → i ≠ k → f i = 0) → finSum n f = f k
  | 0, _, _, hk, _ => by omega
  | n + 1, k, f, hk, hzero => by
    change finSum n f + f n = f k
    by_cases hkn : k = n
    · subst hkn
      rw [finSum_zero_fn k f (fun i hi => hzero i (Nat.lt_succ_of_lt hi) (by omega)),
          r_zero_add]
    · have hlt : k < n := by omega
      rw [finSum_single n k f hlt (fun i hi hne => hzero i (Nat.lt_succ_of_lt hi) hne),
          hzero n (Nat.lt_succ_self n) (Ne.symm hkn), r_add_zero]

end FinSum

/-- Univariate polynomial ring `R[X]`, represented extensionally as finitely supported
coefficient sequences `Nat → R`. -/
def Poly (R : Type u) [CAlgRing R] : Type u :=
  { coeff : Nat → R // ∃ B : Nat, ∀ d : Nat, B ≤ d → coeff d = 0 }

section PolyOps
variable {R : Type u} [CAlgRing R]

theorem Poly.ext {p q : Poly R} (h : ∀ d : Nat, p.val d = q.val d) : p = q :=
  Subtype.ext (funext h)

def Poly.zero : Poly R := ⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩

def Poly.one : Poly R := ⟨fun d => if d = 0 then 1 else 0, ⟨1, fun d hd => by
  have hne : d ≠ 0 := by omega
  simp [hne]⟩⟩

def Poly.add (p q : Poly R) : Poly R :=
  ⟨fun d => p.val d + q.val d, by
    rcases p.property with ⟨Bp, hp⟩
    rcases q.property with ⟨Bq, hq⟩
    refine ⟨Bp + Bq, fun d hd => ?_⟩
    dsimp only
    rw [hp d (by omega), hq d (by omega), r_add_zero]⟩

def Poly.neg (p : Poly R) : Poly R :=
  ⟨fun d => -(p.val d), by
    rcases p.property with ⟨Bp, hp⟩
    refine ⟨Bp, fun d hd => ?_⟩
    dsimp only
    rw [hp d hd, r_neg_zero]⟩

def Poly.mul (p q : Poly R) : Poly R :=
  ⟨fun d => finSum (d + 1) (fun i => p.val i * q.val (d - i)), by
    rcases p.property with ⟨Bp, hp⟩
    rcases q.property with ⟨Bq, hq⟩
    refine ⟨Bp + Bq, fun d hd => ?_⟩
    apply finSum_zero_fn
    intro i _
    by_cases hi : Bp ≤ i
    · rw [hp i hi, r_zero_mul]
    · rw [hq (d - i) (by omega), r_mul_zero]⟩

/-- Monomial `c * X^k`. -/
def Poly.mono (k : Nat) (c : R) : Poly R :=
  ⟨fun d => if d = k then c else 0, ⟨k + 1, fun d hd => by
    have hne : d ≠ k := by omega
    simp [hne]⟩⟩

/-- Constant polynomial embedding `C : R → R[X]`. -/
def Poly.C (c : R) : Poly R := Poly.mono 0 c

/-- Indeterminate `X : R[X]`. -/
def Poly.X : Poly R := Poly.mono 1 1

/-- Truncation keeping coefficients strictly below `k`. -/
def Poly.trunc (k : Nat) (p : Poly R) : Poly R :=
  ⟨fun d => if d < k then p.val d else 0, ⟨k, fun d hd => by
    have hnl : ¬ (d < k) := by omega
    simp [hnl]⟩⟩

theorem Poly.trunc_succ (k : Nat) (p : Poly R) :
    Poly.trunc (k + 1) p = Poly.add (Poly.trunc k p) (Poly.mono k (p.val k)) := by
  apply Poly.ext
  intro d
  change (if d < k + 1 then p.val d else 0) =
    (if d < k then p.val d else 0) + (if d = k then p.val k else 0)
  by_cases h1 : d < k
  · have h2 : d < k + 1 := by omega
    have h3 : d ≠ k := by omega
    simp [h1, h2, h3, r_add_zero]
  · by_cases h3 : d = k
    · subst h3
      have h2 : d < d + 1 := by omega
      simp [h1, h2, r_zero_add]
    · have h2 : ¬ (d < k + 1) := by omega
      simp [h1, h2, h3, r_add_zero]

theorem Poly.eq_trunc_of_bound {B : Nat} {p : Poly R}
    (hp : ∀ d : Nat, B ≤ d → p.val d = 0) : p = Poly.trunc B p := by
  apply Poly.ext
  intro d
  change p.val d = if d < B then p.val d else 0
  by_cases h : d < B
  · simp [h]
  · rw [hp d (by omega)]
    simp [h]

theorem Poly.mono_mul_coeff (k : Nat) (c : R) (q : Poly R) (d : Nat) :
    (Poly.mul (Poly.mono k c) q).val d = if k ≤ d then c * q.val (d - k) else 0 := by
  change finSum (d + 1) (fun i => (if i = k then c else 0) * q.val (d - i)) =
    if k ≤ d then c * q.val (d - k) else 0
  by_cases hk : k ≤ d
  · simp [hk]
    have hlt : k < d + 1 := by omega
    rw [finSum_single (d + 1) k _ hlt]
    · simp
    · intro i _ hne
      simp [hne, r_zero_mul]
  · simp [hk]
    apply finSum_zero_fn
    intro i hi
    have hne : i ≠ k := by omega
    simp [hne, r_zero_mul]

theorem Poly.left_distrib_aux (p q s : Poly R) :
    Poly.mul p (Poly.add q s) = Poly.add (Poly.mul p q) (Poly.mul p s) := by
  apply Poly.ext
  intro d
  change finSum (d + 1) (fun i => p.val i * (q.val (d - i) + s.val (d - i))) =
    finSum (d + 1) (fun i => p.val i * q.val (d - i)) +
    finSum (d + 1) (fun i => p.val i * s.val (d - i))
  rw [← finSum_add]
  exact finSum_congr (d + 1) (fun i _ => r_left_distrib _ _ _)

theorem Poly.mul_comm_aux (p q : Poly R) : Poly.mul p q = Poly.mul q p := by
  apply Poly.ext
  intro d
  change finSum (d + 1) (fun i => p.val i * q.val (d - i)) =
    finSum (d + 1) (fun i => q.val i * p.val (d - i))
  rw [finSum_flip d (fun i => p.val i * q.val (d - i))]
  refine finSum_congr (d + 1) (fun i hi => ?_)
  have hsub : d - (d - i) = i := by omega
  rw [hsub, r_mul_comm]

theorem Poly.right_distrib_aux (p q s : Poly R) :
    Poly.mul (Poly.add p q) s = Poly.add (Poly.mul p s) (Poly.mul q s) := by
  rw [Poly.mul_comm_aux, Poly.left_distrib_aux, Poly.mul_comm_aux s p, Poly.mul_comm_aux s q]

theorem Poly.zero_mul_aux (q : Poly R) : Poly.mul Poly.zero q = Poly.zero := by
  apply Poly.ext
  intro d
  change finSum (d + 1) (fun i => (0 : R) * q.val (d - i)) = 0
  exact finSum_zero_fn (d + 1) _ (fun _ _ => r_zero_mul _)

theorem Poly.mono_mul_assoc (k : Nat) (c : R) (q s : Poly R) :
    Poly.mul (Poly.mul (Poly.mono k c) q) s = Poly.mul (Poly.mono k c) (Poly.mul q s) := by
  apply Poly.ext
  intro d
  rw [Poly.mono_mul_coeff k c (Poly.mul q s) d]
  change finSum (d + 1) (fun i => (Poly.mul (Poly.mono k c) q).val i * s.val (d - i)) =
    if k ≤ d then c * (Poly.mul q s).val (d - k) else 0
  by_cases hk : k ≤ d
  · simp [hk]
    have hsplit : d + 1 = k + (d - k + 1) := by omega
    rw [hsplit, finSum_split k (d - k + 1)]
    have hz : finSum k (fun i => (Poly.mul (Poly.mono k c) q).val i * s.val (d - i)) = 0 := by
      apply finSum_zero_fn
      intro i hi
      rw [Poly.mono_mul_coeff]
      have hnk : ¬ (k ≤ i) := by omega
      simp [hnk, r_zero_mul]
    rw [hz, r_zero_add]
    change finSum (d - k + 1)
        (fun j => (Poly.mul (Poly.mono k c) q).val (k + j) * s.val (d - (k + j))) =
      c * finSum (d - k + 1) (fun j => q.val j * s.val (d - k - j))
    rw [finSum_mul_left]
    refine finSum_congr (d - k + 1) (fun j _ => ?_)
    rw [Poly.mono_mul_coeff]
    have hkj : k ≤ k + j := by omega
    have hsub1 : k + j - k = j := by omega
    have hsub2 : d - (k + j) = d - k - j := by omega
    simp [hkj, hsub1, hsub2, r_mul_assoc]
  · simp [hk]
    apply finSum_zero_fn
    intro i hi
    rw [Poly.mono_mul_coeff]
    have hnk : ¬ (k ≤ i) := by omega
    simp [hnk, r_zero_mul]

theorem Poly.trunc_mul_assoc : ∀ (B : Nat) (p q s : Poly R),
    Poly.mul (Poly.mul (Poly.trunc B p) q) s = Poly.mul (Poly.trunc B p) (Poly.mul q s)
  | 0, p, q, s => by
    have hz : Poly.trunc 0 p = Poly.zero := by
      apply Poly.ext
      intro d
      change (if d < 0 then p.val d else 0) = 0
      simp
    rw [hz, Poly.zero_mul_aux, Poly.zero_mul_aux, Poly.zero_mul_aux]
  | k + 1, p, q, s => by
    rw [Poly.trunc_succ, Poly.right_distrib_aux, Poly.right_distrib_aux,
        Poly.right_distrib_aux, Poly.trunc_mul_assoc k p q s, Poly.mono_mul_assoc]

instance : CAlgRing (Poly R) where
  zero := Poly.zero
  one := Poly.one
  add := Poly.add
  mul := Poly.mul
  neg := Poly.neg
  add_assoc a b c := Poly.ext (fun d => r_add_assoc (a.val d) (b.val d) (c.val d))
  add_comm a b := Poly.ext (fun d => r_add_comm (a.val d) (b.val d))
  zero_add a := Poly.ext (fun d => r_zero_add (a.val d))
  add_left_neg a := Poly.ext (fun d => r_add_left_neg (a.val d))
  mul_assoc a b c := by
    rcases a.property with ⟨Ba, ha⟩
    have heq := Poly.eq_trunc_of_bound ha
    rw [heq]
    exact Poly.trunc_mul_assoc Ba a b c
  mul_comm := Poly.mul_comm_aux
  one_mul a := by
    change Poly.mul (Poly.mono 0 1) a = a
    apply Poly.ext
    intro d
    rw [Poly.mono_mul_coeff]
    have h0 : 0 ≤ d := Nat.zero_le d
    have hsub : d - 0 = d := by omega
    simp [h0, hsub, r_one_mul]
  left_distrib := Poly.left_distrib_aux

theorem Poly.mono_mul_coeff' (k : Nat) (c : R) (q : Poly R) (d : Nat) :
    (Poly.mono k c * q).val d = if k ≤ d then c * q.val (d - k) else 0 :=
  Poly.mono_mul_coeff k c q d

theorem Poly.C_add (a b : R) : Poly.C (a + b) = Poly.C a + Poly.C b := by
  apply Poly.ext
  intro d
  change (if d = 0 then a + b else 0) = (if d = 0 then a else 0) + (if d = 0 then b else 0)
  by_cases h : d = 0
  · simp [h]
  · simp [h, r_add_zero]

theorem Poly.C_mul (a b : R) : Poly.C (a * b) = Poly.C a * Poly.C b := by
  apply Poly.ext
  intro d
  change (if d = 0 then a * b else 0) = (Poly.mono 0 a * Poly.C b).val d
  rw [Poly.mono_mul_coeff' 0 a (Poly.C b) d]
  change (if d = 0 then a * b else 0) = if 0 ≤ d then a * (if d - 0 = 0 then b else 0) else 0
  by_cases h : d = 0
  · simp [h]
  · have h0 : 0 ≤ d := Nat.zero_le d
    have hsub : d - 0 ≠ 0 := by omega
    simp [h, h0, hsub, r_mul_zero]

theorem Poly.C_inj {a b : R} (h : Poly.C a = Poly.C b) : a = b := by
  have h0 : (Poly.C a).val 0 = (Poly.C b).val 0 := congrArg (fun p => p.val 0) h
  exact h0

/-- Polynomial evaluation `eval p x = ∑_{i=0}^{B-1} p_i x^i`. -/
def Poly.evalAt (B : Nat) (p : Poly R) (x : R) : R :=
  finSum B (fun i => p.val i * rpow x i)

theorem Poly.evalAt_eq_of_le {B1 B2 : Nat} {p : Poly R} (hle : B1 ≤ B2)
    (hp : ∀ d : Nat, B1 ≤ d → p.val d = 0) (x : R) :
    Poly.evalAt B2 p x = Poly.evalAt B1 p x := by
  have hsplit : B2 = B1 + (B2 - B1) := by omega
  unfold Poly.evalAt
  rw [hsplit, finSum_split B1 (B2 - B1)]
  have hz : finSum (B2 - B1) (fun j => p.val (B1 + j) * rpow x (B1 + j)) = 0 := by
    apply finSum_zero_fn
    intro j _
    rw [hp (B1 + j) (by omega), r_zero_mul]
  rw [hz, r_add_zero]

theorem Poly.evalAt_indep {B1 B2 : Nat} {p : Poly R}
    (hp1 : ∀ d : Nat, B1 ≤ d → p.val d = 0)
    (hp2 : ∀ d : Nat, B2 ≤ d → p.val d = 0) (x : R) :
    Poly.evalAt B1 p x = Poly.evalAt B2 p x := by
  calc
    Poly.evalAt B1 p x = Poly.evalAt (B1 + B2) p x :=
      (Poly.evalAt_eq_of_le (by omega) hp1 x).symm
    _ = Poly.evalAt B2 p x :=
      Poly.evalAt_eq_of_le (by omega) hp2 x

noncomputable def Poly.eval (p : Poly R) (x : R) : R :=
  Poly.evalAt (Classical.choose p.property) p x

theorem Poly.eval_eq_evalAt {B : Nat} (p : Poly R)
    (hp : ∀ d : Nat, B ≤ d → p.val d = 0) (x : R) :
    Poly.eval p x = Poly.evalAt B p x :=
  Poly.evalAt_indep (Classical.choose_spec p.property) hp x

theorem Poly.eval_zero (x : R) : Poly.eval (0 : Poly R) x = 0 := by
  rw [Poly.eval_eq_evalAt (0 : Poly R) (B := 0) (fun _ _ => rfl)]
  rfl

theorem Poly.eval_one (x : R) : Poly.eval (1 : Poly R) x = 1 := by
  rw [Poly.eval_eq_evalAt (1 : Poly R) (B := 1) (fun d hd => by
    change (if d = 0 then (1 : R) else 0) = 0
    have hne : d ≠ 0 := by omega
    simp [hne])]
  change (0 : R) + (1 : R) * 1 = 1
  rw [r_zero_add, r_one_mul]

theorem Poly.eval_C (c x : R) : Poly.eval (Poly.C c) x = c := by
  rw [Poly.eval_eq_evalAt (Poly.C c) (B := 1) (fun d hd => by
    change (if d = 0 then c else 0) = 0
    have hne : d ≠ 0 := by omega
    simp [hne])]
  change (0 : R) + c * 1 = c
  rw [r_zero_add, r_mul_one]

theorem Poly.eval_X (x : R) : Poly.eval (Poly.X : Poly R) x = x := by
  rw [Poly.eval_eq_evalAt (Poly.X : Poly R) (B := 2) (fun d hd => by
    change (if d = 1 then (1 : R) else 0) = 0
    have hne : d ≠ 1 := by omega
    simp [hne])]
  change ((0 : R) + (0 : R) * 1) + (1 : R) * (x * 1) = x
  rw [r_zero_mul, r_add_zero, r_zero_add, r_one_mul, r_mul_one]

theorem Poly.eval_mono (k : Nat) (c x : R) :
    Poly.eval (Poly.mono k c) x = c * rpow x k := by
  rw [Poly.eval_eq_evalAt (Poly.mono k c) (B := k + 1) (fun d hd => by
    change (if d = k then c else 0) = 0
    have hne : d ≠ k := by omega
    simp [hne])]
  unfold Poly.evalAt
  rw [finSum_single (k + 1) k _ (Nat.lt_succ_self k)]
  · change (if k = k then c else 0) * rpow x k = c * rpow x k
    simp
  · intro i _ hne
    change (if i = k then c else 0) * rpow x i = 0
    simp [hne, r_zero_mul]

theorem Poly.eval_add (p q : Poly R) (x : R) :
    Poly.eval (p + q) x = Poly.eval p x + Poly.eval q x := by
  rcases p.property with ⟨Bp, hp⟩
  rcases q.property with ⟨Bq, hq⟩
  have hpq : ∀ d : Nat, Bp + Bq ≤ d → (p + q).val d = 0 := by
    intro d hd
    change p.val d + q.val d = 0
    rw [hp d (by omega), hq d (by omega), r_add_zero]
  rw [Poly.eval_eq_evalAt (p + q) hpq,
      Poly.eval_eq_evalAt p (B := Bp + Bq) (fun d hd => hp d (by omega)),
      Poly.eval_eq_evalAt q (B := Bp + Bq) (fun d hd => hq d (by omega))]
  unfold Poly.evalAt
  rw [← finSum_add]
  exact finSum_congr (Bp + Bq) (fun i _ => r_right_distrib (p.val i) (q.val i) (rpow x i))

theorem Poly.eval_neg (p : Poly R) (x : R) :
    Poly.eval (-p) x = -(Poly.eval p x) := by
  apply r_add_left_cancel (a := Poly.eval p x)
  rw [← Poly.eval_add, r_add_right_neg, Poly.eval_zero, r_add_right_neg]

theorem Poly.eval_sub (p q : Poly R) (x : R) :
    Poly.eval (p - q) x = Poly.eval p x - Poly.eval q x := by
  change Poly.eval (p + (-q)) x = Poly.eval p x + (-(Poly.eval q x))
  rw [Poly.eval_add, Poly.eval_neg]

theorem rpow_add_aux (x : R) : ∀ k j : Nat, rpow x (k + j) = rpow x k * rpow x j
  | 0, j => by
    have hz : 0 + j = j := by omega
    rw [hz]
    exact (r_one_mul (rpow x j)).symm
  | k + 1, j => by
    have hs : (k + 1) + j = (k + j) + 1 := by omega
    rw [hs, rpow_succ, rpow_succ, rpow_add_aux x k j, r_mul_assoc]

theorem Poly.eval_mono_mul (k : Nat) (c : R) (q : Poly R) (x : R) :
    Poly.eval (Poly.mono k c * q) x = Poly.eval (Poly.mono k c) x * Poly.eval q x := by
  rcases q.property with ⟨Bq, hq⟩
  have hmq : ∀ d : Nat, k + Bq ≤ d → (Poly.mono k c * q).val d = 0 := by
    intro d hd
    rw [Poly.mono_mul_coeff']
    by_cases hk : k ≤ d
    · simp [hk, hq (d - k) (by omega), r_mul_zero]
    · simp [hk]
  rw [Poly.eval_eq_evalAt (Poly.mono k c * q) hmq,
      Poly.eval_mono, Poly.eval_eq_evalAt q hq]
  unfold Poly.evalAt
  rw [finSum_split k Bq]
  have hz : finSum k (fun i => (Poly.mono k c * q).val i * rpow x i) = 0 := by
    apply finSum_zero_fn
    intro i hi
    rw [Poly.mono_mul_coeff']
    have hnk : ¬ (k ≤ i) := by omega
    simp [hnk, r_zero_mul]
  rw [hz, r_zero_add, finSum_mul_left]
  refine finSum_congr Bq (fun j _ => ?_)
  rw [Poly.mono_mul_coeff']
  have hkj : k ≤ k + j := by omega
  have hsub : k + j - k = j := by omega
  simp [hkj, hsub]
  rw [rpow_add_aux x k j]
  calc
    (c * q.val j) * (rpow x k * rpow x j)
      = c * (q.val j * (rpow x k * rpow x j)) := by rw [r_mul_assoc]
    _ = c * ((q.val j * rpow x k) * rpow x j) := by rw [← r_mul_assoc (q.val j)]
    _ = c * ((rpow x k * q.val j) * rpow x j) := by rw [r_mul_comm (q.val j) (rpow x k)]
    _ = c * (rpow x k * (q.val j * rpow x j)) := by rw [r_mul_assoc (rpow x k)]
    _ = (c * rpow x k) * (q.val j * rpow x j) := by rw [← r_mul_assoc c]

theorem Poly.eval_trunc_mul : ∀ (B : Nat) (p q : Poly R) (x : R),
    Poly.eval (Poly.trunc B p * q) x = Poly.eval (Poly.trunc B p) x * Poly.eval q x
  | 0, p, q, x => by
    have hz : Poly.trunc 0 p = 0 := by
      apply Poly.ext
      intro d
      change (if d < 0 then p.val d else 0) = 0
      simp
    rw [hz, r_zero_mul, Poly.eval_zero, r_zero_mul]
  | k + 1, p, q, x => by
    have ht : Poly.trunc (k + 1) p = Poly.trunc k p + Poly.mono k (p.val k) :=
      Poly.trunc_succ k p
    rw [ht, r_right_distrib, Poly.eval_add, Poly.eval_add, r_right_distrib,
        Poly.eval_trunc_mul k p q x, Poly.eval_mono_mul]

theorem Poly.eval_mul (p q : Poly R) (x : R) :
    Poly.eval (p * q) x = Poly.eval p x * Poly.eval q x := by
  rcases p.property with ⟨Bp, hp⟩
  have heq := Poly.eq_trunc_of_bound hp
  conv => lhs; rw [heq]
  conv => rhs; arg 1; rw [heq]
  exact Poly.eval_trunc_mul Bp p q x

theorem Poly.eval_zero_eq_const (p : Poly R) : Poly.eval p 0 = p.val 0 := by
  rcases p.property with ⟨Bp, hp⟩
  have hp1 : ∀ d : Nat, Bp + 1 ≤ d → p.val d = 0 := fun d hd => hp d (by omega)
  rw [Poly.eval_eq_evalAt p hp1]
  unfold Poly.evalAt
  rw [finSum_succ_left Bp]
  have hz : finSum Bp (fun i => p.val (i + 1) * rpow (0 : R) (i + 1)) = 0 := by
    apply finSum_zero_fn
    intro i _
    rw [zero_rpow (by omega), r_mul_zero]
  rw [hz, r_add_zero]
  change p.val 0 * 1 = p.val 0
  exact r_mul_one _

/-- Decomposition `p = C (p(0)) + X * shift(p)` showing `p ∈ (X) ↔ p(0) = 0`. -/
def Poly.shift (p : Poly R) : Poly R :=
  ⟨fun d => p.val (d + 1), by
    rcases p.property with ⟨Bp, hp⟩
    exact ⟨Bp, fun d hd => hp (d + 1) (by omega)⟩⟩

theorem Poly.eq_C_add_X_mul_shift (p : Poly R) :
    p = Poly.C (p.val 0) + Poly.X * Poly.shift p := by
  apply Poly.ext
  intro d
  change p.val d = (Poly.C (p.val 0)).val d + (Poly.mul (Poly.mono 1 1) (Poly.shift p)).val d
  rw [Poly.mono_mul_coeff]
  cases d with
  | zero =>
    change p.val 0 = p.val 0 + 0
    exact (r_add_zero _).symm
  | succ k =>
    have h1 : 1 ≤ k + 1 := by omega
    have hsub : k + 1 - 1 = k := by omega
    have hne : k + 1 ≠ 0 := by omega
    change p.val (k + 1) =
      (if k + 1 = 0 then p.val 0 else 0) +
      (if 1 ≤ k + 1 then (1 : R) * p.val ((k + 1 - 1) + 1) else 0)
    simp [hne, h1, hsub, r_one_mul, r_zero_add]

theorem Poly.mem_span_X_iff (p : Poly R) :
    p ∈ Ideal.span [Poly.X] ↔ Poly.eval p 0 = 0 := by
  rw [Poly.eval_zero_eq_const]
  constructor
  · rintro ⟨q, y, hy, hp⟩
    change y = 0 at hy
    rw [hy, r_add_zero, r_mul_comm] at hp
    have h0 : p.val 0 = (Poly.mul (Poly.mono 1 1) q).val 0 := congrArg (fun z => z.val 0) hp
    rw [Poly.mono_mul_coeff] at h0
    exact h0
  · intro h0
    refine ⟨Poly.shift p, 0, rfl, ?_⟩
    rw [r_add_zero, r_mul_comm]
    have hdecomp := Poly.eq_C_add_X_mul_shift p
    rw [h0] at hdecomp
    have hc0 : (Poly.C (0 : R)) = 0 := by
      apply Poly.ext
      intro d
      change (if d = 0 then (0 : R) else 0) = 0
      by_cases hd : d = 0 <;> simp [hd]
    rw [hc0, r_zero_add] at hdecomp
    exact hdecomp

/-- Leading degree helper for `Poly R`. -/
noncomputable def degBound : Nat → (Nat → R) → Nat
  | 0, _ => 0
  | k + 1, f => if f k ≠ 0 then k else degBound k f

theorem degBound_spec : ∀ (B : Nat) (f : Nat → R),
    (∀ d : Nat, B ≤ d → f d = 0) → (∃ i : Nat, i < B ∧ f i ≠ 0) →
    f (degBound B f) ≠ 0 ∧ degBound B f < B ∧ (∀ d : Nat, degBound B f < d → f d = 0)
  | 0, _, _, ⟨_, hi, _⟩ => by omega
  | k + 1, f, hB, hex => by
    unfold degBound
    by_cases hfk : f k ≠ 0
    · rw [if_pos hfk]
      exact ⟨hfk, Nat.lt_succ_self k, fun d hd => hB d (by omega)⟩
    · rw [if_neg hfk]
      have hfk0 : f k = 0 := Classical.not_not.mp hfk
      rcases hex with ⟨i, hi, hfi⟩
      have hik : i < k := by
        by_cases heq : i = k
        · subst heq; exact False.elim (hfi hfk0)
        · omega
      have hB' : ∀ d : Nat, k ≤ d → f d = 0 := by
        intro d hd
        by_cases heq : d = k
        · subst heq; exact hfk0
        · exact hB d (by omega)
      rcases degBound_spec k f hB' ⟨i, hik, hfi⟩ with ⟨hne, hlt, hgt⟩
      exact ⟨hne, Nat.lt_succ_of_lt hlt, hgt⟩

noncomputable def Poly.natDeg (p : Poly R) : Nat :=
  degBound (Classical.choose p.property) p.val

theorem Poly.exists_lt_bound_of_ne_zero {B : Nat} {p : Poly R}
    (hp : ∀ d : Nat, B ≤ d → p.val d = 0) (hne : p ≠ 0) :
    ∃ i : Nat, i < B ∧ p.val i ≠ 0 :=
  Classical.byContradiction (fun hall => hne (by
    apply Poly.ext
    intro d
    by_cases hd : d < B
    · exact Classical.byContradiction (fun hdnz => hall ⟨d, hd, hdnz⟩)
    · exact hp d (by omega)))

theorem Poly.natDeg_spec {p : Poly R} (hne : p ≠ 0) :
    p.val p.natDeg ≠ 0 ∧ ∀ d : Nat, p.natDeg < d → p.val d = 0 := by
  let B := Classical.choose p.property
  have hp : ∀ d : Nat, B ≤ d → p.val d = 0 := Classical.choose_spec p.property
  have hex := Poly.exists_lt_bound_of_ne_zero hp hne
  rcases degBound_spec B p.val hp hex with ⟨h1, _, h3⟩
  exact ⟨h1, h3⟩

theorem Poly.natDeg_lt_of_bound {B : Nat} {p : Poly R}
    (hp : ∀ d : Nat, B ≤ d → p.val d = 0) (hne : p ≠ 0) :
    p.natDeg < B := by
  rcases Poly.natDeg_spec hne with ⟨hlead, _⟩
  exact Classical.byContradiction (fun hge => hlead (hp p.natDeg (by omega)))

theorem Poly.isDomain (hd : IsDomain R) : IsDomain (Poly R) where
  one_ne_zero := fun h => by
    have h0 : (1 : Poly R).val 0 = (0 : Poly R).val 0 := congrArg (fun z => z.val 0) h
    exact hd.one_ne_zero h0
  mul_eq_zero := by
    intro p q hpq
    by_cases hp : p = 0
    · exact Or.inl hp
    · by_cases hq : q = 0
      · exact Or.inr hq
      · rcases Poly.natDeg_spec hp with ⟨hlp, hgtp⟩
        rcases Poly.natDeg_spec hq with ⟨hlq, hgtq⟩
        let dp := p.natDeg
        let dq := q.natDeg
        have hcoeff : (p * q).val (dp + dq) = p.val dp * q.val dq := by
          change finSum (dp + dq + 1) (fun i => p.val i * q.val (dp + dq - i)) =
            p.val dp * q.val dq
          rw [finSum_single (dp + dq + 1) dp _ (by omega)]
          · have hsub : dp + dq - dp = dq := by omega
            rw [hsub]
          · intro i hi hne
            by_cases hgt : dp < i
            · rw [hgtp i hgt, r_zero_mul]
            · rw [hgtq (dp + dq - i) (by omega), r_mul_zero]
        have hz : (p * q).val (dp + dq) = 0 := by rw [hpq]; rfl
        rw [hcoeff] at hz
        cases hd.mul_eq_zero hz with
        | inl h1 => exact False.elim (hlp h1)
        | inr h2 => exact False.elim (hlq h2)

theorem Poly.natDeg_mul (hd : IsDomain R) {p q : Poly R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natDeg = p.natDeg + q.natDeg := by
  rcases Poly.natDeg_spec hp with ⟨hlp, hgtp⟩
  rcases Poly.natDeg_spec hq with ⟨hlq, hgtq⟩
  have hpq_ne : p * q ≠ 0 := fun h => by
    cases (Poly.isDomain hd).mul_eq_zero h with
    | inl h1 => exact hp h1
    | inr h2 => exact hq h2
  rcases Poly.natDeg_spec hpq_ne with ⟨hlpq, hgtpq⟩
  let dp := p.natDeg
  let dq := q.natDeg
  have hlead : (p * q).val (dp + dq) ≠ 0 := by
    have hcoeff : (p * q).val (dp + dq) = p.val dp * q.val dq := by
      change finSum (dp + dq + 1) (fun i => p.val i * q.val (dp + dq - i)) =
        p.val dp * q.val dq
      rw [finSum_single (dp + dq + 1) dp _ (by omega)]
      · have hsub : dp + dq - dp = dq := by omega
        rw [hsub]
      · intro i _ hne
        by_cases hgt : dp < i
        · rw [hgtp i hgt, r_zero_mul]
        · rw [hgtq (dp + dq - i) (by omega), r_mul_zero]
    rw [hcoeff]
    intro hz
    cases hd.mul_eq_zero hz with
    | inl h1 => exact hlp h1
    | inr h2 => exact hlq h2
  have habove : ∀ d : Nat, dp + dq < d → (p * q).val d = 0 := by
    intro d hd_gt
    change finSum (d + 1) (fun i => p.val i * q.val (d - i)) = 0
    apply finSum_zero_fn
    intro i _
    by_cases hgt : dp < i
    · rw [hgtp i hgt, r_zero_mul]
    · rw [hgtq (d - i) (by omega), r_mul_zero]
  by_cases hlt : (p * q).natDeg < dp + dq
  · exact False.elim (hlead (hgtpq (dp + dq) hlt))
  · by_cases hgt : dp + dq < (p * q).natDeg
    · exact False.elim (hlpq (habove (p * q).natDeg hgt))
    · omega

end PolyOps

section PolyPID
variable {K : Type u} [CAlgField K]

/-- Euclidean division with remainder in `K[X]` over any field `K`. -/
theorem Poly.div_mod_by_bound {g : Poly K} (hg : g ≠ 0) :
    ∀ (B : Nat) (f : Poly K), (∀ d : Nat, B ≤ d → f.val d = 0) →
      ∃ q r : Poly K, f = q * g + r ∧ (r = 0 ∨ r.natDeg < g.natDeg)
  | B, f, hfB => by
    by_cases hf0 : f = 0
    · exact ⟨0, 0, by rw [hf0, r_zero_mul, r_add_zero], Or.inl rfl⟩
    · let df := f.natDeg
      let dg := g.natDeg
      have hdfB : df < B := Poly.natDeg_lt_of_bound hfB hf0
      by_cases hlt : df < dg
      · exact ⟨0, f, by rw [r_zero_mul, r_zero_add], Or.inr hlt⟩
      · have hle : dg ≤ df := by omega
        rcases Poly.natDeg_spec hf0 with ⟨hlf, hgtf⟩
        rcases Poly.natDeg_spec hg with ⟨hlg, hgtg⟩
        let k := df - dg
        let c := f.val df * CAlgField.inv (g.val dg)
        let step := Poly.mono k c * g
        let f' := f - step
        have hf'B : ∀ d : Nat, df ≤ d → f'.val d = 0 := by
          intro d hd
          change f.val d + (-(Poly.mul (Poly.mono k c) g).val d) = 0
          rw [Poly.mono_mul_coeff]
          by_cases hd_eq : d = df
          · subst hd_eq
            have hk : k ≤ df := by omega
            have hsub : df - k = dg := by omega
            simp [hk, hsub]
            have hprod : c * g.val dg = f.val df := by
              have hinv_eq : g.val dg * CAlgField.inv (g.val dg) = 1 :=
                CAlgField.mul_inv_cancel (g.val dg) hlg
              change (f.val df * CAlgField.inv (g.val dg)) * g.val dg = f.val df
              rw [r_mul_assoc, r_mul_comm (CAlgField.inv (g.val dg)) (g.val dg),
                  hinv_eq, r_mul_one]
            rw [hprod, r_add_right_neg]
          · have hgt : df < d := by omega
            have hk : k ≤ d := by omega
            have hsub_gt : dg < d - k := by omega
            rw [hgtf d hgt]
            simp [hk, hgtg (d - k) hsub_gt, r_mul_zero, r_neg_zero, r_add_zero]
        rcases Poly.div_mod_by_bound hg df f' hf'B with ⟨q', r, hf'eq, hr⟩
        refine ⟨Poly.mono k c + q', r, ?_, hr⟩
        rw [r_right_distrib]
        calc
          f = step + f' := by
            change f = step + (f + (-step))
            rw [r_add_comm f (-step), ← r_add_assoc, r_add_right_neg, r_zero_add]
          _ = step + (q' * g + r) := by rw [hf'eq]
          _ = (step + q' * g) + r := by rw [← r_add_assoc]
termination_by B => B

theorem Poly.div_mod (f : Poly K) {g : Poly K} (hg : g ≠ 0) :
    ∃ q r : Poly K, f = q * g + r ∧ (r = 0 ∨ r.natDeg < g.natDeg) :=
  Poly.div_mod_by_bound hg (Classical.choose f.property) f (Classical.choose_spec f.property)

/-- Well-foundedness helper: find a nonzero polynomial of minimum degree in a nonzero ideal. -/
theorem exists_min_natDeg {P : Poly K → Prop} (hex : ∃ f : Poly K, P f ∧ f ≠ 0) :
    ∃ g : Poly K, P g ∧ g ≠ 0 ∧ ∀ h : Poly K, P h → h ≠ 0 → g.natDeg ≤ h.natDeg := by
  let Q : Nat → Prop := fun d => ∃ f : Poly K, P f ∧ f ≠ 0 ∧ f.natDeg = d
  rcases hex with ⟨f0, hf0P, hf0ne⟩
  have hQ : ∀ d : Nat, Q d →
      ∃ m : Nat, Q m ∧ ∀ k : Nat, k < m → ¬ Q k := by
    intro d
    induction d using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hmin : ∀ k : Nat, k < n → ¬ Q k
      · exact ⟨n, hn, hmin⟩
      · have hexk : ∃ k : Nat, k < n ∧ Q k :=
          Classical.byContradiction (fun hno => hmin (fun k hk hQk => hno ⟨k, hk, hQk⟩))
        rcases hexk with ⟨k, hk, hQk⟩
        exact ih k hk hQk
  rcases hQ f0.natDeg ⟨f0, hf0P, hf0ne, rfl⟩ with ⟨m, ⟨g, hgP, hgne, hdeg⟩, hmin⟩
  refine ⟨g, hgP, hgne, fun h hhP hhne => ?_⟩
  rw [hdeg]
  exact Classical.byContradiction (fun hgt => hmin h.natDeg (by omega) ⟨h, hhP, hhne, rfl⟩)

/-- `K[X]` over a field `K` is a Principal Ideal Domain: every ideal is generated by one element. -/
theorem Poly.isPID (I : Ideal (Poly K)) :
    ∃ g : Poly K, (∀ x : Poly K, x ∈ I ↔ x ∈ Ideal.span [g]) := by
  by_cases hzero : ∀ f : Poly K, f ∈ I → f = 0
  · refine ⟨0, fun x => ?_⟩
    constructor
    · intro hx
      refine ⟨0, 0, rfl, ?_⟩
      rw [hzero x hx, r_zero_mul, r_add_zero]
    · rintro ⟨r, y, hy, hx⟩
      change y = 0 at hy
      rw [hx, hy, r_mul_zero, r_add_zero]
      exact I.zero_mem
  · have hex : ∃ f : Poly K, f ∈ I ∧ f ≠ 0 :=
      Classical.byContradiction (fun hno =>
        hzero (fun f hf => Classical.byContradiction (fun hfne => hno ⟨f, hf, hfne⟩)))
    rcases exists_min_natDeg hex with ⟨g, hgI, hgne, hmin⟩
    refine ⟨g, fun x => ?_⟩
    constructor
    · intro hxI
      rcases Poly.div_mod x hgne with ⟨q, r, hxeq, hr⟩
      have hrI : r ∈ I := by
        have hqg : q * g ∈ I := I.mul_mem_left q hgI
        have hsub : x - q * g ∈ I := I.sub_mem hxI hqg
        have hr_eq : x - q * g = r := by
          rw [hxeq]
          change (q * g + r) + (-(q * g)) = r
          rw [r_add_comm (q * g) r, r_add_assoc, r_add_right_neg, r_add_zero]
        rw [← hr_eq]
        exact hsub
      cases hr with
      | inl hr0 =>
        rw [hr0, r_add_zero] at hxeq
        exact ⟨q, 0, rfl, by rw [r_add_zero]; exact hxeq⟩
      | inr hdeg =>
        by_cases hrne : r = 0
        · rw [hrne, r_add_zero] at hxeq
          exact ⟨q, 0, rfl, by rw [r_add_zero]; exact hxeq⟩
        · exact False.elim (by
            have hle := hmin r hrI hrne
            omega)
    · rintro ⟨q, y, hy, hx⟩
      change y = 0 at hy
      rw [hx, hy, r_add_zero]
      exact I.mul_mem_left q hgI

theorem Poly.unit_natDeg_eq_zero {u v : Poly K} (huv : u * v = 1) : u.natDeg = 0 := by
  have hd := Poly.isDomain (CAlgField.isDomain K)
  have hu : u ≠ 0 := fun h => by rw [h, r_zero_mul] at huv; exact hd.one_ne_zero huv.symm
  have hv : v ≠ 0 := fun h => by rw [h, r_mul_zero] at huv; exact hd.one_ne_zero huv.symm
  have hdeg := Poly.natDeg_mul (CAlgField.isDomain K) hu hv
  rw [huv] at hdeg
  have h1deg : (1 : Poly K).natDeg = 0 := by
    have h1b : (1 : Poly K).natDeg < 1 :=
      Poly.natDeg_lt_of_bound (B := 1) (fun d hd => by
        change (if d = 0 then (1 : K) else 0) = 0
        have hne : d ≠ 0 := by omega
        simp [hne]) hd.one_ne_zero
    omega
  rw [h1deg] at hdeg
  omega

theorem Poly.eq_C_of_natDeg_zero {u : Poly K} (hdeg : u.natDeg = 0) :
    u = Poly.C (u.val 0) := by
  by_cases hu : u = 0
  · subst hu
    apply Poly.ext
    intro d
    change (0 : K) = if d = 0 then 0 else 0
    by_cases hd : d = 0 <;> simp [hd]
  · rcases Poly.natDeg_spec hu with ⟨_, hgt⟩
    apply Poly.ext
    intro d
    change u.val d = if d = 0 then u.val 0 else 0
    by_cases hd : d = 0
    · simp [hd]
    · rw [hgt d (by omega)]
      simp [hd]

/-- Krull dimension of `K[X]` is at most `1`: there is no strict chain `p0 ⊂ p1 ⊂ p2`
of three prime ideals in `K[X]`. -/
theorem Poly.no_prime_chain_len_two {p0 p1 p2 : Ideal (Poly K)}
    (hp1 : Ideal.IsPrime p1) (hp2 : Ideal.IsPrime p2)
    (h01 : Ideal.StrictSubset p0 p1) (h12 : Ideal.StrictSubset p1 p2) : False := by
  have hdom := Poly.isDomain (CAlgField.isDomain K)
  rcases Poly.isPID p1 with ⟨g1, hg1⟩
  rcases Poly.isPID p2 with ⟨g2, hg2⟩
  -- `g1 ≠ 0` because `p0 ⊂ p1` implies `p1` contains a nonzero element
  have hg1_ne : g1 ≠ 0 := by
    intro hg10
    rcases h01 with ⟨_, y, hy1, hy0⟩
    rcases (hg1 y).mp hy1 with ⟨q, z, hz, hy⟩
    change z = 0 at hz
    rw [hy, hz, hg10, r_mul_zero, r_add_zero] at hy0
    exact hy0 p0.zero_mem
  have hg2_ne : g2 ≠ 0 := by
    intro hg20
    have hg1_in_p2 : g1 ∈ p2 := h12.1 g1 ((hg1 g1).mpr ⟨1, 0, rfl, by rw [r_one_mul, r_add_zero]⟩)
    rcases (hg2 g1).mp hg1_in_p2 with ⟨q, z, hz, hg1eq⟩
    change z = 0 at hz
    rw [hg1eq, hz, hg20, r_mul_zero, r_add_zero] at hg1_ne
    exact hg1_ne rfl
  -- Since `g1 ∈ p1 ⊆ p2 = (g2)`, write `g1 = q * g2`.
  have hg1_in_p1 : g1 ∈ p1 := (hg1 g1).mpr ⟨1, 0, rfl, by rw [r_one_mul, r_add_zero]⟩
  rcases (hg2 g1).mp (h12.1 g1 hg1_in_p1) with ⟨q, z, hz, hg1eq⟩
  change z = 0 at hz
  rw [hz, r_add_zero] at hg1eq
  -- Since `p1` is prime and `q * g2 = g1 ∈ p1`, either `q ∈ p1` or `g2 ∈ p1`.
  have hprod_in_p1 : q * g2 ∈ p1 := by rw [← hg1eq]; exact hg1_in_p1
  cases hp1.2 q g2 hprod_in_p1 with
  | inr hg2_in_p1 =>
    -- If `g2 ∈ p1`, then `p2 = (g2) ⊆ p1`, contradicting `p1 ⊂ p2`!
    rcases h12 with ⟨_, w, hw2, hw1⟩
    rcases (hg2 w).mp hw2 with ⟨r, z2, hz2, hweq⟩
    change z2 = 0 at hz2
    rw [hweq, hz2, r_add_zero] at hw1
    exact hw1 (p1.mul_mem_left r hg2_in_p1)
  | inl hq_in_p1 =>
    -- If `q ∈ p1 = (g1)`, write `q = s * g1`, so `g1 = s * g1 * g2`, hence `s * g2 = 1`!
    rcases (hg1 q).mp hq_in_p1 with ⟨s, z3, hz3, hqeq⟩
    change z3 = 0 at hz3
    rw [hz3, r_add_zero] at hqeq
    have hunit : g1 * (s * g2) = g1 * 1 := by
      calc
        g1 * (s * g2) = (s * g1) * g2 := by
          rw [r_mul_comm s g1, r_mul_assoc]
        _ = g1 := by rw [← hqeq, ← hg1eq]
        _ = g1 * 1 := (r_mul_one g1).symm
    have hsg2 : s * g2 = 1 := IsDomain.mul_left_cancel hdom hg1_ne hunit
    exact hp2.1 ((hg2 1).mpr ⟨s, 0, rfl, by rw [r_add_zero, hsg2]⟩)

end PolyPID

/-- Canonical list `[0, 1, ..., n-1]` of elements of `Fin n`. -/
def finRangeList : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finRangeList n).map Fin.succ

theorem mem_finRangeList : ∀ {n : Nat} (i : Fin n), i ∈ finRangeList n
  | 0, i => Fin.elim0 i
  | _ + 1, ⟨0, _⟩ => List.Mem.head _
  | _ + 1, ⟨k + 1, hk⟩ =>
    List.mem_cons_of_mem _
      (List.mem_map_of_mem (f := Fin.succ)
        (mem_finRangeList ⟨k, Nat.lt_of_succ_lt_succ hk⟩))

/-- Bundled iterated polynomial ring `(MPoly n K, CAlgRing (MPoly n K))`. -/
@[reducible] def MPolyPkg : Nat → (K : Type u) → [CAlgRing K] → Σ R : Type u, CAlgRing R
  | 0, K, inst => ⟨K, inst⟩
  | n + 1, K, _ =>
    let prev := MPolyPkg n K
    letI : CAlgRing prev.1 := prev.2
    ⟨Poly prev.1, inferInstance⟩

/-- Iterated multivariate polynomial ring `MPoly n K ≅ K[X_0, ..., X_{n-1}]`. -/
abbrev MPoly (n : Nat) (K : Type u) [CAlgRing K] : Type u :=
  (MPolyPkg n K).1

instance MPoly.instRing (n : Nat) (K : Type u) [CAlgRing K] : CAlgRing (MPoly n K) :=
  (MPolyPkg n K).2

theorem MPoly.isDomain (n : Nat) {K : Type u} [CAlgRing K] (hd : IsDomain K) :
    IsDomain (MPoly n K) := by
  induction n with
  | zero => exact hd
  | succ k ih => exact Poly.isDomain ih

/-- Embedding of `MPoly n K` as constants in `MPoly (n + 1) K = (MPoly n K)[X_n]`. -/
def MPoly.liftConst {n : Nat} {K : Type u} [CAlgRing K] (f : MPoly n K) : MPoly (n + 1) K :=
  Poly.C f

/-- Coordinate variable `X_i` in `MPoly n K`. -/
def MPoly.var : {n : Nat} → {K : Type u} → [CAlgRing K] → Fin n → MPoly n K
  | 0, _, _, i => Fin.elim0 i
  | n + 1, K, _, ⟨0, _⟩ =>
    if _ : n = 0 then Poly.X
    else MPoly.liftConst (MPoly.var (n := n) (K := K) ⟨0, by omega⟩)
  | n + 1, K, _, ⟨j + 1, hj⟩ =>
    if _ : j + 1 = n then Poly.X
    else MPoly.liftConst (MPoly.var (n := n) (K := K) ⟨j + 1, by omega⟩)

/-- Evaluation of `f ∈ MPoly n K` at the origin `(0, ..., 0) ∈ K^n`. -/
noncomputable def MPoly.evalOrigin : {n : Nat} → {K : Type u} → [CAlgRing K] → MPoly n K → K
  | 0, _, _, c => c
  | n + 1, _, _, p => MPoly.evalOrigin (n := n) (Poly.eval p 0)

theorem MPoly.evalOrigin_zero {n : Nat} {K : Type u} [CAlgRing K] :
    MPoly.evalOrigin (0 : MPoly n K) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change MPoly.evalOrigin (Poly.eval (0 : Poly (MPoly k K)) 0) = 0
    rw [Poly.eval_zero]
    exact ih

theorem MPoly.evalOrigin_one {n : Nat} {K : Type u} [CAlgRing K] :
    MPoly.evalOrigin (1 : MPoly n K) = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change MPoly.evalOrigin (Poly.eval (1 : Poly (MPoly k K)) 0) = 1
    rw [Poly.eval_one]
    exact ih

theorem MPoly.evalOrigin_add {n : Nat} {K : Type u} [CAlgRing K] (f g : MPoly n K) :
    MPoly.evalOrigin (f + g) = MPoly.evalOrigin f + MPoly.evalOrigin g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change MPoly.evalOrigin (Poly.eval (R := MPoly k K) (f + g) 0) = _
    rw [Poly.eval_add]
    exact ih _ _

theorem MPoly.evalOrigin_mul {n : Nat} {K : Type u} [CAlgRing K] (f g : MPoly n K) :
    MPoly.evalOrigin (f * g) = MPoly.evalOrigin f * MPoly.evalOrigin g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change MPoly.evalOrigin (Poly.eval (R := MPoly k K) (f * g) 0) = _
    rw [Poly.eval_mul]
    exact ih _ _

theorem MPoly.evalOrigin_liftConst {n : Nat} {K : Type u} [CAlgRing K] (f : MPoly n K) :
    MPoly.evalOrigin (MPoly.liftConst f) = MPoly.evalOrigin f := by
  change MPoly.evalOrigin (Poly.eval (R := MPoly n K) (Poly.C f) 0) = MPoly.evalOrigin f
  rw [Poly.eval_C]

theorem MPoly.evalOrigin_var {n : Nat} {K : Type u} [CAlgRing K] (i : Fin n) :
    MPoly.evalOrigin (MPoly.var (K := K) i) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rcases i with ⟨j, hj⟩
    cases j with
    | zero =>
      unfold MPoly.var
      by_cases hk : k = 0
      · subst hk
        simp
        change Poly.eval (Poly.X : Poly K) 0 = 0
        exact Poly.eval_X 0
      · simp [hk]
        rw [MPoly.evalOrigin_liftConst]
        exact ih ⟨0, by omega⟩
    | succ m =>
      unfold MPoly.var
      by_cases hm : m + 1 = k
      · simp [hm]
        change MPoly.evalOrigin (Poly.eval (Poly.X : Poly (MPoly k K)) 0) = 0
        rw [Poly.eval_X]
        exact MPoly.evalOrigin_zero
      · simp [hm]
        rw [MPoly.evalOrigin_liftConst]
        exact ih ⟨m + 1, by omega⟩

/-- List of all coordinate variables `[X_0, ..., X_{n-1}]` in `MPoly n K`. -/
def MPoly.varsList (n : Nat) (K : Type u) [CAlgRing K] : List (MPoly n K) :=
  (finRangeList n).map (fun i => MPoly.var (K := K) i)

/-- The homogeneous maximal ideal `𝔪 = (X_0, ..., X_{n-1}) ⊆ MPoly n K`. -/
def MPoly.maxIdeal (n : Nat) (K : Type u) [CAlgRing K] : Ideal (MPoly n K) :=
  Ideal.span (MPoly.varsList n K)

theorem MPoly.var_mem_maxIdeal {n : Nat} {K : Type u} [CAlgRing K] (i : Fin n) :
    MPoly.var (K := K) i ∈ MPoly.maxIdeal n K := by
  apply Ideal.mem_span_of_mem
  unfold MPoly.varsList
  exact List.mem_map_of_mem (mem_finRangeList i)

theorem MPoly.evalOrigin_eq_zero_of_mem_maxIdeal {n : Nat} {K : Type u} [CAlgRing K]
    {f : MPoly n K} (hf : f ∈ MPoly.maxIdeal n K) : MPoly.evalOrigin f = 0 := by
  let zeroOrigin : Ideal (MPoly n K) := {
    carrier := fun g => MPoly.evalOrigin g = 0
    zero_mem := MPoly.evalOrigin_zero
    add_mem := fun {a b} ha hb => by rw [MPoly.evalOrigin_add, ha, hb, r_add_zero]
    mul_mem_left := fun r {a} ha => by rw [MPoly.evalOrigin_mul, ha, r_mul_zero]
  }
  apply Ideal.span_le (I := zeroOrigin) _ hf
  intro g hg
  unfold MPoly.varsList at hg
  rcases List.mem_map.mp hg with ⟨i, _, rfl⟩
  exact MPoly.evalOrigin_var i

end Conjecture00000000505
