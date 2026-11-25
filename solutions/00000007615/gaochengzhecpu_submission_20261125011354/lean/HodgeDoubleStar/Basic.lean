/-
  HodgeDoubleStar/Basic.lean
  Combinatorial foundations for exterior algebras and pseudo-Riemannian signatures
  on Fin n -> Bool bitmasks in core Lean 4 (zero external dependencies).
-/

namespace HodgeDoubleStar

/-- A subset of `{0, ..., n - 1}` represented as a Boolean indicator mask on `Fin n`. -/
abbrev Mask (n : Nat) : Type := Fin n → Bool

/-- Empty subset mask (`∅`). -/
def emptyMask (n : Nat) : Mask n := fun _ => false

/-- Full subset mask (`{0, ..., n - 1}`). -/
def fullMask (n : Nat) : Mask n := fun _ => true

/-- Prepend a Boolean at index `0` to a mask on `Fin n`, yielding a mask on `Fin (n + 1)`. -/
def consMask {n : Nat} (b : Bool) (I : Mask n) : Mask (n + 1) :=
  Fin.cases b I

/-- Value of a mask on `Fin (n + 1)` at index `0`. -/
def headMask {n : Nat} (I : Mask (n + 1)) : Bool :=
  I ⟨0, Nat.zero_lt_succ n⟩

/-- Restriction of a mask on `Fin (n + 1)` to indices `1, ..., n`. -/
def tailMask {n : Nat} (I : Mask (n + 1)) : Mask n :=
  fun i => I i.succ

@[simp] theorem headMask_consMask {n : Nat} (b : Bool) (I : Mask n) :
    headMask (consMask b I) = b := rfl

@[simp] theorem tailMask_consMask {n : Nat} (b : Bool) (I : Mask n) :
    tailMask (consMask b I) = I := by
  funext i
  simp [tailMask, consMask]

@[simp] theorem consMask_eta {n : Nat} (I : Mask (n + 1)) :
    consMask (headMask I) (tailMask I) = I := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro _
    rfl

theorem mask_zero_eq (I J : Mask 0) : I = J := by
  funext i
  exact Fin.elim0 i

/-- Boolean equality test on masks. -/
def maskEq : {n : Nat} → Mask n → Mask n → Bool
  | 0, _, _ => true
  | _ + 1, I, J => (headMask I == headMask J) && maskEq (tailMask I) (tailMask J)

theorem maskEq_iff {n : Nat} (I J : Mask n) : maskEq I J = true ↔ I = J := by
  induction n with
  | zero =>
    simp [maskEq, mask_zero_eq I J]
  | succ n ih =>
    simp only [maskEq, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hhead, htail⟩
      rw [← consMask_eta I, ← consMask_eta J, hhead, htail]
    · intro h
      subst h
      exact ⟨rfl, rfl⟩

instance instDecidableEqMask {n : Nat} : DecidableEq (Mask n) := fun I J =>
  if h : maskEq I J = true then
    isTrue ((maskEq_iff I J).mp h)
  else
    isFalse (fun heq => h ((maskEq_iff I J).mpr heq))

/-- Pointwise complement `I^c = {0, ..., n - 1} \ I`. -/
def compMask {n : Nat} (I : Mask n) : Mask n :=
  fun i => !(I i)

/-- Pointwise union `I ∪ J`. -/
def orMask {n : Nat} (I J : Mask n) : Mask n :=
  fun i => I i || J i

/-- Pointwise intersection `I ∩ J`. -/
def andMask {n : Nat} (I J : Mask n) : Mask n :=
  fun i => I i && J i

/-- Disjointness test `I ∩ J = ∅`. -/
def disjointMask : {n : Nat} → Mask n → Mask n → Bool
  | 0, _, _ => true
  | _ + 1, I, J => !(headMask I && headMask J) && disjointMask (tailMask I) (tailMask J)

theorem disjointMask_iff {n : Nat} (I J : Mask n) :
    disjointMask I J = true ↔ ∀ i : Fin n, (I i && J i) = false := by
  induction n with
  | zero =>
    simp only [disjointMask]
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      trivial
  | succ n ih =>
    simp only [disjointMask, Bool.and_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨h0, htail⟩ i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · intro j
        exact htail j
    · intro hall
      exact ⟨hall ⟨0, Nat.zero_lt_succ n⟩, fun j => hall j.succ⟩

@[simp] theorem compMask_compMask {n : Nat} (I : Mask n) :
    compMask (compMask I) = I := by
  funext i
  simp [compMask]

@[simp] theorem headMask_compMask {n : Nat} (I : Mask (n + 1)) :
    headMask (compMask I) = !(headMask I) := rfl

@[simp] theorem tailMask_compMask {n : Nat} (I : Mask (n + 1)) :
    tailMask (compMask I) = compMask (tailMask I) := rfl

@[simp] theorem compMask_consMask {n : Nat} (b : Bool) (I : Mask n) :
    compMask (consMask b I) = consMask (!b) (compMask I) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [compMask, consMask]
  · intro j
    simp [compMask, consMask]

theorem compMask_ne_self {n : Nat} (hn : 1 ≤ n) (I : Mask n) : compMask I ≠ I := by
  intro h
  have h0 := congrFun h ⟨0, hn⟩
  simp only [compMask] at h0
  cases hh : I ⟨0, hn⟩ <;> rw [hh] at h0 <;> cases h0

theorem disjointMask_comp_right {n : Nat} (I : Mask n) :
    disjointMask I (compMask I) = true := by
  rw [disjointMask_iff]
  intro i
  cases h : I i <;> simp [compMask, h]

theorem orMask_comp_right {n : Nat} (I : Mask n) :
    orMask I (compMask I) = fullMask n := by
  funext i
  cases h : I i <;> simp [orMask, compMask, fullMask, h]

theorem disjoint_or_full_iff {n : Nat} (I J : Mask n) :
    (disjointMask I J = true ∧ orMask I J = fullMask n) ↔ J = compMask I := by
  constructor
  · rintro ⟨hdisj, hor⟩
    rw [disjointMask_iff] at hdisj
    funext i
    have hd := hdisj i
    have ho := congrFun hor i
    simp only [orMask, fullMask] at ho
    cases hi : I i <;> cases hj : J i <;> simp [compMask, hi, hj] at hd ho ⊢
  · intro hJ
    subst hJ
    exact ⟨disjointMask_comp_right I, orMask_comp_right I⟩

/-- Helper converting a Boolean to `0` or `1`. -/
def b2n (b : Bool) : Nat :=
  match b with
  | false => 0
  | true => 1

@[simp] theorem b2n_false : b2n false = 0 := rfl
@[simp] theorem b2n_true : b2n true = 1 := rfl

theorem b2n_le_one (b : Bool) : b2n b ≤ 1 := by
  cases b <;> decide

theorem b2n_add_b2n_not (b : Bool) : b2n b + b2n (!b) = 1 := by
  cases b <;> rfl

/-- Cardinality `|I|` (degree) of a mask `I : Mask n`. -/
def degMask : {n : Nat} → Mask n → Nat
  | 0, _ => 0
  | _ + 1, I => b2n (headMask I) + degMask (tailMask I)

@[simp] theorem degMask_consMask {n : Nat} (b : Bool) (I : Mask n) :
    degMask (consMask b I) = b2n b + degMask I := by
  simp [degMask]

@[simp] theorem degMask_empty (n : Nat) : degMask (emptyMask n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hhead : headMask (emptyMask (n + 1)) = false := rfl
    have htail : tailMask (emptyMask (n + 1)) = emptyMask n := rfl
    simp [degMask, hhead, htail, ih]

@[simp] theorem degMask_full (n : Nat) : degMask (fullMask n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hhead : headMask (fullMask (n + 1)) = true := rfl
    have htail : tailMask (fullMask (n + 1)) = fullMask n := rfl
    simp only [degMask, hhead, htail, b2n_true, ih]
    omega

theorem degMask_le {n : Nat} (I : Mask n) : degMask I ≤ n := by
  induction n with
  | zero => simp [degMask]
  | succ n ih =>
    simp only [degMask]
    have h1 := b2n_le_one (headMask I)
    have h2 := ih (tailMask I)
    omega

theorem degMask_eq_n_iff_full {n : Nat} (I : Mask n) :
    degMask I = n ↔ I = fullMask n := by
  induction n with
  | zero =>
    simp [degMask, mask_zero_eq I (fullMask 0)]
  | succ n ih =>
    constructor
    · intro hdeg
      simp only [degMask] at hdeg
      have hle := degMask_le (tailMask I)
      cases hh : headMask I
      · rw [hh, b2n_false] at hdeg
        omega
      · rw [hh, b2n_true] at hdeg
        have htail_deg : degMask (tailMask I) = n := by omega
        have htail := (ih (tailMask I)).mp htail_deg
        rw [← consMask_eta I, hh, htail]
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro _
          rfl
    · intro hfull
      subst hfull
      exact degMask_full (n + 1)

/-- Partition of ambient dimension: `|I| + |I^c| = n`. -/
theorem degMask_add_degMask_comp {n : Nat} (I : Mask n) :
    degMask I + degMask (compMask I) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [degMask, headMask_compMask, tailMask_compMask]
    have hb := b2n_add_b2n_not (headMask I)
    have ht := ih (tailMask I)
    omega

theorem degMask_comp {n : Nat} (I : Mask n) :
    degMask (compMask I) = n - degMask I := by
  have h := degMask_add_degMask_comp I
  omega

theorem degMask_or_of_disjoint {n : Nat} (I J : Mask n) (hd : disjointMask I J = true) :
    degMask (orMask I J) = degMask I + degMask J := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [disjointMask, Bool.and_eq_true, Bool.not_eq_true'] at hd
    rcases hd with ⟨h0, htail⟩
    have hrec := ih (tailMask I) (tailMask J) htail
    have hor_tail : tailMask (orMask I J) = orMask (tailMask I) (tailMask J) := rfl
    have hor_head : headMask (orMask I J) = (headMask I || headMask J) := rfl
    simp only [degMask, hor_head, hor_tail, hrec]
    cases hhI : headMask I <;> cases hhJ : headMask J
    · simp
    · simp; omega
    · simp; omega
    · rw [hhI, hhJ] at h0; cases h0

/-- Existence of a subset mask of every valid degree `0 ≤ p ≤ n`. -/
theorem exists_mask_of_deg (n p : Nat) (hp : p ≤ n) : ∃ I : Mask n, degMask I = p := by
  induction n generalizing p with
  | zero =>
    have hp0 : p = 0 := by omega
    subst hp0
    exact ⟨emptyMask 0, rfl⟩
  | succ n ih =>
    cases p with
    | zero =>
      exact ⟨emptyMask (n + 1), degMask_empty (n + 1)⟩
    | succ p' =>
      obtain ⟨I', hI'⟩ := ih p' (by omega)
      refine ⟨consMask true I', ?_⟩
      simp only [degMask_consMask, b2n_true, hI']
      omega

/--
  Inversion count `inv(I, J) = |{(i, j) ∈ Fin n × Fin n : j < i ∧ I i = true ∧ J j = true}|`,
  measuring the number of transpositions needed to shuffle `(I, J)` into increasing order.
-/
def invCount : {n : Nat} → Mask n → Mask n → Nat
  | 0, _, _ => 0
  | _ + 1, I, J =>
      b2n (headMask J) * degMask (tailMask I) + invCount (tailMask I) (tailMask J)

@[simp] theorem invCount_consMask {n : Nat} (a b : Bool) (I J : Mask n) :
    invCount (consMask a I) (consMask b J) =
      b2n b * degMask I + invCount I J := by
  simp [invCount]

/-- Ordered list `[0, 1, ..., n - 1]` of all elements of `Fin n`. -/
def finList : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finList n).map Fin.succ

theorem degMask_eq_countP {n : Nat} (I : Mask n) :
    degMask I = (finList n).countP I := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [degMask, finList, List.countP_cons, List.countP_map]
    have hcomp : (I ∘ Fin.succ) = tailMask I := rfl
    rw [hcomp, ← ih (tailMask I)]
    cases hh : headMask I
    · simp [headMask] at hh
      simp [hh]
    · simp [headMask] at hh
      simp [hh]
      omega

/-- Explicit pair-counting characterization of `invCount`:
    `invCount I J` equals the exact count of pairs `(i, j)` with `j < i`, `I i = true`, `J j = true`. -/
theorem invCount_eq_pairCount {n : Nat} (I J : Mask n) :
    invCount I J =
      ((finList n).map (fun j =>
        (finList n).countP (fun i => decide (j.val < i.val) && I i && J j))).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [invCount, finList, List.map_cons, List.sum_cons, List.map_map]
    have hfirst :
        (⟨0, Nat.zero_lt_succ n⟩ :: List.map Fin.succ (finList n)).countP
          (fun i => decide (0 < i.val) && I i && J ⟨0, Nat.zero_lt_succ n⟩) =
        b2n (headMask J) * degMask (tailMask I) := by
      rw [List.countP_cons, List.countP_map]
      have h0 : (decide (0 < (0 : Nat)) && I ⟨0, Nat.zero_lt_succ n⟩ && J ⟨0, Nat.zero_lt_succ n⟩) = false := rfl
      rw [h0]
      cases hJ0 : headMask J
      · have hJ0' : J 0 = false := hJ0
        simp [hJ0']
      · have hJ0' : J 0 = true := hJ0
        simp only [b2n_true, Nat.one_mul, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [degMask_eq_countP (tailMask I)]
        congr 1
        funext k
        simp [Function.comp, tailMask, Fin.succ, hJ0']
    have hrest :
        List.map
          ((fun j : Fin (n + 1) =>
              (⟨0, Nat.zero_lt_succ n⟩ :: List.map Fin.succ (finList n)).countP
                (fun i => decide (j.val < i.val) && I i && J j)) ∘ Fin.succ)
          (finList n) =
        List.map
          (fun j : Fin n =>
            (finList n).countP (fun i => decide (j.val < i.val) && tailMask I i && tailMask J j))
          (finList n) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, List.countP_cons, List.countP_map]
      have h0false : (decide ((j.succ).val < 0) && I ⟨0, Nat.zero_lt_succ n⟩ && J j.succ) = false := by
        simp
      rw [h0false]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      congr 1
      funext i
      simp [Function.comp, tailMask, Fin.succ]
    rw [hfirst, hrest, ← ih (tailMask I) (tailMask J)]

/--
  **Fundamental Shuffle Partition Identity:**
  For any subset `I ⊆ {0, ..., n - 1}` and its complement `I^c`, every pair in `I × I^c`
  has either `i > j` (counted by `inv(I, I^c)`) or `j > i` (counted by `inv(I^c, I)`):
  `inv(I, I^c) + inv(I^c, I) = |I| * |I^c|`.
-/
theorem invCount_add_invCount_comp {n : Nat} (I : Mask n) :
    invCount I (compMask I) + invCount (compMask I) I = degMask I * degMask (compMask I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [invCount, degMask, headMask_compMask, tailMask_compMask]
    have h := ih (tailMask I)
    cases hh : headMask I
    · simp only [Bool.not_false, b2n_true, b2n_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add]
      calc
        degMask (tailMask I) + invCount (tailMask I) (compMask (tailMask I)) +
            invCount (compMask (tailMask I)) (tailMask I)
          = degMask (tailMask I) +
              (invCount (tailMask I) (compMask (tailMask I)) +
                invCount (compMask (tailMask I)) (tailMask I)) := by omega
        _ = degMask (tailMask I) + degMask (tailMask I) * degMask (compMask (tailMask I)) := by rw [h]
        _ = degMask (tailMask I) * (1 + degMask (compMask (tailMask I))) := by
              rw [Nat.mul_add, Nat.mul_one]
    · simp only [Bool.not_true, b2n_false, b2n_true, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      calc
        invCount (tailMask I) (compMask (tailMask I)) +
            (degMask (compMask (tailMask I)) + invCount (compMask (tailMask I)) (tailMask I))
          = degMask (compMask (tailMask I)) +
              (invCount (tailMask I) (compMask (tailMask I)) +
                invCount (compMask (tailMask I)) (tailMask I)) := by omega
        _ = degMask (compMask (tailMask I)) +
              degMask (tailMask I) * degMask (compMask (tailMask I)) := by rw [h]
        _ = (1 + degMask (tailMask I)) * degMask (compMask (tailMask I)) := by
              rw [Nat.add_mul, Nat.one_mul]

/-- General disjoint-mask shuffle identity: `inv(I, J) + inv(J, I) = |I| * |J|` whenever `I ∩ J = ∅`. -/
theorem invCount_add_invCount_of_disjoint {n : Nat} (I J : Mask n)
    (hd : disjointMask I J = true) :
    invCount I J + invCount J I = degMask I * degMask J := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [disjointMask, Bool.and_eq_true, Bool.not_eq_true'] at hd
    rcases hd with ⟨h0, htail⟩
    have h := ih (tailMask I) (tailMask J) htail
    simp only [invCount, degMask]
    cases hhI : headMask I <;> cases hhJ : headMask J
    · simp [h]
    · simp only [b2n_true, b2n_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add]
      calc
        degMask (tailMask I) + invCount (tailMask I) (tailMask J) + invCount (tailMask J) (tailMask I)
          = degMask (tailMask I) + (invCount (tailMask I) (tailMask J) + invCount (tailMask J) (tailMask I)) := by omega
        _ = degMask (tailMask I) + degMask (tailMask I) * degMask (tailMask J) := by rw [h]
        _ = degMask (tailMask I) * (1 + degMask (tailMask J)) := by rw [Nat.mul_add, Nat.mul_one]
    · simp only [b2n_false, b2n_true, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
      calc
        invCount (tailMask I) (tailMask J) + (degMask (tailMask J) + invCount (tailMask J) (tailMask I))
          = degMask (tailMask J) + (invCount (tailMask I) (tailMask J) + invCount (tailMask J) (tailMask I)) := by omega
        _ = degMask (tailMask J) + degMask (tailMask I) * degMask (tailMask J) := by rw [h]
        _ = (1 + degMask (tailMask I)) * degMask (tailMask J) := by rw [Nat.add_mul, Nat.one_mul]
    · rw [hhI, hhJ] at h0; cases h0

/-- Exact integer power of minus one: `signPow k = (-1)^k ∈ {1, -1}`. -/
def signPow (k : Nat) : Int :=
  if k % 2 == 0 then 1 else -1

@[simp] theorem signPow_zero : signPow 0 = 1 := rfl
@[simp] theorem signPow_one : signPow 1 = -1 := rfl

theorem signPow_add (a b : Nat) : signPow (a + b) = signPow a * signPow b := by
  unfold signPow
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab]

@[simp] theorem signPow_mul_self (k : Nat) : signPow k * signPow k = 1 := by
  rw [← signPow_add]
  unfold signPow
  have hk : (k + k) % 2 = 0 := by omega
  simp [hk]

theorem signPow_eq_one_iff (k : Nat) : signPow k = 1 ↔ k % 2 = 0 := by
  unfold signPow
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk <;> simp [hk]

theorem signPow_eq_neg_one_iff (k : Nat) : signPow k = -1 ↔ k % 2 = 1 := by
  unfold signPow
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk <;> simp [hk]

/-- Parity of a square: `(m * m) % 2 = m % 2`. -/
theorem sq_mod_two (m : Nat) : (m * m) % 2 = m % 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hexpand : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      calc
        (m + 1) * (m + 1) = (m + 1) * m + (m + 1) * 1 := Nat.mul_add (m + 1) m 1
        _ = (m * m + 1 * m) + (m + 1) := by rw [Nat.add_mul, Nat.mul_one]
        _ = m * m + 2 * m + 1 := by omega
    rw [hexpand]
    omega

/--
  A diagonal pseudo-Riemannian metric signature on an oriented orthonormal basis `e_0, ..., e_{n-1}`:
  `eta i = false` represents `⟨e_i, e_i⟩ = +1` (spacelike / positive-definite),
  `eta i = true`  represents `⟨e_i, e_i⟩ = -1` (timelike / negative-definite).
-/
abbrev MetricSig (n : Nat) : Type := Mask n

/-- The negative index of inertia `s` (number of `-1` eigenvalues in the signature). -/
def negIndex {n : Nat} (eta : MetricSig n) : Nat :=
  degMask eta

/-- Purely Riemannian (positive-definite) metric signature `(n, 0)`, so `s = 0`. -/
def riemSig (n : Nat) : MetricSig n :=
  emptyMask n

@[simp] theorem negIndex_riemSig (n : Nat) : negIndex (riemSig n) = 0 :=
  degMask_empty n

/-- Explicit coordinate formula for `(r, s)` signature on `Fin n` when `n = r + s`:
    first `r` basis covectors have `+1`, remaining `s` basis covectors have `-1`. -/
def sigOfRS (n r : Nat) : MetricSig n :=
  fun i => decide (r ≤ i.val)

/-- Canonical `(r, s)` signature on `ℝ^{r, s}` (`n = r + s`). -/
abbrev stdSigRS (r s : Nat) : MetricSig (r + s) :=
  sigOfRS (r + s) r

theorem negIndex_sigOfRS (n r s : Nat) (hn : r + s = n) :
    negIndex (sigOfRS n r) = s := by
  induction n generalizing r s with
  | zero =>
    have hs : s = 0 := by omega
    subst hs
    rfl
  | succ n ih =>
    cases r with
    | zero =>
      have hs : s = n + 1 := by omega
      subst hs
      have hfull : sigOfRS (n + 1) 0 = fullMask (n + 1) := by
        funext i
        simp [sigOfRS, fullMask]
      rw [negIndex, hfull, degMask_full]
    | succ r' =>
      unfold negIndex degMask
      have hhead : headMask (sigOfRS (n + 1) (r' + 1)) = false := by
        simp [headMask, sigOfRS]
      have htail : tailMask (sigOfRS (n + 1) (r' + 1)) = sigOfRS n r' := by
        funext i
        simp [tailMask, sigOfRS, Fin.succ]
      rw [hhead, htail, b2n_false, Nat.zero_add]
      exact ih r' s (by omega)

@[simp] theorem negIndex_stdSigRS (r s : Nat) : negIndex (stdSigRS r s) = s :=
  negIndex_sigOfRS (r + s) r s rfl

/-- Basis Gram inner product `η_I = ⟨e_I, e_I⟩ = ∏_{i ∈ I} η_i = (-1)^{|I ∩ {i : η_i = -1}|}`. -/
def etaSign {n : Nat} (eta : MetricSig n) (I : Mask n) : Int :=
  signPow (degMask (andMask I eta))

@[simp] theorem etaSign_mul_self {n : Nat} (eta : MetricSig n) (I : Mask n) :
    etaSign eta I * etaSign eta I = 1 :=
  signPow_mul_self _

theorem degMask_and_add_comp_and {n : Nat} (eta : MetricSig n) (I : Mask n) :
    degMask (andMask I eta) + degMask (andMask (compMask I) eta) = negIndex eta := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold negIndex at ih ⊢
    have ht1 : tailMask (andMask I eta) = andMask (tailMask I) (tailMask eta) := rfl
    have ht2 : tailMask (andMask (compMask I) eta) = andMask (compMask (tailMask I)) (tailMask eta) := rfl
    have hh1 : headMask (andMask I eta) = (headMask I && headMask eta) := rfl
    have hh2 : headMask (andMask (compMask I) eta) = (!(headMask I) && headMask eta) := rfl
    simp only [degMask, ht1, ht2, hh1, hh2]
    have h := ih (tailMask eta) (tailMask I)
    cases headMask I <;> cases headMask eta <;> simp <;> omega

/-- Product of metric signs on a subset and its complement equals `(-1)^s`:
    `η_I * η_{I^c} = (-1)^s`. -/
theorem etaSign_mul_etaSign_comp {n : Nat} (eta : MetricSig n) (I : Mask n) :
    etaSign eta I * etaSign eta (compMask I) = signPow (negIndex eta) := by
  unfold etaSign
  rw [← signPow_add, degMask_and_add_comp_and]

@[simp] theorem etaSign_riemSig {n : Nat} (I : Mask n) :
    etaSign (riemSig n) I = 1 := by
  have hand : andMask I (riemSig n) = emptyMask n := by
    funext i
    simp [andMask, riemSig, emptyMask]
  simp [etaSign, hand]

end HodgeDoubleStar
