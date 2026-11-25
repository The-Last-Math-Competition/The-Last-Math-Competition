import Std

namespace DPGap

private theorem binomial_first_terms (a j : Nat) :
    a^j * (a+j+1) ≤ (a+1)^(j+1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : a*(a+(j+1)+1) ≤ (a+j+1)*(a+1) := by
      calc
        a*(a+(j+1)+1) = a*(a+j+1)+a := by
          rw [show a+(j+1)+1 = (a+j+1)+1 by omega, Nat.mul_succ]
        _ ≤ a*(a+j+1)+(a+j+1) := Nat.add_le_add_left (by omega) _
        _ = (a+j+1)*(a+1) := by rw [Nat.mul_comm a (a+j+1), ← Nat.mul_succ]
    calc
      a^(j+1)*(a+(j+1)+1) = a^j*(a*(a+(j+1)+1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ a^j*((a+j+1)*(a+1)) := Nat.mul_le_mul_left _ h
      _ = (a^j*(a+j+1))*(a+1) := by rw [Nat.mul_assoc]
      _ ≤ (a+1)^(j+1)*(a+1) := Nat.mul_le_mul_right _ ih
      _ = (a+1)^(j+1+1) := (Nat.pow_succ _ _).symm

theorem twice_smaller_power (k : Nat) (hk : 2 ≤ k) : 2*(k-1)^k < k^k := by
  cases k with
  | zero => omega
  | succ a =>
    have hpos : 0 < a^a := Nat.pow_pos (by omega)
    change 2*a^(a+1) < (a+1)^(a+1)
    calc
      2*a^(a+1) = a^a*(2*a) := by rw [Nat.pow_succ]; ac_rfl
      _ < a^a*(a+a+1) := Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ ≤ (a+1)^(a+1) := binomial_first_terms a a

private theorem le_two_pow (k : Nat) : k ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 0 < 2^k := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

def side (k : Nat) : Nat := 2*k*k

theorem counting_inequality (k : Nat) (hk : 2 ≤ k) :
    k^(2*side k)*(k-1)^(side k*side k) < k^(side k*side k) := by
  let m := side k
  let q := 2*k*m
  change k^(2*m)*(k-1)^(m*m) < k^(m*m)
  have hsize : m*m = k*q := by dsimp [m,q,side]; ac_rfl
  have hexp : k*(2*m) = q := by dsimp [q]; ac_rfl
  have htwo : (2^k)^(2*m) = 2^q := by rw [← Nat.pow_mul, hexp]
  have hsmall : (k-1)^(m*m) = ((k-1)^k)^q := by rw [← Nat.pow_mul, ← hsize]
  have hq : q ≠ 0 := by
    have hkp : 0 < k := by omega
    have hm : 0 < m := by dsimp [m,side]; exact Nat.mul_pos (Nat.mul_pos (by decide) hkp) hkp
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hkp) hm)
  calc
    k^(2*m)*(k-1)^(m*m) ≤ (2^k)^(2*m)*(k-1)^(m*m) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (le_two_pow k) _)
    _ = (2*(k-1)^k)^q := by rw [htwo, hsmall, Nat.mul_pow]
    _ < (k^k)^q := Nat.pow_lt_pow_left (twice_smaller_power k hk) hq
    _ = k^(m*m) := by rw [← Nat.pow_mul, ← hsize]

/-- All words of a prescribed length over an explicitly listed alphabet. -/
def words (choices : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => choices.flatMap fun x => (words choices n).map (x :: ·)

private theorem flatMap_length {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp [hx, ht, Nat.succ_mul, Nat.add_comm]

theorem words_length (choices : List Nat) (n : Nat) :
    (words choices n).length = choices.length^n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words, flatMap_length choices _ (choices.length^n)]
    · rw [Nat.pow_succ, Nat.mul_comm]
    · intro x _; simpa using ih

theorem words_nodup (choices : List Nat) (h : choices.Nodup) (n : Nat) :
    (words choices n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp only [words, List.Nodup, List.pairwise_flatMap]
    constructor
    · intro x _
      rw [List.pairwise_map]
      exact ih.imp (fun hn he => hn (List.cons.inj he).2)
    · apply h.imp
      intro a b hab x hx y hy eq
      simp only [List.mem_map] at hx hy
      obtain ⟨xs, _, rfl⟩ := hx
      obtain ⟨ys, _, rfl⟩ := hy
      exact hab (List.cons.inj eq).1

theorem words_membership (choices : List Nat) (n : Nat) (w : List Nat) :
    w ∈ words choices n ↔ w.length = n ∧ ∀ x ∈ w, x ∈ choices := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons x xs =>
      simp only [words, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, ha, z, hz, eq⟩
        rcases List.cons.inj eq with ⟨rfl,rfl⟩
        obtain ⟨hlen,hcolors⟩ := (ih z).mp hz
        refine ⟨by simp [hlen], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ha
        · exact hcolors _ hy
      · rintro ⟨hlen,hcolors⟩
        refine ⟨x, hcolors x (List.mem_cons_self ..), xs, (ih xs).mpr ⟨?_,?_⟩, rfl⟩
        · simpa using hlen
        · exact fun y hy => hcolors y (List.mem_cons_of_mem x hy)

/-- One shift is forbidden at each edge by a fixed vertex assignment. -/
def avoids : List Nat → List Nat → Prop
  | [], [] => True
  | x::xs, b::bs => x ≠ b ∧ avoids xs bs
  | _, _ => False

def compatible (k : Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | b::bs => ((List.range k).erase b).flatMap fun x => (compatible k bs).map (x :: ·)

theorem compatible_length (k : Nat) (bad : List Nat) (h : ∀ b ∈ bad, b < k) :
    (compatible k bad).length = (k-1)^bad.length := by
  induction bad with
  | nil => simp [compatible]
  | cons b bs ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem b hx))
    have hm : b ∈ List.range k := List.mem_range.mpr (h b (List.mem_cons_self ..))
    rw [compatible, flatMap_length _ _ ((k-1)^bs.length)]
    · simp [List.length_erase_of_mem hm, Nat.pow_succ, Nat.mul_comm]
    · intro x _; simpa using ht

theorem mem_compatible (k : Nat) (bad cover : List Nat) :
    cover ∈ compatible k bad ↔
      cover ∈ words (List.range k) bad.length ∧ avoids cover bad := by
  induction bad generalizing cover with
  | nil => cases cover <;> simp [compatible, words, avoids]
  | cons b bs ih =>
    cases cover with
    | nil => simp [compatible, words, avoids]
    | cons x xs =>
      simp only [compatible, List.length_cons, words, avoids, List.mem_flatMap, List.mem_map]
      have he (l : List Nat) (z : List (List Nat)) :
          (∃ a, a ∈ l ∧ ∃ r, r ∈ z ∧ a :: r = x :: xs) ↔ x ∈ l ∧ xs ∈ z := by
        constructor
        · rintro ⟨a, ha, r, hr, eq⟩
          rcases List.cons.inj eq with ⟨rfl,rfl⟩
          exact ⟨ha,hr⟩
        · rintro ⟨hx,hxs⟩
          exact ⟨x,hx,xs,hxs,rfl⟩
      rw [he, he, List.nodup_range.mem_erase_iff, ih]
      constructor
      · rintro ⟨⟨hne,hx⟩,hxs,hav⟩; exact ⟨⟨hx,hxs⟩,hne,hav⟩
      · rintro ⟨⟨hx,hxs⟩,hne,hav⟩; exact ⟨⟨hne,hx⟩,hxs,hav⟩

private theorem subset_length {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} (hxs : xs.Nodup) (h : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hxs
    have aIn : a ∈ ys := h (List.mem_cons_self ..)
    have hs : xs ⊆ ys.erase a := by
      intro x hx
      apply (List.mem_erase_of_ne (show x ≠ a from fun he => ha (he ▸ hx))).mpr
      exact h (List.mem_cons_of_mem a hx)
    have hl := ih hn hs
    rw [List.length_erase_of_mem aIn] at hl
    have hp : 0 < ys.length := List.length_pos_of_mem aIn
    simp only [List.length_cons]
    omega

def forbiddenShift (k a b : Nat) : Nat := (((b : Int)-(a : Int)) % (k : Int)).toNat

theorem forbidden_shift_lt (k a b : Nat) (hk : 0 < k) : forbiddenShift k a b < k := by
  have hk' : (0:Int) < (k:Int) := by exact_mod_cast hk
  have lo := Int.emod_nonneg ((b:Int)-(a:Int)) (by omega : (k:Int) ≠ 0)
  have hi := Int.emod_lt_of_pos ((b:Int)-(a:Int)) hk'
  unfold forbiddenShift
  omega

theorem cyclic_forbidden_iff (k a b s : Nat) (hk : 0 < k) (hb : b < k) (hs : s < k) :
    ((a : Int)+(s : Int)) % (k : Int) = b ↔ s = forbiddenShift k a b := by
  have hk' : (0:Int) < (k:Int) := by omega
  have lo := Int.emod_nonneg ((b:Int)-(a:Int)) (by omega : (k:Int) ≠ 0)
  have hs' : (s : Int) % (k : Int) = s := Int.emod_eq_of_lt (by omega) (by omega)
  have hb' : (b : Int) % (k : Int) = b := Int.emod_eq_of_lt (by omega) (by omega)
  have he : ((forbiddenShift k a b : Nat) : Int) = ((b : Int)-(a : Int)) % (k : Int) := by
    unfold forbiddenShift
    omega
  constructor
  · intro h
    have hi : ((b : Int)-(a : Int)) % (k : Int) = (s : Int) := by
      rw [← h, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      rw [show (a : Int)+(s : Int)-(a : Int) = (s:Int) by omega, hs']
    omega
  · intro h
    rw [show (s : Int) = ((b : Int)-(a : Int)) % (k : Int) by omega]
    rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
    rw [show (a : Int)+((b : Int)-(a : Int)) = (b : Int) by omega, hb']

/-- For each shift and right color, the matching has precisely one left
    endpoint. The left-to-right coordinate is the sum residue itself. -/
theorem matching_right_unique (k s b : Nat) (hk : 0 < k) (hb : b < k) :
    ∃ a < k, ((a : Int)+(s : Int)) % (k : Int) = b ∧
      ∀ a' < k, ((a' : Int)+(s : Int)) % (k : Int) = b → a' = a := by
  let a := forbiddenShift k s b
  have ha : a < k := forbidden_shift_lt _ _ _ hk
  refine ⟨a,ha,?_,?_⟩
  · rw [Int.add_comm]
    exact (cyclic_forbidden_iff k s b a hk hb ha).mpr rfl
  · intro a' ha' heq
    rw [Int.add_comm] at heq
    exact (cyclic_forbidden_iff k s b a' hk hb ha').mp heq

/-- Row-major encoding indexes the m×m edges without omissions or repeats. -/
theorem encode_edge (m i j : Nat) (hi : i < m) (hj : j < m) :
    m*i+j < m*m ∧ (m*i+j)/m = i ∧ (m*i+j)%m = j := by
  have hm : 0 < m := by omega
  refine ⟨?_, ?_, ?_⟩
  · calc
      m*i+j < m*i+m := Nat.add_lt_add_left hj _
      _ = m*(i+1) := (Nat.mul_succ m i).symm
      _ ≤ m*m := Nat.mul_le_mul_left m (by omega)
  · rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hj, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem decode_edge (m edge : Nat) (he : edge < m*m) :
    edge/m < m ∧ edge%m < m ∧ m*(edge/m)+edge%m = edge := by
  have hm : 0 < m := by cases m <;> simp_all
  exact ⟨Nat.div_lt_of_lt_mul he, Nat.mod_lt _ hm, by rw [Nat.add_comm, Nat.mod_add_div]⟩

def forbiddenWord (k m : Nat) (assignment : List Nat) : List Nat :=
  (List.range (m*m)).map fun edge =>
    forbiddenShift k (assignment[edge/m]?.getD 0) (assignment[m+edge%m]?.getD 0)

theorem forbidden_word_length (k m : Nat) (assignment : List Nat) :
    (forbiddenWord k m assignment).length = m*m := by simp [forbiddenWord]

private theorem forbidden_word_entries (k m : Nat) (hk : 0 < k) (a : List Nat) :
    ∀ c ∈ forbiddenWord k m a, c < k := by
  intro c hm
  simp only [forbiddenWord, List.mem_map] at hm
  obtain ⟨i, _, rfl⟩ := hm
  exact forbidden_shift_lt _ _ _ hk

def covers (k m : Nat) := words (List.range k) (m*m)
def assignments (k m : Nat) := words (List.range k) (2*m)
def colorableCovers (k m : Nat) := (assignments k m).flatMap fun a =>
  compatible k (forbiddenWord k m a)

theorem cover_count (k m : Nat) : (covers k m).length = k^(m*m) := by
  simp [covers, words_length]

theorem colorable_cover_list_count (k m : Nat) (hk : 0 < k) :
    (colorableCovers k m).length = k^(2*m)*(k-1)^(m*m) := by
  unfold colorableCovers
  rw [flatMap_length _ _ ((k-1)^(m*m))]
  · simp [assignments, words_length]
  · intro a _
    rw [compatible_length _ _ (forbidden_word_entries _ _ hk _), forbidden_word_length]

theorem exists_uncolorable_cyclic_cover (k : Nat) (hk : 2 ≤ k) :
    ∃ c ∈ covers k (side k), ∀ a ∈ assignments k (side k),
      ¬ avoids c (forbiddenWord k (side k) a) := by
  classical
  by_cases h : ∃ c ∈ covers k (side k), ∀ a ∈ assignments k (side k),
      ¬ avoids c (forbiddenWord k (side k) a)
  · exact h
  · have hsub : covers k (side k) ⊆ colorableCovers k (side k) := by
      intro c hc
      by_cases hc' : c ∈ colorableCovers k (side k)
      · exact hc'
      · exfalso
        apply h
        refine ⟨c,hc,?_⟩
        intro a ha hav
        apply hc'
        simp only [colorableCovers, List.mem_flatMap]
        refine ⟨a,ha,(mem_compatible _ _ _).mpr ⟨?_,hav⟩⟩
        rw [forbidden_word_length]
        exact hc
    have hlength : (covers k (side k)).length ≤ (colorableCovers k (side k)).length :=
      subset_length (words_nodup _ List.nodup_range _) hsub
    rw [cover_count, colorable_cover_list_count _ _ (by omega)] at hlength
    exact (Nat.not_le_of_gt (counting_inequality k hk) hlength).elim

/-- A bounded downward step cannot skip an integer target. -/
theorem deletion_hits (dp : Nat → Nat) (n target : Nat)
    (step : ∀ i < n, dp i ≤ dp (i+1)+1) (beginning : target ≤ dp 0)
    (ending : dp n ≤ target) : ∃ i ≤ n, dp i = target := by
  induction n with
  | zero => exact ⟨0,by omega,by omega⟩
  | succ n ih =>
    by_cases h : dp n ≤ target
    · obtain ⟨i,hi,he⟩ := ih (fun j hj => step j (by omega)) h
      exact ⟨i,by omega,he⟩
    · have hs := step n (by omega)
      exact ⟨n+1,by omega,by omega⟩

theorem exact_gap_of_deletion (dp vertices : Nat → Nat) (g n : Nat)
    (step : ∀ i < n, dp i ≤ dp (i+1)+1) (beginning : g+2 ≤ dp 0)
    (ending : dp n = 2) (size : ∀ i ≤ n, vertices i ≤ 2*side (g+1)) :
    ∃ i ≤ n, dp i-2 = g ∧ vertices i ≤ 4*(g+1)^2 := by
  obtain ⟨i,hi,he⟩ := deletion_hits dp n (g+2) step beginning (by omega)
  have hs : 2*side (g+1) = 4*(g+1)^2 := by
    unfold side
    rw [Nat.pow_succ, Nat.pow_one]
    change 2*(2*(g+1)*(g+1)) = (2*2)*((g+1)*(g+1))
    ac_rfl
  exact ⟨i,hi,by omega,hs ▸ size i hi⟩

#print axioms cyclic_forbidden_iff
#print axioms matching_right_unique
#print axioms encode_edge
#print axioms decode_edge
#print axioms exists_uncolorable_cyclic_cover
#print axioms exact_gap_of_deletion

end DPGap
