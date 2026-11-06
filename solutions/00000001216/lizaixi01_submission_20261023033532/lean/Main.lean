import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace TLMC1216

/-- The actual infinite three-row board. Vertical movement is allowed between any rows. -/
abbrev Square := ℤ × Fin 3
def origin : Square := (0,0)

/-- Four wall columns first, then the 59 interior columns, then unused exterior columns. -/
def column (k : ℕ) : ℤ :=
  if k=0 then -31 else if k=1 then -30 else if k=2 then 30 else if k=3 then 31
  else if k<63 then (k : ℤ)-33 else (k : ℤ)-31

/-- A completely predetermined schedule, one square each turn. -/
def burn (n : ℕ) : Square := (column (n/3), ⟨n%3,Nat.mod_lt _ (by decide)⟩)

lemma column_injective : Function.Injective column := by
  intro m n h
  unfold column at h
  split_ifs at h <;> omega

lemma burn_injective : Function.Injective burn := by
  intro m n h
  have hc : column (m/3)=column (n/3) := congrArg Prod.fst h
  have hd := column_injective hc
  have hr : m%3=n%3 := congrArg (fun p : Square => p.2.val) h
  omega

lemma burn_at (k : ℕ) (y : Fin 3) : burn (3*k+y.val) = (column k,y) := by
  have hy := y.isLt
  have hd : (3*k+y.val)/3=k := by omega
  have hr : (3*k+y.val)%3=y.val := by omega
  apply Prod.ext
  · simp [burn,hd]
  · apply Fin.ext
    exact hr

lemma wall_turn_lt (i : Fin 4) (y : Fin 3) : 3*i.val+y.val<12 := by
  have hi := i.isLt
  have hy := y.isLt
  omega

lemma interior_covered (x : ℤ) (y : Fin 3) (hx : -29≤x ∧ x≤29) :
    ∃ m<189, burn m=(x,y) := by
  let k : ℕ := (x+33).toNat
  have hkcast : (k : ℤ)=x+33 := by
    dsimp [k]
    exact Int.toNat_of_nonneg (by omega)
  have hklo : 4≤k := by omega
  have hkhi : k<63 := by omega
  have hcol : column k=x := by
    simp [column,show k≠0 by omega,show k≠1 by omega,show k≠2 by omega,
      show k≠3 by omega,hkhi,hkcast]
  refine ⟨3*k+y.val,?_,?_⟩
  · have hy := y.isLt
    omega
  · rw [burn_at,hcol]

/-- Positions a(n+1) are chosen before the devil burns d(n).
Thus landing a(n+1) must avoid exactly the earlier burns d(m), m<n.
The devil may burn the occupied square, as in Conway's original rules. -/
def LegalPlay (d : ℕ → Square) (a : ℕ → Square) : Prop :=
  a 0=origin ∧
  (∀ n, |(a (n+1)).1-(a n).1|≤2) ∧
  (∀ n m, m<n → a (n+1)≠d m)

/-- The first rounds angel moves, each preceding the corresponding devil turn. -/
def LegalPrefix (d : ℕ → Square) (a : ℕ → Square) (rounds : ℕ) : Prop :=
  a 0=origin ∧
  (∀ n, n<rounds → |(a (n+1)).1-(a n).1|≤2) ∧
  (∀ n, n<rounds → ∀ m, m<n → a (n+1)≠d m)

lemma legal_prefix (d a : ℕ → Square) (h : LegalPlay d a) (rounds : ℕ) :
    LegalPrefix d a rounds :=
  ⟨h.1,fun n _ => h.2.1 n,fun n _ m hm => h.2.2 n m hm⟩

/-- Allowing arbitrary vertical motion and even staying only strengthens the angel.
Every usual king-distance-two move is included in the horizontal restriction. -/
lemma king_move_is_allowed (u v : Square)
    (h : max |v.1-u.1| |(v.2.val : ℤ)-(u.2.val : ℤ)|≤2) : |v.1-u.1|≤2 := by
  exact (le_max_left _ _).trans h

lemma horizontal_bound (a : ℕ → Square) (h0 : a 0=origin)
    (rounds : ℕ) (hstep : ∀ n, n<rounds → |(a (n+1)).1-(a n).1|≤2) :
    ∀ n : ℕ, n≤rounds → -2*(n : ℤ)≤(a n).1 ∧ (a n).1≤2*(n : ℤ) := by
  intro n
  induction n with
  | zero => intro _; simp [h0,origin]
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hs := abs_le.mp (hstep n (by omega))
    constructor <;> push_cast <;> omega

lemma avoids_wall (a : ℕ → Square)
    (ha : ∀ n, n<190 → ∀ m, m<n → a (n+1)≠burn m)
    (k : ℕ) (hk : 12≤k) (hkr : k<190) (i : Fin 4) :
    (a (k+1)).1≠column i.val := by
  intro h
  let y := (a (k+1)).2
  have hm : 3*i.val+y.val<k := (wall_turn_lt i y).trans_le hk
  apply ha k hkr (3*i.val+y.val) hm
  rw [burn_at]
  exact Prod.ext h rfl

lemma trapped_after_walls (a : ℕ → Square) (ha : LegalPrefix burn a 190) :
    ∀ n, n≤178 → -29≤(a (12+n)).1 ∧ (a (12+n)).1≤29 := by
  intro n
  induction n with
  | zero =>
    intro _
    have hb := horizontal_bound a ha.1 190 ha.2.1 12 (by omega)
    norm_num at hb
    simp only [Nat.add_zero]
    omega
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hkr : 12+n<190 := by omega
    have hs := abs_le.mp (ha.2.1 (12+n) hkr)
    have h0 := avoids_wall a ha.2.2 (12+n) (by omega) hkr 0
    have h1 := avoids_wall a ha.2.2 (12+n) (by omega) hkr 1
    have h2 := avoids_wall a ha.2.2 (12+n) (by omega) hkr 2
    have h3 := avoids_wall a ha.2.2 (12+n) (by omega) hkr 3
    norm_num [column] at h0 h1 h2 h3
    have he : 12+n+1=12+(n+1) := by omega
    rw [he] at hs h0 h1 h2 h3
    constructor <;> omega

/-- After 189 devil burns, the angel cannot make its 190th legal move. -/
theorem no_legal_190_moves (a : ℕ → Square) : ¬ LegalPrefix burn a 190 := by
  intro ha
  have ht := trapped_after_walls a ha 178 (by omega)
  norm_num at ht
  obtain ⟨m,hm,hburn⟩ := interior_covered (a 190).1 (a 190).2 ht
  have hne := ha.2.2 189 (by omega) m hm
  apply hne
  exact hburn.symm

theorem no_infinite_legal_play : ¬ ∃ a : ℕ → Square, LegalPlay burn a := by
  rintro ⟨a,ha⟩
  exact no_legal_190_moves a (legal_prefix burn a ha 190)

/-- Any full-history angel response rule, with no computability or locality restriction. -/
abbrev AngelStrategy := List Square → List Square → Square

/-- The first history contains the initial position and all angel positions so far;
the second contains exactly the squares already burned. -/
def Follows (A : AngelStrategy) (d a : ℕ → Square) : Prop :=
  ∀ n, a (n+1)=A ((List.range (n+1)).map a) ((List.range n).map d)

def Defeats (d : ℕ → Square) (A : AngelStrategy) : Prop :=
  ¬ ∃ a : ℕ → Square, LegalPlay d a ∧ Follows A d a

/-- An actual legal oblivious devil schedule defeats every full-history strategy. -/
theorem explicit_devil_defeats_every_strategy :
    Function.Injective burn ∧ ∀ A : AngelStrategy, Defeats burn A := by
  refine ⟨burn_injective,?_⟩
  intro A h
  obtain ⟨a,ha,_⟩ := h
  exact no_infinite_legal_play ⟨a,ha⟩

/-- Surviving all legal oblivious schedules is necessary for any winning strategy
against the usual, potentially adaptive devil. Even this necessary condition fails. -/
def EscapesEveryObliviousDevil (A : AngelStrategy) : Prop :=
  ∀ d : ℕ → Square, Function.Injective d →
    ∃ a : ℕ → Square, LegalPlay d a ∧ Follows A d a

theorem no_angel_winning_strategy : ¬ ∃ A : AngelStrategy, EscapesEveryObliviousDevil A := by
  rintro ⟨A,hA⟩
  exact (explicit_devil_defeats_every_strategy.2 A) (hA burn burn_injective)

end TLMC1216
