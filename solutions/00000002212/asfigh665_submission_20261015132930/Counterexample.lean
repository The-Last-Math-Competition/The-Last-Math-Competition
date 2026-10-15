import Std
namespace CatenaryCounterexample
structure Triple where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def value (g x : Triple) : Nat := g.a*x.a + g.b*x.b + g.c*x.c

def distance (x y : Triple) : Nat :=
  max ((x.a - min x.a y.a) + (x.b - min x.b y.b) + (x.c - min x.c y.c))
      ((y.a - min x.a y.a) + (y.b - min x.b y.b) + (y.c - min x.c y.c))

inductive Chain (g : Triple) (N : Nat) : Triple → Triple → Prop
  | refl (x) : Chain g N x x
  | step {x y z} : value g x = value g y → distance x y ≤ N →
      Chain g N y z → Chain g N x z

def Bound (g : Triple) (N : Nat) : Prop :=
  ∀ x y, value g x = value g y → Chain g N x y

def CatenaryDegree (g : Triple) (N : Nat) : Prop :=
  Bound g N ∧ ∀ m, m < N → ¬ Bound g m

def g : Triple := ⟨3,4,5⟩
def h : Triple := ⟨3,7,8⟩

theorem distance_symm (x y : Triple) : distance x y = distance y x := by
  unfold distance
  omega

theorem chain_trans {g : Triple} {N : Nat} {x y z : Triple}
    (hxy : Chain g N x y) (hyz : Chain g N y z) : Chain g N x z := by
  induction hxy with
  | refl => exact hyz
  | step he hd _ ih => exact Chain.step he hd (ih hyz)

theorem chain_symm {g : Triple} {N : Nat} {x y : Triple}
    (p : Chain g N x y) : Chain g N y x := by
  induction p with
  | refl => exact Chain.refl _
  | step he hd _ ih =>
    apply chain_trans ih
    apply Chain.step he.symm
    · rw [distance_symm]; exact hd
    · exact Chain.refl _

def Normal (x : Triple) : Prop := x.b + x.c ≤ 1

theorem normalise (x : Triple) :
    ∃ y, Normal y ∧ value g x = value g y ∧ Chain g 3 x y := by
  have aux : ∀ k, ∀ x : Triple, x.b+x.c = k →
      ∃ y, Normal y ∧ value g x = value g y ∧ Chain g 3 x y := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx
      by_cases hb : 2 ≤ x.b
      · let y : Triple := ⟨x.a+1,x.b-2,x.c+1⟩
        have hv : value g x = value g y := by dsimp [value,g,y]; omega
        have hd : distance x y ≤ 3 := by dsimp [distance,y]; omega
        have hk : y.b+y.c < k := by dsimp [y]; omega
        obtain ⟨z, hn, hvz, hc⟩ := ih _ hk y rfl
        exact ⟨z,hn,hv.trans hvz,Chain.step hv hd hc⟩
      · by_cases hc : 2 ≤ x.c
        · let y : Triple := ⟨x.a+2,x.b+1,x.c-2⟩
          have hv : value g x = value g y := by dsimp [value,g,y]; omega
          have hd : distance x y ≤ 3 := by dsimp [distance,y]; omega
          have hk : y.b+y.c < k := by dsimp [y]; omega
          obtain ⟨z, hn, hvz, hp⟩ := ih _ hk y rfl
          exact ⟨z,hn,hv.trans hvz,Chain.step hv hd hp⟩
        · by_cases hm : x.b = 1 ∧ x.c = 1
          · let y : Triple := ⟨x.a+3,0,0⟩
            have hv : value g x = value g y := by dsimp [value,g,y]; omega
            have hd : distance x y ≤ 3 := by dsimp [distance,y]; omega
            exact ⟨y,by dsimp [Normal,y]; omega, hv,Chain.step hv hd (Chain.refl _)⟩
          · exact ⟨x,by dsimp [Normal]; omega,rfl,Chain.refl _⟩
  exact aux (x.b+x.c) x rfl

theorem normal_unique {x y : Triple} (hx : Normal x) (hy : Normal y)
    (he : value g x = value g y) : x = y := by
  cases x with
  | mk a b c =>
    cases y with
    | mk d e f =>
      dsimp [Normal,value,g] at *
      have hb01 : b = 0 ∨ b = 1 := by omega
      have hc01 : c = 0 ∨ c = 1 := by omega
      have he01 : e = 0 ∨ e = 1 := by omega
      have hf01 : f = 0 ∨ f = 1 := by omega
      have ha : a=d := by rcases hb01 with hb | hb <;> rcases hc01 with hc | hc <;> rcases he01 with he | he <;> rcases hf01 with hf | hf <;> omega
      have hb : b=e := by omega
      have hc : c=f := by omega
      subst_vars
      rfl

theorem g_bound_three : Bound g 3 := by
  intro x y hxy
  obtain ⟨u,hu,hxu,hcu⟩ := normalise x
  obtain ⟨v,hv,hyv,hcv⟩ := normalise y
  have huv : u=v := normal_unique hu hv (hxu.symm.trans (hxy.trans hyv))
  subst v
  exact chain_trans hcu (chain_symm hcv)


theorem normalise_h (x : Triple) :
    ∃ y, Normal y ∧ value h x = value h y ∧ Chain h 5 x y := by
  have aux : ∀ k, ∀ x : Triple, x.b+x.c = k →
      ∃ y, Normal y ∧ value h x = value h y ∧ Chain h 5 x y := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx
      by_cases hb : 2 ≤ x.b
      · let y : Triple := ⟨x.a+2,x.b-2,x.c+1⟩
        have hv : value h x = value h y := by dsimp [value,h,y]; omega
        have hd : distance x y ≤ 5 := by dsimp [distance,y]; omega
        have hk : y.b+y.c < k := by dsimp [y]; omega
        obtain ⟨z, hn, hvz, hc⟩ := ih _ hk y rfl
        exact ⟨z,hn,hv.trans hvz,Chain.step hv hd hc⟩
      · by_cases hc : 2 ≤ x.c
        · let y : Triple := ⟨x.a+3,x.b+1,x.c-2⟩
          have hv : value h x = value h y := by dsimp [value,h,y]; omega
          have hd : distance x y ≤ 5 := by dsimp [distance,y]; omega
          have hk : y.b+y.c < k := by dsimp [y]; omega
          obtain ⟨z, hn, hvz, hp⟩ := ih _ hk y rfl
          exact ⟨z,hn,hv.trans hvz,Chain.step hv hd hp⟩
        · by_cases hm : x.b = 1 ∧ x.c = 1
          · let y : Triple := ⟨x.a+5,0,0⟩
            have hv : value h x = value h y := by dsimp [value,h,y]; omega
            have hd : distance x y ≤ 5 := by dsimp [distance,y]; omega
            exact ⟨y,by dsimp [Normal,y]; omega, hv,Chain.step hv hd (Chain.refl _)⟩
          · exact ⟨x,by dsimp [Normal]; omega,rfl,Chain.refl _⟩
  exact aux (x.b+x.c) x rfl

theorem normal_unique_h {x y : Triple} (hx : Normal x) (hy : Normal y)
    (he : value h x = value h y) : x = y := by
  cases x with
  | mk a b c =>
    cases y with
    | mk d e f =>
      dsimp [Normal,value,h] at *
      have hb01 : b = 0 ∨ b = 1 := by omega
      have hc01 : c = 0 ∨ c = 1 := by omega
      have he01 : e = 0 ∨ e = 1 := by omega
      have hf01 : f = 0 ∨ f = 1 := by omega
      have ha : a=d := by rcases hb01 with hb | hb <;> rcases hc01 with hc | hc <;> rcases he01 with he | he <;> rcases hf01 with hf | hf <;> omega
      have hb : b=e := by omega
      have hc : c=f := by omega
      subst_vars
      rfl

theorem h_bound_five : Bound h 5 := by
  intro x y hxy
  obtain ⟨u,hu,hxu,hcu⟩ := normalise_h x
  obtain ⟨v,hv,hyv,hcv⟩ := normalise_h y
  have huv : u=v := normal_unique_h hu hv (hxu.symm.trans (hxy.trans hyv))
  subst v
  exact chain_trans hcu (chain_symm hcv)



theorem isolated {g x : Triple} {N : Nat}
    (hi : ∀ y, value g x = value g y → distance x y ≤ N → x=y) :
    ∀ z, Chain g N x z → x=z := by
  intro z hc
  induction hc with
  | refl => rfl
  | @step a b c he hd hc ih =>
    have hab : a=b := hi b he hd
    subst b
    exact ih hi

theorem g_degree_three : CatenaryDegree g 3 := by
  refine ⟨g_bound_three, ?_⟩
  intro m hm hbound
  let x : Triple := ⟨3,0,0⟩
  let y : Triple := ⟨0,1,1⟩
  have hchain := hbound x y (by decide)
  have hi : ∀ z, value g x = value g z → distance x z ≤ m → x=z := by
    intro z hv hd
    cases z with
    | mk a b c =>
      dsimp [value,g,x,distance] at *
      have ha : a=3 := by omega
      have hb : b=0 := by omega
      have hc : c=0 := by omega
      subst_vars
      rfl
  have hh := isolated hi y hchain
  have hne : x ≠ y := by decide
  exact hne hh

theorem h_degree_five : CatenaryDegree h 5 := by
  refine ⟨h_bound_five, ?_⟩
  intro m hm hbound
  let x : Triple := ⟨5,0,0⟩
  let y : Triple := ⟨0,1,1⟩
  have hchain := hbound x y (by decide)
  have hi : ∀ z, value h x = value h z → distance x z ≤ m → x=z := by
    intro z hv hd
    cases z with
    | mk a b c =>
      dsimp [value,h,x,distance] at *
      have hb012 : b=0 ∨ b=1 ∨ b=2 := by omega
      have hc01 : c=0 ∨ c=1 := by omega
      have ha : a=5 := by rcases hb012 with hb | hb | hb <;> rcases hc01 with hc | hc <;> omega
      have hb : b=0 := by omega
      have hc : c=0 := by omega
      subst_vars
      rfl
  have hh := isolated hi y hchain
  have hne : x ≠ y := by decide
  exact hne hh



/-- Membership in the additive submonoid generated by the three entries. -/
def Member (g : Triple) (n : Nat) : Prop := ∃ x, value g x = n

theorem member_zero (g : Triple) : Member g 0 := by
  exact ⟨⟨0,0,0⟩, by simp [value]⟩

theorem member_add {g : Triple} {m n : Nat}
    (hm : Member g m) (hn : Member g n) : Member g (m+n) := by
  obtain ⟨x,hx⟩ := hm
  obtain ⟨y,hy⟩ := hn
  refine ⟨⟨x.a+y.a,x.b+y.b,x.c+y.c⟩, ?_⟩
  dsimp [value] at *
  simp only [Nat.mul_add]
  omega

/-- Positive distinct generators, each irreducible, with finite complement.
The three uniqueness clauses say that each displayed generator has only its
one-letter factorization, hence that these are precisely three minimal generators. -/
def Admissible (g : Triple) : Prop :=
  0 < g.a ∧ g.a < g.b ∧ g.b < g.c ∧
  (∀ x, value g x = g.a → x = ⟨1,0,0⟩) ∧
  (∀ x, value g x = g.b → x = ⟨0,1,0⟩) ∧
  (∀ x, value g x = g.c → x = ⟨0,0,1⟩) ∧
  ∃ conductor, ∀ n, conductor ≤ n → Member g n

theorem g_admissible : Admissible g := by
  refine ⟨by decide,by decide,by decide,?_,?_,?_,3,?_⟩
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,g] at he
      have ha : a=1 := by omega
      have hb : b=0 := by omega
      have hc : c=0 := by omega
      subst_vars; rfl
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,g] at he
      have ha : a=0 := by omega
      have hb : b=1 := by omega
      have hc : c=0 := by omega
      subst_vars; rfl
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,g] at he
      have ha : a=0 := by omega
      have hb : b=0 := by omega
      have hc : c=1 := by omega
      subst_vars; rfl
  · intro n hn
    have hr : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hr with hr | hr | hr
    · exact ⟨⟨n/3,0,0⟩, by dsimp [value,g]; omega⟩
    · exact ⟨⟨(n-4)/3,1,0⟩, by dsimp [value,g]; omega⟩
    · exact ⟨⟨(n-5)/3,0,1⟩, by dsimp [value,g]; omega⟩

theorem h_admissible : Admissible h := by
  refine ⟨by decide,by decide,by decide,?_,?_,?_,6,?_⟩
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,h] at he
      have ha : a=1 := by omega
      have hb : b=0 := by omega
      have hc : c=0 := by omega
      subst_vars; rfl
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,h] at he
      have hb01 : b=0 ∨ b=1 := by omega
      have hc01 : c=0 ∨ c=1 := by omega
      have ha : a=0 := by rcases hb01 with hb | hb <;> rcases hc01 with hc | hc <;> omega
      have hb : b=1 := by omega
      have hc : c=0 := by omega
      subst_vars; rfl
  · intro x he
    cases x with
    | mk a b c =>
      dsimp [value,h] at he
      have hb01 : b=0 ∨ b=1 := by omega
      have hc01 : c=0 ∨ c=1 := by omega
      have ha : a=0 := by rcases hb01 with hb | hb <;> rcases hc01 with hc | hc <;> omega
      have hb : b=0 := by omega
      have hc : c=1 := by omega
      subst_vars; rfl
  · intro n hn
    have hr : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hr with hr | hr | hr
    · exact ⟨⟨n/3,0,0⟩, by dsimp [value,h]; omega⟩
    · exact ⟨⟨(n-7)/3,1,0⟩, by dsimp [value,h]; omega⟩
    · exact ⟨⟨(n-8)/3,0,1⟩, by dsimp [value,h]; omega⟩

def minimumGenerator (g : Triple) := min g.a (min g.b g.c)

theorem degree_unique {g : Triple} {m n : Nat}
    (hm : CatenaryDegree g m) (hn : CatenaryDegree g n) : m=n := by
  by_cases hmn : m<n
  · exact False.elim (hn.2 m hmn hm.1)
  · by_cases hnm : n<m
    · exact False.elim (hm.2 n hnm hn.1)
    · omega

/-- The mathematical function claim; requiring an explicit function would only
strengthen this already false statement. -/
def Conjecture2212 : Prop :=
  ∃ f : Nat → Nat, ∀ a, Admissible a →
    CatenaryDegree a (f (minimumGenerator a))

theorem counterexample :
    Admissible g ∧ Admissible h ∧ minimumGenerator g = minimumGenerator h ∧
    CatenaryDegree g 3 ∧ CatenaryDegree h 5 := by
  exact ⟨g_admissible,h_admissible,by decide,g_degree_three,h_degree_five⟩

theorem conjecture_false : ¬ Conjecture2212 := by
  intro ⟨f,hf⟩
  have hg := degree_unique (hf g g_admissible) g_degree_three
  have hh := degree_unique (hf h h_admissible) h_degree_five
  change f 3 = 3 at hg
  change f 3 = 5 at hh
  omega

#print axioms counterexample
#print axioms conjecture_false
end CatenaryCounterexample
