import Std

namespace E8Gram

abbrev Vector := Fin 8 → Int

def sum (u : Vector) : Int :=
  u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7

def dot (u v : Vector) : Int := sum fun i => u i * v i
def sqnorm (u : Vector) : Int := dot u u

/-- The E8 lattice in coordinates doubled to clear denominators. -/
def Lattice (u : Vector) : Prop :=
  (∀ i, u i % 2 = u 0 % 2) ∧ sum u % 4 = 0

def gram (u v : Vector) : Int := sqnorm u * sqnorm v - dot u v * dot u v
def shift (u v : Vector) (k : Int) : Vector := fun i => v i - k * u i

private theorem sq_ge {n x : Int} (hn : 0 ≤ n) (hx : n ≤ x ∨ x ≤ -n) :
    n*n ≤ x*x := by
  rcases hx with pos | neg
  · have hx0 : 0 ≤ x := by omega
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right pos hn)
      (Int.mul_le_mul_of_nonneg_left pos hx0)
  · rw [← Int.neg_mul_neg x x]
    have h : n ≤ -x := by omega
    have hx0 : 0 ≤ -x := by omega
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h hn)
      (Int.mul_le_mul_of_nonneg_left h hx0)

private theorem sqnonneg (x : Int) : 0 ≤ x*x := by
  simpa using sq_ge (n := 0) (x := x) (by decide) (by omega)

private theorem abs_sq_ge (x : Int) (he : x % 2 = 0) : 2 * (x.natAbs : Int) ≤ x*x := by
  by_cases hx : 0 ≤ x
  · rw [Int.natAbs_of_nonneg hx]
    by_cases h : x = 0
    · simp [h]
    · exact Int.mul_le_mul_of_nonneg_right (by omega) hx
  · rw [Int.ofNat_natAbs_of_nonpos (by omega), ← Int.neg_mul_neg x x]
    exact Int.mul_le_mul_of_nonneg_right (by omega) (by omega)

private theorem abs_mod (x : Int) (he : x % 2 = 0) : (x.natAbs : Int) % 4 = x % 4 := by
  by_cases hx : 0 ≤ x
  · rw [Int.natAbs_of_nonneg hx]
  · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
    omega

private theorem add_mod_eq {a b c d : Int} (ha : a % 4 = b % 4)
    (hc : c % 4 = d % 4) : (a+c)%4 = (b+d)%4 := by
  calc
    (a+c)%4 = (a%4+c%4)%4 := Int.add_emod _ _ _
    _ = (b%4+d%4)%4 := by rw [ha,hc]
    _ = (b+d)%4 := (Int.add_emod _ _ _).symm

private theorem finCases {i : Fin 8} :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  simp only [Fin.ext_iff]
  have := i.isLt
  omega

private theorem sum_abs_pos (u : Vector) (hu : ∃ i, u i ≠ 0) :
    0 < sum (fun i => (u i).natAbs) := by
  rcases hu with ⟨i, hi⟩
  have h : (0 : Int) < (u i).natAbs := by
    by_cases hx : 0 ≤ u i
    · rw [Int.natAbs_of_nonneg hx]; omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]; omega
  simp only [sum]
  rcases finCases (i := i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem minimum_norm (u : Vector) (hu : Lattice u) (hn : ∃ i, u i ≠ 0) : 8 ≤ sqnorm u := by
  rcases hu with ⟨hpar, hsum⟩
  by_cases even : u 0 % 2 = 0
  · have he : ∀ i, u i % 2 = 0 := fun i => (hpar i).trans even
    have hs : sum (fun i => (u i).natAbs) % 4 = 0 := by
      have h0 := abs_mod (u 0) (he 0)
      have h1 := abs_mod (u 1) (he 1)
      have h2 := abs_mod (u 2) (he 2)
      have h3 := abs_mod (u 3) (he 3)
      have h4 := abs_mod (u 4) (he 4)
      have h5 := abs_mod (u 5) (he 5)
      have h6 := abs_mod (u 6) (he 6)
      have h7 := abs_mod (u 7) (he 7)
      simp only [sum] at hsum ⊢
      rw [add_mod_eq (add_mod_eq (add_mod_eq (add_mod_eq
        (add_mod_eq (add_mod_eq (add_mod_eq h0 h1) h2) h3) h4) h5) h6) h7]
      exact hsum
    have hl : 4 ≤ sum (fun i => (u i).natAbs) := by
      have := sum_abs_pos u hn
      omega
    have h0 := abs_sq_ge (u 0) (he 0)
    have h1 := abs_sq_ge (u 1) (he 1)
    have h2 := abs_sq_ge (u 2) (he 2)
    have h3 := abs_sq_ge (u 3) (he 3)
    have h4 := abs_sq_ge (u 4) (he 4)
    have h5 := abs_sq_ge (u 5) (he 5)
    have h6 := abs_sq_ge (u 6) (he 6)
    have h7 := abs_sq_ge (u 7) (he 7)
    simp only [sqnorm, dot, sum] at hl ⊢
    omega
  · have hodd : ∀ i, 1 ≤ u i * u i := by
      intro i
      have := hpar i
      simpa using sq_ge (n:=1) (x:=u i) (by decide) (by omega)
    have h0 := hodd 0
    have h1 := hodd 1
    have h2 := hodd 2
    have h3 := hodd 3
    have h4 := hodd 4
    have h5 := hodd 5
    have h6 := hodd 6
    have h7 := hodd 7
    simp only [sqnorm, dot, sum]
    omega

private theorem shift_lattice {u v : Vector} (hu : Lattice u) (hv : Lattice v) (k : Int) :
    Lattice (shift u v k) := by
  rcases hu with ⟨up, us⟩
  rcases hv with ⟨vp, vs⟩
  constructor
  · intro i
    change (v i-k*u i)%2 = (v 0-k*u 0)%2
    rw [Int.sub_emod (v i), Int.sub_emod (v 0), Int.mul_emod k (u i),
      Int.mul_emod k (u 0), up i, vp i]
  · have h : sum (shift u v k) = sum v - k * sum u := by
      simp only [shift, sum, Int.mul_add]
      omega
    rw [h, Int.sub_emod, Int.mul_emod, us, vs]
    simp

private theorem shift_dot (u v : Vector) (k : Int) :
    dot u (shift u v k) = dot u v - k * sqnorm u := by
  have hm (a b : Int) : a * (b-k*a) = a*b-k*(a*a) := by
    rw [Int.mul_sub, show a*(k*a)=k*(a*a) by ac_rfl]
  simp only [dot, sqnorm, sum, shift, hm, Int.mul_add]
  omega

private theorem shift_sq_coord (a b k : Int) :
    (a-k*b)*(a-k*b)=a*a-2*(k*(b*a))+(k*k)*(b*b) := by
  simp only [Int.sub_mul, Int.mul_sub]
  rw [show a*(k*b)=k*(b*a) by ac_rfl, show (k*b)*a=k*(b*a) by ac_rfl,
    show (k*b)*(k*b)=(k*k)*(b*b) by ac_rfl]
  omega

private theorem shift_sq (u v : Vector) (k : Int) :
    sqnorm (shift u v k) = sqnorm v - 2*(k*dot u v) + (k*k)*sqnorm u := by
  simp only [sqnorm, dot, sum, shift, shift_sq_coord, Int.mul_add]
  omega

private theorem shift_gram (u v : Vector) (hu : sqnorm u = 8) (k : Int) :
    gram u (shift u v k) = gram u v := by
  unfold gram
  rw [shift_dot, shift_sq, hu, shift_sq_coord]
  rw [show k * (8 * dot u v) = 8 * (k * dot u v) by ac_rfl]
  simp only [Int.mul_sub, Int.mul_add]
  rw [show (k*k)*8=8*(k*k) by ac_rfl, show (k*k)*(8*8)=64*(k*k) by
    change (k*k)*64=64*(k*k); ac_rfl]
  omega

/-- Positive determinants in the first orthogonalized projection are at least
    48 in doubled coordinates, hence at least 3 in E8 coordinates. -/
theorem minimum_gram (u v : Vector) (hu : Lattice u) (hv : Lattice v)
    (hshort : sqnorm u = 8) (hpos : 0 < gram u v) : 48 ≤ gram u v := by
  let k := (dot u v + 4) / 8
  let w := shift u v k
  have hw : Lattice w := shift_lattice hu hv k
  have hgram : gram u w = gram u v := shift_gram u v hshort k
  have hd : dot u w = dot u v - 8*k := by
    unfold w
    rw [shift_dot, hshort, Int.mul_comm]
  have hb : -4 ≤ dot u w ∧ dot u w ≤ 4 := by
    unfold k at hd
    omega
  have hb' : dot u w * dot u w ≤ 16 := by
    have h : dot u w = -4 ∨ dot u w = -3 ∨ dot u w = -2 ∨ dot u w = -1 ∨
        dot u w = 0 ∨ dot u w = 1 ∨ dot u w = 2 ∨ dot u w = 3 ∨ dot u w = 4 := by omega
    rcases h with h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hn : ∃ i, w i ≠ 0 := by
    by_cases h : ∃ i, w i ≠ 0
    · exact h
    · have he (i : Fin 8) : w i = 0 := by
        by_cases hi : w i = 0
        · exact hi
        · exact False.elim (h ⟨i, hi⟩)
      have hz : gram u w = 0 := by simp [gram, sqnorm, dot, sum, he]
      omega
  have hnorm := minimum_norm w hw hn
  have hbound : 48 ≤ gram u w := by
    unfold gram
    rw [hshort]
    omega
  rwa [hgram] at hbound

def first : Vector := fun i => if i = 0 then 2 else if i = 1 then -2 else 0
def second : Vector := fun i => if i = 0 ∨ i = 2 then 2 else 0

theorem firstLattice : Lattice first := by
  constructor
  · intro i; rcases finCases (i := i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem secondLattice : Lattice second := by
  constructor
  · intro i; rcases finCases (i := i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem firstMinimum : sqnorm first = 8 ∧
    ∀ u, Lattice u → (∃ i, u i ≠ 0) → sqnorm first ≤ sqnorm u := by
  refine ⟨by decide, ?_⟩
  intro u hu hn
  have : sqnorm first = 8 := by decide
  rw [this]
  exact minimum_norm u hu hn

theorem secondMinimum : gram first second = 48 ∧
    ∀ v, Lattice v → 0 < gram first v → gram first second ≤ gram first v := by
  refine ⟨by decide, ?_⟩
  intro v hv hpos
  have : gram first second = 48 := by decide
  rw [this]
  exact minimum_gram first v firstLattice hv firstMinimum.1 hpos

private def pair (i j : Fin 8) (a b : Int) : Vector :=
  fun k => if k = i then a else if k = j then b else 0

set_option maxHeartbeats 1500000 in
private theorem sum_pair (i j : Fin 8) (hne : i ≠ j) (a b : Int) :
    sum (pair i j a b) = a+b := by
  rcases finCases (i := i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finCases (i := j) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (hne rfl).elim | simp [sum, pair] <;> omega

set_option maxHeartbeats 1500000 in
private theorem dot_pair (u : Vector) (i j : Fin 8) (hne : i ≠ j) (a b : Int) :
    dot u (pair i j a b) = u i*a + u j*b := by
  have each (k : Fin 8) : u k * pair i j a b k = pair i j (u i*a) (u j*b) k := by
    by_cases hi : k=i
    · subst k; simp [pair]
    · by_cases hj : k=j
      · subst k; simp [pair, hi]
      · simp [pair, hi, hj]
  simp only [dot, each, sum_pair i j hne]

private theorem pair_lattice {i j : Fin 8} (hne : i ≠ j) {a b : Int}
    (ha : a%2=0) (hb : b%2=0) (hs : (a+b)%4=0) : Lattice (pair i j a b) := by
  have even (k : Fin 8) : pair i j a b k % 2 = 0 := by
    by_cases hi : k = i
    · simp [pair, hi, ha]
    · by_cases hj : k = j <;> simp [pair, hi, hj, hb, Ne.symm hne]
  exact ⟨fun k => (even k).trans (even 0).symm, by rwa [sum_pair i j hne]⟩

private theorem norm_pair {i j : Fin 8} (hne : i ≠ j) (a b : Int) :
    sqnorm (pair i j a b) = a*a+b*b := by
  rw [sqnorm, dot_pair _ i j hne]
  simp [pair, Ne.symm hne]

private theorem sq_le_norm (u : Vector) (i : Fin 8) : u i * u i ≤ sqnorm u := by
  have n0 := sqnonneg (u 0)
  have n1 := sqnonneg (u 1)
  have n2 := sqnonneg (u 2)
  have n3 := sqnonneg (u 3)
  have n4 := sqnonneg (u 4)
  have n5 := sqnonneg (u 5)
  have n6 := sqnonneg (u 6)
  have n7 := sqnonneg (u 7)
  simp only [sqnorm, dot, sum]
  rcases finCases (i:=i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem even_root_coord (u : Vector) (hn : sqnorm u = 8) (i : Fin 8)
    (he : u i % 2 = 0) (hi : u i ≠ 0) : u i * u i = 4 := by
  have hl := sq_le_norm u i
  have hb : -4 < u i ∧ u i < 4 := by
    by_cases h : 4 ≤ u i ∨ u i ≤ -4
    · have := sq_ge (by decide : 0 ≤ (4:Int)) h
      omega
    · omega
  have h : u i = 2 ∨ u i = -2 := by omega
  rcases h with h | h <;> rw [h] <;> decide

private theorem odd_root_coord (u : Vector) (hn : sqnorm u = 8) (i : Fin 8)
    (he : ∀ j, u j % 2 = 1) : u i*u i=1 := by
  have sq (j : Fin 8) : 1 ≤ u j*u j := by
    have := he j
    simpa using sq_ge (n:=1) (x:=u j) (by decide) (by omega)
  have n0 := sq 0
  have n1 := sq 1
  have n2 := sq 2
  have n3 := sq 3
  have n4 := sq 4
  have n5 := sq 5
  have n6 := sq 6
  have n7 := sq 7
  simp only [sqnorm, dot, sum] at hn
  rcases finCases (i:=i) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Each first shortest vector has a second root with the required inner
    product, so the determinant does not depend on the choice of first root. -/
theorem neighboring_root (u : Vector) (hu : Lattice u) (hn : sqnorm u = 8) :
    ∃ v, Lattice v ∧ sqnorm v = 8 ∧ dot u v = 4 := by
  by_cases even : u 0 % 2 = 0
  · have he (i : Fin 8) : u i % 2 = 0 := (hu.1 i).trans even
    have hnonzero : ∃ i, u i ≠ 0 := by
      by_cases h : ∃ i, u i ≠ 0
      · exact h
      · have hz (i : Fin 8) : u i = 0 := by
          by_cases hi : u i = 0
          · exact hi
          · exact (h ⟨i, hi⟩).elim
        simp [sqnorm, dot, sum, hz] at hn
    have hzero : ∃ j, u j = 0 := by
      by_cases h : ∃ j, u j = 0
      · exact h
      · have hnz (j : Fin 8) : u j ≠ 0 := fun h' => h ⟨j, h'⟩
        have n0 := even_root_coord u hn 0 (he 0) (hnz 0)
        have n1 := even_root_coord u hn 1 (he 1) (hnz 1)
        have n2 := even_root_coord u hn 2 (he 2) (hnz 2)
        have n3 := sqnonneg (u 3)
        have n4 := sqnonneg (u 4)
        have n5 := sqnonneg (u 5)
        have n6 := sqnonneg (u 6)
        have n7 := sqnonneg (u 7)
        simp only [sqnorm, dot, sum] at hn
        omega
    obtain ⟨i, hi⟩ := hnonzero
    obtain ⟨j, hj⟩ := hzero
    have hne : i ≠ j := by intro h; rw [h] at hi; exact hi hj
    have hisq := even_root_coord u hn i (he i) hi
    have hb : u i = 2 ∨ u i = -2 := by
      have hx := sq_le_norm u i
      have hlim : -4 < u i ∧ u i < 4 := by
        by_cases h : 4 ≤ u i ∨ u i ≤ -4
        · have := sq_ge (by decide : 0 ≤ (4:Int)) h; omega
        · omega
      have := he i
      omega
    refine ⟨pair i j (u i) 2, pair_lattice hne (he i) (by decide) ?_, ?_, ?_⟩
    · rcases hb with h | h <;> rw [h] <;> decide
    · rw [norm_pair hne, hisq]; decide
    · rw [dot_pair _ _ _ hne, hisq, hj]; decide
  · have he (i : Fin 8) : u i % 2 = 1 := by have := hu.1 i; omega
    have h0 := odd_root_coord u hn 0 he
    have h1 := odd_root_coord u hn 1 he
    have hne : (0 : Fin 8) ≠ 1 := by decide
    have a (x : Int) : (2*x)*(2*x)=4*(x*x) := by
      rw [show (2*x)*(2*x) = (2*2)*(x*x) by ac_rfl]
      rw [show (2:Int)*2=4 by decide]
    have b (x : Int) : x*(2*x)=2*(x*x) := by ac_rfl
    refine ⟨pair 0 1 (2*u 0) (2*u 1), pair_lattice hne (by omega) (by omega) (by
        have := he 0; have := he 1; omega), ?_, ?_⟩
    · rw [norm_pair hne, a, a, h0, h1]; decide
    · rw [dot_pair _ _ _ hne, b, b, h0, h1]; decide

structure KZPrefix (u v : Vector) : Prop where
  firstInLattice : Lattice u
  firstNonzero : ∃ i, u i ≠ 0
  shortestFirst : ∀ w, Lattice w → (∃ i, w i ≠ 0) → sqnorm u ≤ sqnorm w
  secondInLattice : Lattice v
  secondIndependent : 0 < gram u v
  shortestSecond : ∀ w, Lattice w → 0 < gram u w → gram u v ≤ gram u w

theorem explicitKZPrefix : KZPrefix first second := ⟨firstLattice, ⟨0, by decide⟩,
  firstMinimum.2, secondLattice, by decide, secondMinimum.2⟩

theorem everyKZSecondGram (u v : Vector) (h : KZPrefix u v) : gram u v / 16 = 3 := by
  have hn : sqnorm u = 8 := by
    have hmin := minimum_norm u h.firstInLattice h.firstNonzero
    have hmax := h.shortestFirst first firstLattice ⟨0, by decide⟩
    rw [firstMinimum.1] at hmax
    omega
  obtain ⟨w, hw, hnorm, hinner⟩ := neighboring_root u h.firstInLattice hn
  have hwGram : gram u w = 48 := by simp [gram, hn, hnorm, hinner]
  have hmin := minimum_gram u v h.firstInLattice h.secondInLattice hn h.secondIndependent
  have hmax := h.shortestSecond w hw (by rw [hwGram]; decide)
  rw [hwGram] at hmax
  omega

theorem secondGramNotPowerOfTwo (u v : Vector) (h : KZPrefix u v) (n : Nat) :
    gram u v / 16 ≠ (2 : Int)^n := by
  rw [everyKZSecondGram u v h]
  cases n with
  | zero => decide
  | succ k =>
    rw [Int.pow_succ]
    omega

#print axioms firstMinimum
#print axioms secondMinimum
#print axioms explicitKZPrefix
#print axioms everyKZSecondGram
#print axioms secondGramNotPowerOfTwo

end E8Gram
