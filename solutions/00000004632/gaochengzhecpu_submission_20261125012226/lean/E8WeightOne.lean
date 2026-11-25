import Std

namespace E8WeightOne

/-- Euclidean coordinates are doubled. Thus a root has squared norm 8. -/
def squaredNorm : List Int → Int
  | [] => 0
  | x :: xs => x*x + squaredNorm xs

def coordinateSum : List Int → Int
  | [] => 0
  | x :: xs => x + coordinateSum xs

def sameParity (xs : List Int) (p : Int) : Prop := ∀ x ∈ xs, x % 2 = p

def lattice (xs : List Int) : Prop := xs.length = 8 ∧
  (sameParity xs 0 ∨ sameParity xs 1) ∧ coordinateSum xs % 4 = 0

def roots (xs : List Int) : Prop := lattice xs ∧ squaredNorm xs = 8

private theorem sq_nonneg (x : Int) : 0 ≤ x*x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem norm_nonneg (xs : List Int) : 0 ≤ squaredNorm xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have h := sq_nonneg x
    simp only [squaredNorm]
    omega

private theorem sq_le_norm {x : Int} {xs : List Int} (h : x ∈ xs) :
    x*x ≤ squaredNorm xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · have hh := norm_nonneg ys
      simp only [squaredNorm]
      omega
    · have hh := ih h
      have hy := sq_nonneg y
      simp only [squaredNorm]
      omega

private theorem coord_small (x : Int) (hx : x*x ≤ 8) : -2 ≤ x ∧ x ≤ 2 := by
  have aux (t : Int) (h : 3 ≤ t) : 9 ≤ t*t := by
    have hp : 0 ≤ t := by omega
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h (by decide : (0:Int) ≤ 3))
      (Int.mul_le_mul_of_nonneg_left h hp)
  constructor
  · by_cases h : -2 ≤ x
    · exact h
    · have hh := aux (-x) (by omega)
      rw [Int.neg_mul_neg] at hh
      omega
  · by_cases h : x ≤ 2
    · exact h
    · have hh := aux x (by omega)
      omega

private theorem even_square_mod (x : Int) (hx : x % 2 = 0) : x*x % 8 = (2*x) % 8 := by
  have h : x % 8 = 0 ∨ x % 8 = 2 ∨ x % 8 = 4 ∨ x % 8 = 6 := by omega
  rw [Int.mul_emod x x, Int.mul_emod 2 x]
  rcases h with h | h | h | h <;> rw [h] <;> decide

private theorem odd_square_mod (x : Int) (hx : x % 2 = 1) : x*x % 8 = 1 := by
  have h : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rw [Int.mul_emod x x]
  rcases h with h | h | h | h <;> rw [h] <;> decide

private theorem sum_mod {a b c d : Int} (h₁ : a%8=b%8) (h₂ : c%8=d%8) :
    (a+c)%8=(b+d)%8 := by
  calc
    (a+c)%8 = (a%8+c%8)%8 := Int.add_emod _ _ _
    _ = (b%8+d%8)%8 := by rw [h₁,h₂]
    _ = (b+d)%8 := (Int.add_emod _ _ _).symm

private theorem even_norm_mod (xs : List Int) (h : sameParity xs 0) :
    squaredNorm xs % 8 = (2*coordinateSum xs)%8 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have h₁ := even_square_mod x (h x (List.mem_cons_self ..))
    have h₂ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [squaredNorm, coordinateSum, Int.mul_add]
    exact sum_mod h₁ h₂

private theorem odd_norm_mod (xs : List Int) (h : sameParity xs 1) :
    squaredNorm xs % 8 = (xs.length : Int)%8 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have h₁ := odd_square_mod x (h x (List.mem_cons_self ..))
    have h₂ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [squaredNorm]
    rw [show ((x::xs).length : Int) = 1+(xs.length : Int) by simp; omega]
    exact sum_mod h₁ h₂

/-- Every lattice vector has even unscaled squared norm. -/
theorem lattice_even {xs : List Int} (h : lattice xs) : squaredNorm xs % 8 = 0 := by
  rcases h with ⟨hlen, hpar, hsum⟩
  rcases hpar with he | ho
  · rw [even_norm_mod xs he]
    omega
  · rw [odd_norm_mod xs ho, hlen]
    decide

/-- Backtracking enumeration with a remaining squared-norm budget. -/
def vectorsOfNorm (choices : List Int) : Nat → Int → List (List Int)
  | 0, budget => if budget = 0 then [[]] else []
  | dim + 1, budget => choices.flatMap fun x =>
    if x*x ≤ budget then (vectorsOfNorm choices dim (budget-x*x)).map (x :: ·) else []

theorem mem_vectorsOfNorm {choices : List Int} {dim : Nat} {budget : Int} {xs : List Int} :
    xs ∈ vectorsOfNorm choices dim budget ↔ xs.length = dim ∧ squaredNorm xs = budget ∧
      (∀ x ∈ xs, x ∈ choices) := by
  induction dim generalizing xs budget with
  | zero =>
    cases xs with
    | nil => by_cases h : budget = 0 <;> simp [vectorsOfNorm, squaredNorm, h, Eq.comm]
    | cons x xs => by_cases h : budget = 0 <;> simp [vectorsOfNorm, h]
  | succ dim ih =>
    constructor
    · intro h
      simp only [vectorsOfNorm, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      by_cases hb : x*x ≤ budget
      · simp only [hb, if_true, List.mem_map] at h
        obtain ⟨ys, hy, rfl⟩ := h
        obtain ⟨hlen, hnorm, hyc⟩ := ih.mp hy
        refine ⟨by simp [hlen], by simp only [squaredNorm]; omega, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hyc y hy
      · simp [hb] at h
    · rintro ⟨hlen, hnorm, hchoice⟩
      cases xs with
      | nil => simp at hlen
      | cons x ys =>
        have hy := norm_nonneg ys
        have hb : x*x ≤ budget := by simp only [squaredNorm] at hnorm; omega
        have hy' : ys ∈ vectorsOfNorm choices dim (budget-x*x) := by
          apply ih.mpr
          refine ⟨by simpa using hlen, by simp only [squaredNorm] at hnorm; omega, ?_⟩
          exact fun y h => hchoice y (List.mem_cons_of_mem x h)
        simp only [vectorsOfNorm, List.mem_flatMap]
        refine ⟨x, hchoice x (List.mem_cons_self ..), ?_⟩
        simp only [hb, if_true, List.mem_map]
        exact ⟨ys, hy', rfl⟩

def integralRoots : List (List Int) :=
  (vectorsOfNorm [-2,0,2] 8 8).filter (fun xs => coordinateSum xs % 4 == 0)

def halfIntegralRoots : List (List Int) :=
  (vectorsOfNorm [-1,1] 8 8).filter (fun xs => coordinateSum xs % 4 == 0)

def allRoots : List (List Int) := integralRoots ++ halfIntegralRoots

theorem root_enumeration (xs : List Int) : xs ∈ allRoots ↔ roots xs := by
  simp only [allRoots, integralRoots, halfIntegralRoots, List.mem_append, List.mem_filter,
    mem_vectorsOfNorm, beq_iff_eq]
  constructor
  · intro h
    rcases h with h | h
    · refine ⟨⟨h.1.1, Or.inl ?_, h.2⟩, h.1.2.1⟩
      intro x hx
      have hx := h.1.2.2 x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    · refine ⟨⟨h.1.1, Or.inr ?_, h.2⟩, h.1.2.1⟩
      intro x hx
      have hx := h.1.2.2 x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide
  · rintro ⟨⟨hlen, hpar, hsum⟩, hn⟩
    have small (x : Int) (hx : x ∈ xs) : -2 ≤ x ∧ x ≤ 2 :=
      coord_small x (hn ▸ sq_le_norm hx)
    rcases hpar with he | ho
    · left
      refine ⟨⟨hlen, hn, ?_⟩, hsum⟩
      intro x hx
      have hr := he x hx
      have hs := small x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · right
      refine ⟨⟨hlen, hn, ?_⟩, hsum⟩
      intro x hx
      have hr := ho x hx
      have hs := small x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem distinct_vectorsOfNorm (choices : List Int) (h : choices.Nodup)
    (dim : Nat) (budget : Int) : (vectorsOfNorm choices dim budget).Nodup := by
  induction dim generalizing budget with
  | zero => simp [vectorsOfNorm]; split <;> simp
  | succ dim ih =>
    simp only [vectorsOfNorm, List.Nodup, List.pairwise_flatMap]
    constructor
    · intro x _
      by_cases hx : x*x ≤ budget
      · simp only [hx, if_true, List.pairwise_map]
        exact (ih (budget-x*x)).imp (fun neq heq => neq (List.cons.inj heq).2)
      · simp [hx]
    · apply h.imp
      intro a b hab x hx y hy eq
      by_cases ha : a*a ≤ budget
      · by_cases hb : b*b ≤ budget
        · simp only [ha, hb, if_true, List.mem_map] at hx hy
          obtain ⟨xs, _, rfl⟩ := hx
          obtain ⟨ys, _, rfl⟩ := hy
          exact hab (List.cons.inj eq).1
        · simp [hb] at hy
      · simp [ha] at hx

theorem root_list_nodup : allRoots.Nodup := by
  unfold allRoots
  apply List.pairwise_append.mpr
  refine ⟨(distinct_vectorsOfNorm [-2,0,2] (by decide) 8 8).filter _,
    (distinct_vectorsOfNorm [-1,1] (by decide) 8 8).filter _, ?_⟩
  intro xs hxs ys hys heq
  subst ys
  have h₁ := mem_vectorsOfNorm.mp (List.mem_filter.mp hxs).1
  have h₂ := mem_vectorsOfNorm.mp (List.mem_filter.mp hys).1
  cases xs with
  | nil => simp at h₁
  | cons x rest =>
    have ha := h₁.2.2 x (List.mem_cons_self ..)
    have hb := h₂.2.2 x (List.mem_cons_self ..)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem counts : integralRoots.length = 112 ∧ halfIntegralRoots.length = 128 ∧
    allRoots.length = 240 := by decide

structure BasisCoordinates where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  c4 : Int
  c5 : Int
  c6 : Int
  c7 : Int

/-- Rows of the doubled basis are 4e₀, 2(eᵢ-e₀) for i=1,…,6, and (1,…,1). -/
def basisExpansion (c : BasisCoordinates) : List Int :=
  [4*c.c0-2*(c.c1+c.c2+c.c3+c.c4+c.c5+c.c6)+c.c7,
    2*c.c1+c.c7, 2*c.c2+c.c7, 2*c.c3+c.c7, 2*c.c4+c.c7, 2*c.c5+c.c7,
    2*c.c6+c.c7, c.c7]

theorem expansion_in_lattice (c : BasisCoordinates) : lattice (basisExpansion c) := by
  have hp (x : Int) (hx : x ∈ basisExpansion c) : x % 2 = c.c7 % 2 := by
    simp only [basisExpansion, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hpar : c.c7%2 = 0 ∨ c.c7%2 = 1 := by omega
  refine ⟨rfl, ?_, ?_⟩
  · rcases hpar with h | h
    · exact Or.inl (fun x hx => (hp x hx).trans h)
    · exact Or.inr (fun x hx => (hp x hx).trans h)
  · simp only [basisExpansion, coordinateSum]
    omega

theorem lattice_spanned_by_basis (xs : List Int) (h : lattice xs) :
    ∃ c, basisExpansion c = xs := by
  rcases h with ⟨hlen, hpar, hsum⟩
  rcases xs with _ | ⟨a0,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a1,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a2,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a3,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a4,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a5,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a6,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨a7,xs⟩
  · simp at hlen
  have hz : xs = [] := by simp at hlen; exact hlen
  subst xs
  have hp (x : Int) (hx : x ∈ [a0,a1,a2,a3,a4,a5,a6,a7]) : x % 2 = a7 % 2 := by
    rcases hpar with he | ho
    · rw [he x hx, he a7 (by simp)]
    · rw [ho x hx, ho a7 (by simp)]
  have h1 := hp a1 (by simp)
  have h2 := hp a2 (by simp)
  have h3 := hp a3 (by simp)
  have h4 := hp a4 (by simp)
  have h5 := hp a5 (by simp)
  have h6 := hp a6 (by simp)
  simp only [coordinateSum] at hsum
  refine ⟨⟨(a0+a1+a2+a3+a4+a5+a6+a7)/4-2*a7,
    (a1-a7)/2, (a2-a7)/2, (a3-a7)/2, (a4-a7)/2, (a5-a7)/2, (a6-a7)/2, a7⟩, ?_⟩
  simp only [basisExpansion, List.cons.injEq, and_true]
  repeat' constructor <;> omega

private def indicator (i j : Nat) : Int := if i = j then 1 else 0

def basis : List (List Int) := (List.range 8).map fun i =>
  basisExpansion ⟨indicator i 0, indicator i 1, indicator i 2, indicator i 3,
    indicator i 4, indicator i 5, indicator i 6, indicator i 7⟩

def entry (i j : Nat) : Int := (basis[i]?.getD [])[j]?.getD 0

def lowerTriangular : Bool := (List.range 8).all fun i =>
  (List.range 8).all fun j => !(i < j) || entry i j == 0

def diagonalProduct : Int := (List.range 8).foldl (fun p i => p * entry i i) 1

theorem basis_certificate : basis.length = 8 ∧ lowerTriangular = true ∧
    diagonalProduct = 256 ∧ diagonalProduct / 2^8 = 1 := by decide

def centralCharge : Nat := basis.length
def weightOneDimension : Nat := basis.length + allRoots.length

/-- Numerical data of the lattice VOA from its rank and norm-two vectors. -/
theorem counterexampleData : centralCharge = 8 ∧ centralCharge < 24 ∧
    weightOneDimension = 248 ∧ ¬ (weightOneDimension = 0 ∨ weightOneDimension = 1) := by
  simp only [centralCharge, weightOneDimension, basis_certificate.1, counts.2.2]
  decide

#print axioms lattice_even
#print axioms lattice_spanned_by_basis
#print axioms root_enumeration
#print axioms root_list_nodup
#print axioms counts
#print axioms basis_certificate
#print axioms counterexampleData

end E8WeightOne
