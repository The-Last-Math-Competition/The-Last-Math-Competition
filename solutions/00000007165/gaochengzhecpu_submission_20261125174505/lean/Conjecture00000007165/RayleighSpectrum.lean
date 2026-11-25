/-
  Conjecture 00000007165 — Rayleigh Quotients, Hermitian Spectra & Linear Eigenspaces
  Core Lean 4.19.0 (zero external dependencies).

  Establishes:
  1. Real (`Vec n`) and complex (`CVec n`) inner-product modules and matrix spaces.
  2. Exact rational values `RatVal` (`num / den`, `0 < den`), exact Rayleigh quotients
     `rayleigh` and `cRayleigh`, and projective scale invariance (`ProjEquiv`, `CProjEquiv`).
  3. Hermitian quadratic form reality (`(hermInner z (cMatVec A z)).im = 0`).
  4. Theorem 1 (Positive Linear-Cone Characterization / Non-Vacuity):
     For any spectrum with maximum eigenvalue `lamMax` of multiplicity `m` (`1 ≤ m ≤ n`),
       `R_A(x) ≤ lamMax` and `R_A(x) = lamMax ↔ A x = lamMax • x`,
     so the unnormalized linear cone `{0} ∪ {x ≠ 0 : R_A(x) = lamMax}` equals the
     eigenspace `ker(A - lamMax I)` and has exact `𝔽`-dimension `m` (and real
     dimension `2m ≠ m` over `ℂ`).
-/

import Conjecture00000007165.ModuleDim

namespace Conjecture00000007165

/-! ## 1. Real Vectors `Vec n`, Inner Product, and Matrices `Mat n` -/

abbrev Vec (n : Nat) := Fin n → Int

def zeroVec (n : Nat) : Vec n := fun _ => 0
def addVec {n : Nat} (x y : Vec n) : Vec n := fun i => x i + y i
def negVec {n : Nat} (x : Vec n) : Vec n := fun i => - x i
def smulVec {n : Nat} (c : Int) (x : Vec n) : Vec n := fun i => c * x i

def vecZMod (n : Nat) : ZMod (Vec n) where
  zero := zeroVec n
  add := addVec
  neg := negVec
  smul := smulVec
  add_assoc := fun a b c => by funext i; simp [addVec]; omega
  add_comm := fun a b => by funext i; simp [addVec]; omega
  zero_add := fun a => by funext i; simp [addVec, zeroVec]
  add_zero := fun a => by funext i; simp [addVec, zeroVec]
  add_left_neg := fun a => by funext i; simp [addVec, negVec, zeroVec]; omega
  one_smul := fun a => by funext i; simp [smulVec]
  zero_smul := fun a => by funext i; simp [smulVec, zeroVec]
  smul_zero := fun c => by funext i; simp [smulVec, zeroVec]
  add_smul := fun c₁ c₂ a => by funext i; simp [smulVec, addVec, Int.add_mul]
  smul_add := fun c a b => by funext i; simp [smulVec, addVec, Int.mul_add]
  mul_smul := fun c₁ c₂ a => by funext i; simp [smulVec, Int.mul_assoc]

theorem vecFinSum_apply (n d : Nat) (f : Fin d → Vec n) (k : Fin n) :
    ZMod.finSum (vecZMod n) d f k = intSum d (fun j => f j k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [ZMod.finSum, intSum]
    change addVec (ZMod.finSum (vecZMod n) d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (f ⟨d, Nat.lt_succ_self d⟩) k = _
    simp only [addVec, ih]

def stdBasis (n : Nat) (j : Fin n) : Vec n :=
  fun i => if i = j then 1 else 0

def dot {n : Nat} (x y : Vec n) : Int :=
  intSum n (fun i => x i * y i)

def normSq {n : Nat} (x : Vec n) : Int := dot x x

theorem dot_comm {n : Nat} (x y : Vec n) : dot x y = dot y x := by
  unfold dot
  apply intSum_congr
  intro i
  exact Int.mul_comm _ _

theorem normSq_nonneg {n : Nat} (x : Vec n) : 0 ≤ normSq x := by
  unfold normSq dot
  exact intSum_nonneg (fun i => int_sq_nonneg (x i))

theorem normSq_eq_zero_iff {n : Nat} (x : Vec n) : normSq x = 0 ↔ x = zeroVec n := by
  unfold normSq dot
  rw [intSum_eq_zero_iff_of_nonneg (fun i => int_sq_nonneg (x i))]
  constructor
  · intro hall
    funext i
    exact (int_sq_eq_zero_iff (x i)).mp (hall i)
  · intro hx i
    rw [hx]
    rfl

theorem normSq_pos {n : Nat} {x : Vec n} (hx : x ≠ zeroVec n) : 0 < normSq x := by
  have hnn := normSq_nonneg x
  have hnz : normSq x ≠ 0 := fun h0 => hx ((normSq_eq_zero_iff x).mp h0)
  omega

theorem normSq_smul {n : Nat} (c : Int) (x : Vec n) :
    normSq (smulVec c x) = (c * c) * normSq x := by
  unfold normSq dot smulVec
  rw [← intSum_mul_left]
  apply intSum_congr
  intro i
  have : c * x i * (c * x i) = c * c * (x i * x i) := by
    simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  exact this

theorem normSq_stdBasis (n : Nat) (j : Fin n) : normSq (stdBasis n j) = 1 := by
  unfold normSq dot stdBasis
  have hcong : intSum n (fun i => (if i = j then (1 : Int) else 0) * (if i = j then 1 else 0)) =
      intSum n (fun i => if i = j then (1 : Int) else 0) := by
    apply intSum_congr
    intro i
    by_cases h : i = j <;> simp [h]
  rw [hcong, intSum_ite_eq]

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def zeroMat (n : Nat) : Mat n := fun _ _ => 0
def addMat {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j + B i j
def negMat {n : Nat} (A : Mat n) : Mat n := fun i j => - A i j
def smulMat {n : Nat} (c : Int) (A : Mat n) : Mat n := fun i j => c * A i j

def matZMod (n : Nat) : ZMod (Mat n) where
  zero := zeroMat n
  add := addMat
  neg := negMat
  smul := smulMat
  add_assoc := fun a b c => by funext i j; simp [addMat]; omega
  add_comm := fun a b => by funext i j; simp [addMat]; omega
  zero_add := fun a => by funext i j; simp [addMat, zeroMat]
  add_zero := fun a => by funext i j; simp [addMat, zeroMat]
  add_left_neg := fun a => by funext i j; simp [addMat, negMat, zeroMat]; omega
  one_smul := fun a => by funext i j; simp [smulMat]
  zero_smul := fun a => by funext i j; simp [smulMat, zeroMat]
  smul_zero := fun c => by funext i j; simp [smulMat, zeroMat]
  add_smul := fun c₁ c₂ a => by funext i j; simp [smulMat, addMat, Int.add_mul]
  smul_add := fun c a b => by funext i j; simp [smulMat, addMat, Int.mul_add]
  mul_smul := fun c₁ c₂ a => by funext i j; simp [smulMat, Int.mul_assoc]

theorem matFinSum_apply (n d : Nat) (f : Fin d → Mat n) (i j : Fin n) :
    ZMod.finSum (matZMod n) d f i j = intSum d (fun k => f k i j) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [ZMod.finSum, intSum]
    change addMat (ZMod.finSum (matZMod n) d (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
      (f ⟨d, Nat.lt_succ_self d⟩) i j = _
    simp only [addMat, ih]

def matVec {n : Nat} (A : Mat n) (x : Vec n) : Vec n :=
  fun i => intSum n (fun j => A i j * x j)

def transpose {n : Nat} (A : Mat n) : Mat n := fun i j => A j i

def IsSym {n : Nat} (A : Mat n) : Prop := ∀ i j, A i j = A j i

def trMat {n : Nat} (A : Mat n) : Int := intSum n (fun i => A i i)

def diagMat {n : Nat} (eigs : Fin n → Int) : Mat n :=
  fun i j => if i = j then eigs i else 0

theorem diagMat_isSym {n : Nat} (eigs : Fin n → Int) : IsSym (diagMat eigs) := by
  intro i j
  unfold diagMat
  by_cases h : i = j
  · subst h; rfl
  · have h' : j ≠ i := fun heq => h heq.symm
    simp [h, h']

theorem matVec_diagMat {n : Nat} (eigs : Fin n → Int) (x : Vec n) (i : Fin n) :
    matVec (diagMat eigs) x i = eigs i * x i := by
  unfold matVec diagMat
  have hcong : intSum n (fun j => (if i = j then eigs i else 0) * x j) =
      intSum n (fun j => if j = i then eigs j * x j else 0) := by
    apply intSum_congr
    intro j
    by_cases h : j = i
    · subst h; simp
    · have h' : i ≠ j := fun heq => h heq.symm
      simp [h, h']
  rw [hcong, intSum_ite_eq]

theorem dot_smulVec {n : Nat} (c : Int) (x y : Vec n) :
    dot (smulVec c x) y = c * dot x y := by
  unfold dot smulVec
  rw [← intSum_mul_left]
  apply intSum_congr
  intro i
  exact Int.mul_assoc c (x i) (y i)

theorem matVec_smulVec {n : Nat} (A : Mat n) (c : Int) (x : Vec n) :
    matVec A (smulVec c x) = smulVec c (matVec A x) := by
  funext i
  unfold matVec smulVec
  rw [← intSum_mul_left]
  apply intSum_congr
  intro j
  simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-! ## 2. Exact Rational Values `RatVal` and the Rayleigh Quotient -/

structure RatVal where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RatVal

def ofInt (k : Int) : RatVal := ⟨k, 1, by omega⟩

def Eq (r s : RatVal) : Prop := r.num * s.den = s.num * r.den

def Le (r s : RatVal) : Prop := r.num * s.den ≤ s.num * r.den

theorem eq_refl (r : RatVal) : Eq r r := rfl

theorem eq_symm {r s : RatVal} (h : Eq r s) : Eq s r := h.symm

end RatVal

/-- Exact Rayleigh quotient `R_A(x) = ⟨x, A x⟩ / ‖x‖²` for `x ≠ 0`. -/
def rayleigh {n : Nat} (A : Mat n) (x : Vec n) (hx : x ≠ zeroVec n) : RatVal :=
  ⟨dot x (matVec A x), normSq x, normSq_pos hx⟩

/-- Projective ray equivalence on `Vec n`: `a • x = b • y` for nonzero scalars `a, b`. -/
def ProjEquiv {n : Nat} (x y : Vec n) : Prop :=
  ∃ a b : Int, a ≠ 0 ∧ b ≠ 0 ∧ smulVec a x = smulVec b y

theorem projEquiv_refl {n : Nat} (x : Vec n) : ProjEquiv x x :=
  ⟨1, 1, by omega, by omega, rfl⟩

theorem projEquiv_symm {n : Nat} {x y : Vec n} (h : ProjEquiv x y) : ProjEquiv y x := by
  rcases h with ⟨a, b, ha, hb, hab⟩
  exact ⟨b, a, hb, ha, hab.symm⟩

theorem projEquiv_trans {n : Nat} {x y z : Vec n}
    (hxy : ProjEquiv x y) (hyz : ProjEquiv y z) : ProjEquiv x z := by
  rcases hxy with ⟨a₁, b₁, ha₁, hb₁, h1⟩
  rcases hyz with ⟨a₂, b₂, ha₂, hb₂, h2⟩
  refine ⟨a₂ * a₁, b₁ * b₂, Int.mul_ne_zero ha₂ ha₁, Int.mul_ne_zero hb₁ hb₂, ?_⟩
  funext i
  have hi1 := congrFun h1 i
  have hi2 := congrFun h2 i
  simp only [smulVec] at hi1 hi2 ⊢
  calc (a₂ * a₁) * x i
      = a₂ * (a₁ * x i) := by rw [Int.mul_assoc]
    _ = a₂ * (b₁ * y i) := by rw [hi1]
    _ = b₁ * (a₂ * y i) := by simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = b₁ * (b₂ * z i) := by rw [hi2]
    _ = (b₁ * b₂) * z i := by rw [Int.mul_assoc]

/-- Exact scale / projective invariance of the Rayleigh quotient: `[x] = [y] → R_A(x) = R_A(y)`. -/
theorem rayleigh_projInvar {n : Nat} (A : Mat n) {x y : Vec n}
    (hx : x ≠ zeroVec n) (hy : y ≠ zeroVec n) (hp : ProjEquiv x y) :
    RatVal.Eq (rayleigh A x hx) (rayleigh A y hy) := by
  rcases hp with ⟨a, b, ha, _hb, hab⟩
  unfold RatVal.Eq rayleigh
  simp only
  have hquad : (a * a) * dot x (matVec A x) = (b * b) * dot y (matVec A y) := by
    have h1 : dot (smulVec a x) (matVec A (smulVec a x)) = (a * a) * dot x (matVec A x) := by
      rw [matVec_smulVec, dot_smulVec, dot_comm x (smulVec a _), dot_smulVec, dot_comm]
      rw [Int.mul_assoc]
    have h2 : dot (smulVec b y) (matVec A (smulVec b y)) = (b * b) * dot y (matVec A y) := by
      rw [matVec_smulVec, dot_smulVec, dot_comm y (smulVec b _), dot_smulVec, dot_comm]
      rw [Int.mul_assoc]
    rw [← h1, hab, h2]
  have hnorm : (a * a) * normSq x = (b * b) * normSq y := by
    rw [← normSq_smul, hab, normSq_smul]
  have ha2_ne : a * a ≠ 0 := Int.mul_ne_zero ha ha
  apply Int.eq_of_mul_eq_mul_left ha2_ne
  calc (a * a) * (dot x (matVec A x) * normSq y)
      = ((a * a) * dot x (matVec A x)) * normSq y := by rw [← Int.mul_assoc]
    _ = ((b * b) * dot y (matVec A y)) * normSq y := by rw [hquad]
    _ = dot y (matVec A y) * ((b * b) * normSq y) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = dot y (matVec A y) * ((a * a) * normSq x) := by rw [← hnorm]
    _ = (a * a) * (dot y (matVec A y) * normSq x) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-! ## 3. Theorem 1A: Positive Linear-Cone Characterization (Real Symmetric Case) -/

/-- Ordered spectrum condition: `lamMax` is the maximum eigenvalue of `eigs` with exact multiplicity `m`. -/
def HasMaxMult {n : Nat} (eigs : Fin n → Int) (lamMax : Int) (m : Nat) : Prop :=
  1 ≤ m ∧ m ≤ n ∧
  (∀ i : Fin n, i.val < m → eigs i = lamMax) ∧
  (∀ i : Fin n, m ≤ i.val → eigs i < lamMax)

def RealEigenspace {n : Nat} (A : Mat n) (lam : Int) (x : Vec n) : Prop :=
  matVec A x = smulVec lam x

/-- Spectral gap identity: `lamMax * ‖x‖² - ⟨x, diag(eigs) x⟩ = ∑ᵢ (lamMax - eigsᵢ) xᵢ²`. -/
theorem diag_spectral_gap {n : Nat} (eigs : Fin n → Int) (lamMax : Int) (x : Vec n) :
    lamMax * normSq x - dot x (matVec (diagMat eigs) x) =
      intSum n (fun i => (lamMax - eigs i) * (x i * x i)) := by
  unfold normSq dot
  rw [← intSum_mul_left]
  have hsub : ∀ d : Nat, (f g : Fin d → Int) →
      intSum d f - intSum d g = intSum d (fun i => f i - g i) := by
    intro d f g
    induction d with
    | zero => rfl
    | succ d ih =>
      simp only [intSum]
      have := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                 (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega
  rw [hsub]
  apply intSum_congr
  intro i
  rw [matVec_diagMat]
  have : lamMax * (x i * x i) - x i * (eigs i * x i) = (lamMax - eigs i) * (x i * x i) := by
    rw [Int.sub_mul]
    simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  exact this

theorem rayleigh_le_max {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) {x : Vec n} (hx : x ≠ zeroVec n) :
    RatVal.Le (rayleigh (diagMat eigs) x hx) (RatVal.ofInt lamMax) := by
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  unfold RatVal.Le rayleigh RatVal.ofInt
  simp only [Int.mul_one]
  have hgap := diag_spectral_gap eigs lamMax x
  have hnonneg : 0 ≤ intSum n (fun i => (lamMax - eigs i) * (x i * x i)) := by
    apply intSum_nonneg
    intro i
    have hsq := int_sq_nonneg (x i)
    by_cases hi : i.val < m
    · rw [h_eq i hi]; simp
    · have hge : m ≤ i.val := by omega
      have hlt_i := h_lt i hge
      have hpos : 0 ≤ lamMax - eigs i := by omega
      exact Int.mul_nonneg hpos hsq
  omega

theorem eigvec_diag_iff_vanish_above {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) (x : Vec n) :
    RealEigenspace (diagMat eigs) lamMax x ↔ ∀ i : Fin n, m ≤ i.val → x i = 0 := by
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  unfold RealEigenspace
  constructor
  · intro heig i hi
    have hi_eq := congrFun heig i
    rw [matVec_diagMat] at hi_eq
    simp only [smulVec] at hi_eq
    have hdiff : (lamMax - eigs i) * x i = 0 := by
      rw [Int.sub_mul, ← hi_eq]
      omega
    have hne : lamMax - eigs i ≠ 0 := by
      have := h_lt i hi
      omega
    cases Int.mul_eq_zero.mp hdiff with
    | inl h0 => exact absurd h0 hne
    | inr hx0 => exact hx0
  · intro hvan
    funext i
    rw [matVec_diagMat]
    simp only [smulVec]
    by_cases hi : i.val < m
    · rw [h_eq i hi]
    · have hge : m ≤ i.val := by omega
      rw [hvan i hge]
      simp

theorem rayleigh_eq_max_iff_eigvec {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) {x : Vec n} (hx : x ≠ zeroVec n) :
    RatVal.Eq (rayleigh (diagMat eigs) x hx) (RatVal.ofInt lamMax) ↔
      RealEigenspace (diagMat eigs) lamMax x := by
  have hiff_van := eigvec_diag_iff_vanish_above hspec x
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  rw [hiff_van]
  unfold RatVal.Eq rayleigh RatVal.ofInt
  simp only [Int.mul_one]
  have hgap := diag_spectral_gap eigs lamMax x
  have hterm_nonneg : ∀ i : Fin n, 0 ≤ (lamMax - eigs i) * (x i * x i) := by
    intro i
    have hsq := int_sq_nonneg (x i)
    by_cases hi : i.val < m
    · rw [h_eq i hi]; simp
    · have hlt_i := h_lt i (by omega)
      exact Int.mul_nonneg (by omega) hsq
  constructor
  · intro heq i hi
    have hsum0 : intSum n (fun j => (lamMax - eigs j) * (x j * x j)) = 0 := by omega
    have hall := (intSum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum0 i
    have hpos : lamMax - eigs i ≠ 0 := by
      have := h_lt i hi
      omega
    cases Int.mul_eq_zero.mp hall with
    | inl h0 => exact absurd h0 hpos
    | inr hsq0 => exact (int_sq_eq_zero_iff (x i)).mp hsq0
  · intro hvan
    have hsum0 : intSum n (fun j => (lamMax - eigs j) * (x j * x j)) = 0 := by
      apply (intSum_eq_zero_iff_of_nonneg hterm_nonneg).mpr
      intro j
      by_cases hj : j.val < m
      · rw [h_eq j hj]; simp
      · rw [hvan j (by omega)]; simp
    omega

/-- The unnormalized linear cone `{0} ∪ {x ≠ 0 : R_A(x) = lamMax}` has exact dimension `m`. -/
theorem realEigenspace_hasDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ZMod.HasDim (vecZMod n) (RealEigenspace (diagMat eigs) lamMax) m := by
  have hmn : m ≤ n := hspec.2.1
  let b : Fin m → Vec n := fun j => stdBasis n ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩
  let coord : Vec n → Fin m → Int := fun v j => v ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩
  apply ZMod.hasDim_of_coords (vecZMod n) b coord
  · intro j
    rw [eigvec_diag_iff_vanish_above hspec]
    intro i hi
    simp only [b, stdBasis]
    have hne : i ≠ ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩ := by
      intro heq
      have hv : i.val = j.val := congrArg Fin.val heq
      omega
    simp [hne]
  · intro c j
    unfold coord ZMod.linComb
    rw [vecFinSum_apply]
    have hcong : intSum m (fun k => ((vecZMod n).smul (c k) (b k)) ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩) =
        intSum m (fun k => if k = j then c k else 0) := by
      apply intSum_congr
      intro k
      simp only [vecZMod, smulVec, b, stdBasis]
      by_cases hkj : k = j
      · subst hkj; simp
      · have hne : (⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩ : Fin n) ≠
            ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
          intro heq
          apply hkj
          exact Fin.ext (congrArg Fin.val heq).symm
        simp [hkj, hne]
    rw [hcong, intSum_ite_eq]
  · intro _j; rfl
  · intro v hv
    have hvan := (eigvec_diag_iff_vanish_above hspec v).mp hv
    funext i
    unfold ZMod.linComb coord
    rw [vecFinSum_apply]
    by_cases hi : i.val < m
    · let j₀ : Fin m := ⟨i.val, hi⟩
      have hcong : intSum m (fun k => ((vecZMod n).smul (v ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k)) i) =
          intSum m (fun k => if k = j₀ then v i else 0) := by
        apply intSum_congr
        intro k
        simp only [vecZMod, smulVec, b, stdBasis]
        by_cases hkj : k = j₀
        · subst hkj
          have heq : i = ⟨j₀.val, Nat.lt_of_lt_of_le j₀.isLt hmn⟩ := Fin.ext rfl
          simp [heq]
        · have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
            intro heq
            apply hkj
            exact Fin.ext (congrArg Fin.val heq).symm
          simp [hkj, hne]
      rw [hcong, intSum_ite_eq]
    · rw [hvan i (by omega)]
      have hcong : intSum m (fun k => ((vecZMod n).smul (v ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k)) i) =
          intSum m (fun _ => 0) := by
        apply intSum_congr
        intro k
        simp only [vecZMod, smulVec, b, stdBasis]
        have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
          intro heq
          have hv_eq : i.val = k.val := congrArg Fin.val heq
          omega
        simp [hne]
      rw [hcong, intSum_zero_fn]

/-! ## 4. Complex Vectors `CVec n`, Hermitian Matrices `CMat n`, & Complex Rayleigh Quotient -/

abbrev CVec (n : Nat) := Fin n → GaussInt

def zeroCVec (n : Nat) : CVec n := fun _ => GaussInt.zero
def addCVec {n : Nat} (z w : CVec n) : CVec n := fun i => GaussInt.add (z i) (w i)
def negCVec {n : Nat} (z : CVec n) : CVec n := fun i => GaussInt.neg (z i)
def rSmulCVec {n : Nat} (c : Int) (z : CVec n) : CVec n :=
  fun i => GaussInt.mul (GaussInt.ofInt c) (z i)
def cSmulCVec {n : Nat} (c : GaussInt) (z : CVec n) : CVec n :=
  fun i => GaussInt.mul c (z i)

def cVecRMod (n : Nat) : ZMod (CVec n) where
  zero := zeroCVec n
  add := addCVec
  neg := negCVec
  smul := rSmulCVec
  add_assoc := fun a b c => by funext i; exact GaussInt.add_assoc _ _ _
  add_comm := fun a b => by funext i; exact GaussInt.add_comm _ _
  zero_add := fun a => by funext i; exact GaussInt.zero_add _
  add_zero := fun a => by funext i; exact GaussInt.add_zero _
  add_left_neg := fun a => by funext i; exact GaussInt.add_left_neg _
  one_smul := fun a => by funext i; exact GaussInt.one_mul _
  zero_smul := fun a => by funext i; exact GaussInt.zero_mul _
  smul_zero := fun c => by funext i; exact GaussInt.mul_zero _
  add_smul := fun c₁ c₂ a => by
    funext i
    simp only [rSmulCVec, addCVec]
    have h : GaussInt.ofInt (c₁ + c₂) = GaussInt.add (GaussInt.ofInt c₁) (GaussInt.ofInt c₂) := by
      ext <;> simp [GaussInt.ofInt, GaussInt.add]
    rw [h, GaussInt.add_mul]
  smul_add := fun c a b => by funext i; exact GaussInt.mul_add _ _ _
  mul_smul := fun c₁ c₂ a => by
    funext i
    simp only [rSmulCVec]
    have h : GaussInt.ofInt (c₁ * c₂) = GaussInt.mul (GaussInt.ofInt c₁) (GaussInt.ofInt c₂) := by
      ext <;> simp [GaussInt.ofInt, GaussInt.mul]
    rw [h, GaussInt.mul_assoc]

def cVecCMod (n : Nat) : CMod (CVec n) where
  toZMod := cVecRMod n
  csmul := cSmulCVec
  one_csmul := fun a => by funext i; exact GaussInt.one_mul _
  zero_csmul := fun a => by funext i; exact GaussInt.zero_mul _
  csmul_zero := fun z => by funext i; exact GaussInt.mul_zero _
  add_csmul := fun z₁ z₂ a => by funext i; exact GaussInt.add_mul _ _ _
  csmul_add := fun z a b => by funext i; exact GaussInt.mul_add _ _ _
  mul_csmul := fun z₁ z₂ a => by funext i; exact GaussInt.mul_assoc _ _ _

theorem cVecFinSum_apply (n d : Nat) (f : Fin d → CVec n) (k : Fin n) :
    ZMod.finSum (cVecRMod n) d f k = gaussSum d (fun j => f j k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [ZMod.finSum, gaussSum]
    change addCVec (ZMod.finSum (cVecRMod n) d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (f ⟨d, Nat.lt_succ_self d⟩) k = _
    simp only [addCVec, ih]

def cStdBasis (n : Nat) (j : Fin n) : CVec n :=
  fun i => if i = j then GaussInt.one else GaussInt.zero

def cImagBasis (n : Nat) (j : Fin n) : CVec n :=
  fun i => if i = j then GaussInt.I else GaussInt.zero

def hermInner {n : Nat} (z w : CVec n) : GaussInt :=
  gaussSum n (fun j => GaussInt.mul (GaussInt.conj (z j)) (w j))

def cNormSq {n : Nat} (z : CVec n) : Int :=
  intSum n (fun j => (z j).normSq)

theorem hermInner_self_re {n : Nat} (z : CVec n) : (hermInner z z).re = cNormSq z := by
  unfold hermInner cNormSq
  rw [gaussSum_re]
  apply intSum_congr
  intro j
  rw [GaussInt.conj_mul_self]
  rfl

theorem hermInner_self_im {n : Nat} (z : CVec n) : (hermInner z z).im = 0 := by
  unfold hermInner
  rw [gaussSum_im]
  rw [intSum_congr (g := fun _ => 0)]
  · exact intSum_zero_fn n
  · intro j
    rw [GaussInt.conj_mul_self]
    rfl

theorem cNormSq_nonneg {n : Nat} (z : CVec n) : 0 ≤ cNormSq z :=
  intSum_nonneg (fun j => GaussInt.normSq_nonneg (z j))

theorem cNormSq_eq_zero_iff {n : Nat} (z : CVec n) : cNormSq z = 0 ↔ z = zeroCVec n := by
  unfold cNormSq
  rw [intSum_eq_zero_iff_of_nonneg (fun j => GaussInt.normSq_nonneg (z j))]
  constructor
  · intro hall
    funext j
    exact (GaussInt.normSq_eq_zero_iff (z j)).mp (hall j)
  · intro hz j
    rw [hz]
    rfl

theorem cNormSq_pos {n : Nat} {z : CVec n} (hz : z ≠ zeroCVec n) : 0 < cNormSq z := by
  have hnn := cNormSq_nonneg z
  have hnz : cNormSq z ≠ 0 := fun h0 => hz ((cNormSq_eq_zero_iff z).mp h0)
  omega

theorem cNormSq_cSmul {n : Nat} (c : GaussInt) (z : CVec n) :
    cNormSq (cSmulCVec c z) = c.normSq * cNormSq z := by
  unfold cNormSq cSmulCVec
  rw [← intSum_mul_left]
  apply intSum_congr
  intro j
  simp only [GaussInt.normSq, GaussInt.mul]
  have h1 : (c.re * (z j).re - c.im * (z j).im) * (c.re * (z j).re - c.im * (z j).im) +
      (c.re * (z j).im + c.im * (z j).re) * (c.re * (z j).im + c.im * (z j).re) =
      (c.re * c.re + c.im * c.im) * ((z j).re * (z j).re + (z j).im * (z j).im) := by
    simp [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
          Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  exact h1

abbrev CMat (n : Nat) := Fin n → Fin n → GaussInt

def zeroCMat (n : Nat) : CMat n := fun _ _ => GaussInt.zero
def addCMat {n : Nat} (A B : CMat n) : CMat n := fun i j => GaussInt.add (A i j) (B i j)
def negCMat {n : Nat} (A : CMat n) : CMat n := fun i j => GaussInt.neg (A i j)
def rSmulCMat {n : Nat} (c : Int) (A : CMat n) : CMat n :=
  fun i j => GaussInt.mul (GaussInt.ofInt c) (A i j)

def cMatRMod (n : Nat) : ZMod (CMat n) where
  zero := zeroCMat n
  add := addCMat
  neg := negCMat
  smul := rSmulCMat
  add_assoc := fun a b c => by funext i j; exact GaussInt.add_assoc _ _ _
  add_comm := fun a b => by funext i j; exact GaussInt.add_comm _ _
  zero_add := fun a => by funext i j; exact GaussInt.zero_add _
  add_zero := fun a => by funext i j; exact GaussInt.add_zero _
  add_left_neg := fun a => by funext i j; exact GaussInt.add_left_neg _
  one_smul := fun a => by funext i j; exact GaussInt.one_mul _
  zero_smul := fun a => by funext i j; exact GaussInt.zero_mul _
  smul_zero := fun c => by funext i j; exact GaussInt.mul_zero _
  add_smul := fun c₁ c₂ a => by
    funext i j
    have h : GaussInt.ofInt (c₁ + c₂) = GaussInt.add (GaussInt.ofInt c₁) (GaussInt.ofInt c₂) := by
      ext <;> simp [GaussInt.ofInt, GaussInt.add]
    simp only [rSmulCMat, addCMat]
    rw [h, GaussInt.add_mul]
  smul_add := fun c a b => by funext i j; exact GaussInt.mul_add _ _ _
  mul_smul := fun c₁ c₂ a => by
    funext i j
    have h : GaussInt.ofInt (c₁ * c₂) = GaussInt.mul (GaussInt.ofInt c₁) (GaussInt.ofInt c₂) := by
      ext <;> simp [GaussInt.ofInt, GaussInt.mul]
    simp only [rSmulCMat]
    rw [h, GaussInt.mul_assoc]

def IsHermitian {n : Nat} (A : CMat n) : Prop :=
  ∀ i j, A j i = GaussInt.conj (A i j)

def cMatVec {n : Nat} (A : CMat n) (z : CVec n) : CVec n :=
  fun i => gaussSum n (fun j => GaussInt.mul (A i j) (z j))

def cDiagMat {n : Nat} (eigs : Fin n → Int) : CMat n :=
  fun i j => if i = j then GaussInt.ofInt (eigs i) else GaussInt.zero

theorem cDiagMat_isHermitian {n : Nat} (eigs : Fin n → Int) : IsHermitian (cDiagMat eigs) := by
  intro i j
  unfold cDiagMat
  by_cases h : i = j
  · subst h; simp [GaussInt.conj, GaussInt.ofInt]
  · have h' : j ≠ i := fun heq => h heq.symm
    simp [h, h', GaussInt.conj, GaussInt.zero]

theorem gaussSum_conj (d : Nat) (f : Fin d → GaussInt) :
    GaussInt.conj (gaussSum d f) = gaussSum d (fun i => GaussInt.conj (f i)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp [gaussSum, GaussInt.conj_add, ih]

theorem gaussSum_mul_left (d : Nat) (c : GaussInt) (f : Fin d → GaussInt) :
    gaussSum d (fun i => GaussInt.mul c (f i)) = GaussInt.mul c (gaussSum d f) := by
  induction d with
  | zero => simp [gaussSum, GaussInt.mul_zero]
  | succ d ih =>
    simp only [gaussSum]
    rw [ih, GaussInt.mul_add]

theorem gaussSum_mul_right (d : Nat) (f : Fin d → GaussInt) (c : GaussInt) :
    gaussSum d (fun i => GaussInt.mul (f i) c) = GaussInt.mul (gaussSum d f) c := by
  induction d with
  | zero => simp [gaussSum, GaussInt.zero_mul]
  | succ d ih =>
    simp only [gaussSum]
    rw [ih, GaussInt.add_mul]

/-- Hermitian quadratic forms are purely real: `Im ⟨z, A z⟩ = 0` whenever `A* = A`. -/
theorem hermInner_cMatVec_im_zero {n : Nat} {A : CMat n} (hA : IsHermitian A) (z : CVec n) :
    (hermInner z (cMatVec A z)).im = 0 := by
  have hconj : GaussInt.conj (hermInner z (cMatVec A z)) = hermInner z (cMatVec A z) := by
    unfold hermInner cMatVec
    rw [gaussSum_conj]
    have h1 : gaussSum n (fun i => GaussInt.conj (GaussInt.mul (GaussInt.conj (z i))
        (gaussSum n (fun j => GaussInt.mul (A i j) (z j))))) =
        gaussSum n (fun i => gaussSum n (fun j =>
          GaussInt.mul (GaussInt.conj (z j)) (GaussInt.mul (A j i) (z i)))) := by
      apply gaussSum_congr
      intro i
      rw [GaussInt.conj_mul, GaussInt.conj_conj, gaussSum_conj, ← gaussSum_mul_right]
      apply gaussSum_congr
      intro j
      rw [GaussInt.conj_mul, ← hA i j, GaussInt.mul_assoc]
    rw [h1, gaussSum_comm]
    apply gaussSum_congr
    intro j
    rw [← gaussSum_mul_left]
  have him : -(hermInner z (cMatVec A z)).im = (hermInner z (cMatVec A z)).im :=
    congrArg GaussInt.im hconj
  omega

/-- Exact complex Rayleigh quotient `R_A(z) = Re⟨z, A z⟩ / ‖z‖²` for `z ≠ 0`. -/
def cRayleigh {n : Nat} (A : CMat n) (z : CVec n) (hz : z ≠ zeroCVec n) : RatVal :=
  ⟨(hermInner z (cMatVec A z)).re, cNormSq z, cNormSq_pos hz⟩

/-- Complex projective equivalence `[z] = [w]` in `ℂℙ^{n-1}`. -/
def CProjEquiv {n : Nat} (z w : CVec n) : Prop :=
  ∃ a b : GaussInt, a ≠ GaussInt.zero ∧ b ≠ GaussInt.zero ∧ cSmulCVec a z = cSmulCVec b w

theorem cRayleigh_cProjInvar {n : Nat} (A : CMat n) {z w : CVec n}
    (hz : z ≠ zeroCVec n) (hw : w ≠ zeroCVec n) (hp : CProjEquiv z w) :
    RatVal.Eq (cRayleigh A z hz) (cRayleigh A w hw) := by
  rcases hp with ⟨a, b, ha, _hb, hab⟩
  unfold RatVal.Eq cRayleigh
  simp only
  have hscale : ∀ (c : GaussInt) (u : CVec n),
      hermInner (cSmulCVec c u) (cMatVec A (cSmulCVec c u)) =
        GaussInt.mul (GaussInt.ofInt c.normSq) (hermInner u (cMatVec A u)) := by
    intro c u
    unfold hermInner cMatVec cSmulCVec
    rw [← gaussSum_mul_left]
    apply gaussSum_congr
    intro i
    have hrow : gaussSum n (fun j => GaussInt.mul (A i j) (GaussInt.mul c (u j))) =
        GaussInt.mul c (gaussSum n (fun j => GaussInt.mul (A i j) (u j))) := by
      rw [← gaussSum_mul_left]
      apply gaussSum_congr
      intro j
      rw [← GaussInt.mul_assoc, GaussInt.mul_comm (A i j) c, GaussInt.mul_assoc]
    rw [hrow, GaussInt.conj_mul]
    calc GaussInt.mul (GaussInt.mul (GaussInt.conj (u i)) (GaussInt.conj c))
            (GaussInt.mul c (gaussSum n (fun j => GaussInt.mul (A i j) (u j))))
        = GaussInt.mul (GaussInt.conj (u i))
            (GaussInt.mul (GaussInt.mul (GaussInt.conj c) c)
              (gaussSum n (fun j => GaussInt.mul (A i j) (u j)))) := by
          simp [GaussInt.mul_assoc]
      _ = GaussInt.mul (GaussInt.ofInt c.normSq)
            (GaussInt.mul (GaussInt.conj (u i))
              (gaussSum n (fun j => GaussInt.mul (A i j) (u j)))) := by
          rw [GaussInt.conj_mul_self, ← GaussInt.mul_assoc,
              GaussInt.mul_comm (GaussInt.conj (u i)) (GaussInt.ofInt c.normSq),
              GaussInt.mul_assoc]
  have hquad_re : a.normSq * (hermInner z (cMatVec A z)).re =
      b.normSq * (hermInner w (cMatVec A w)).re := by
    have h1 := congrArg GaussInt.re (hscale a z)
    have h2 := congrArg GaussInt.re (hscale b w)
    rw [hab] at h1
    rw [h1] at h2
    simp [GaussInt.mul, GaussInt.ofInt] at h2
    exact h2
  have hnorm : a.normSq * cNormSq z = b.normSq * cNormSq w := by
    rw [← cNormSq_cSmul, hab, cNormSq_cSmul]
  have ha_ns_ne : a.normSq ≠ 0 := fun h0 => ha ((GaussInt.normSq_eq_zero_iff a).mp h0)
  apply Int.eq_of_mul_eq_mul_left ha_ns_ne
  calc a.normSq * ((hermInner z (cMatVec A z)).re * cNormSq w)
      = (a.normSq * (hermInner z (cMatVec A z)).re) * cNormSq w := by rw [← Int.mul_assoc]
    _ = (b.normSq * (hermInner w (cMatVec A w)).re) * cNormSq w := by rw [hquad_re]
    _ = (hermInner w (cMatVec A w)).re * (b.normSq * cNormSq w) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (hermInner w (cMatVec A w)).re * (a.normSq * cNormSq z) := by rw [← hnorm]
    _ = a.normSq * ((hermInner w (cMatVec A w)).re * cNormSq z) := by
        simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-! ## 5. Theorem 1B: Positive Linear-Cone Characterization (Complex Hermitian Case) -/

def ComplexEigenspace {n : Nat} (A : CMat n) (lam : Int) (z : CVec n) : Prop :=
  cMatVec A z = cSmulCVec (GaussInt.ofInt lam) z

theorem cMatVec_cDiagMat {n : Nat} (eigs : Fin n → Int) (z : CVec n) (i : Fin n) :
    cMatVec (cDiagMat eigs) z i = GaussInt.mul (GaussInt.ofInt (eigs i)) (z i) := by
  unfold cMatVec cDiagMat
  ext
  · rw [gaussSum_re]
    have hcong : intSum n (fun j => (GaussInt.mul (if i = j then GaussInt.ofInt (eigs i) else GaussInt.zero) (z j)).re) =
        intSum n (fun j => if j = i then (GaussInt.mul (GaussInt.ofInt (eigs j)) (z j)).re else 0) := by
      apply intSum_congr
      intro j
      by_cases h : j = i
      · subst h; simp
      · have h' : i ≠ j := fun heq => h heq.symm
        simp [h, h', GaussInt.mul, GaussInt.zero]
    rw [hcong, intSum_ite_eq]
  · rw [gaussSum_im]
    have hcong : intSum n (fun j => (GaussInt.mul (if i = j then GaussInt.ofInt (eigs i) else GaussInt.zero) (z j)).im) =
        intSum n (fun j => if j = i then (GaussInt.mul (GaussInt.ofInt (eigs j)) (z j)).im else 0) := by
      apply intSum_congr
      intro j
      by_cases h : j = i
      · subst h; simp
      · have h' : i ≠ j := fun heq => h heq.symm
        simp [h, h', GaussInt.mul, GaussInt.zero]
    rw [hcong, intSum_ite_eq]

theorem cDiag_spectral_gap {n : Nat} (eigs : Fin n → Int) (lamMax : Int) (z : CVec n) :
    lamMax * cNormSq z - (hermInner z (cMatVec (cDiagMat eigs) z)).re =
      intSum n (fun i => (lamMax - eigs i) * (z i).normSq) := by
  unfold cNormSq hermInner
  rw [gaussSum_re, ← intSum_mul_left]
  have hsub : ∀ d : Nat, (f g : Fin d → Int) →
      intSum d f - intSum d g = intSum d (fun i => f i - g i) := by
    intro d f g
    induction d with
    | zero => rfl
    | succ d ih =>
      simp only [intSum]
      have := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                 (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega
  rw [hsub]
  apply intSum_congr
  intro i
  rw [cMatVec_cDiagMat]
  simp only [GaussInt.conj, GaussInt.mul, GaussInt.ofInt, GaussInt.normSq]
  have : lamMax * ((z i).re * (z i).re + (z i).im * (z i).im) -
      ((z i).re * (eigs i * (z i).re - 0 * (z i).im) -
       (-(z i).im) * (eigs i * (z i).im + 0 * (z i).re)) =
      (lamMax - eigs i) * ((z i).re * (z i).re + (z i).im * (z i).im) := by
    rw [Int.sub_mul]
    simp [Int.mul_add, Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  exact this

theorem cRayleigh_le_max {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) {z : CVec n} (hz : z ≠ zeroCVec n) :
    RatVal.Le (cRayleigh (cDiagMat eigs) z hz) (RatVal.ofInt lamMax) := by
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  unfold RatVal.Le cRayleigh RatVal.ofInt
  simp only [Int.mul_one]
  have hgap := cDiag_spectral_gap eigs lamMax z
  have hnonneg : 0 ≤ intSum n (fun i => (lamMax - eigs i) * (z i).normSq) := by
    apply intSum_nonneg
    intro i
    have hns := GaussInt.normSq_nonneg (z i)
    by_cases hi : i.val < m
    · rw [h_eq i hi]; simp
    · have hlt_i := h_lt i (by omega)
      exact Int.mul_nonneg (by omega) hns
  omega

theorem cEigvec_diag_iff_vanish_above {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) (z : CVec n) :
    ComplexEigenspace (cDiagMat eigs) lamMax z ↔ ∀ i : Fin n, m ≤ i.val → z i = GaussInt.zero := by
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  unfold ComplexEigenspace
  constructor
  · intro heig i hi
    have hi_eq := congrFun heig i
    rw [cMatVec_cDiagMat] at hi_eq
    simp only [cSmulCVec] at hi_eq
    have hre := congrArg GaussInt.re hi_eq
    have him := congrArg GaussInt.im hi_eq
    simp [GaussInt.mul, GaussInt.ofInt] at hre him
    have hne : lamMax - eigs i ≠ 0 := by have := h_lt i hi; omega
    have hd_re : (lamMax - eigs i) * (z i).re = 0 := by rw [Int.sub_mul]; omega
    have hd_im : (lamMax - eigs i) * (z i).im = 0 := by rw [Int.sub_mul]; omega
    have hz_re : (z i).re = 0 := by
      cases Int.mul_eq_zero.mp hd_re with
      | inl h0 => exact absurd h0 hne
      | inr h0 => exact h0
    have hz_im : (z i).im = 0 := by
      cases Int.mul_eq_zero.mp hd_im with
      | inl h0 => exact absurd h0 hne
      | inr h0 => exact h0
    ext <;> simp [GaussInt.zero, hz_re, hz_im]
  · intro hvan
    funext i
    rw [cMatVec_cDiagMat]
    simp only [cSmulCVec]
    by_cases hi : i.val < m
    · rw [h_eq i hi]
    · rw [hvan i (by omega), GaussInt.mul_zero, GaussInt.mul_zero]

theorem cRayleigh_eq_max_iff_eigvec {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) {z : CVec n} (hz : z ≠ zeroCVec n) :
    RatVal.Eq (cRayleigh (cDiagMat eigs) z hz) (RatVal.ofInt lamMax) ↔
      ComplexEigenspace (cDiagMat eigs) lamMax z := by
  rw [cEigvec_diag_iff_vanish_above hspec z]
  rcases hspec with ⟨_, _, h_eq, h_lt⟩
  unfold RatVal.Eq cRayleigh RatVal.ofInt
  simp only [Int.mul_one]
  have hgap := cDiag_spectral_gap eigs lamMax z
  have hterm_nonneg : ∀ i : Fin n, 0 ≤ (lamMax - eigs i) * (z i).normSq := by
    intro i
    by_cases hi : i.val < m
    · rw [h_eq i hi]; simp
    · exact Int.mul_nonneg (by have := h_lt i (by omega); omega) (GaussInt.normSq_nonneg (z i))
  constructor
  · intro heq i hi
    have hsum0 : intSum n (fun j => (lamMax - eigs j) * (z j).normSq) = 0 := by omega
    have hall := (intSum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum0 i
    have hne : lamMax - eigs i ≠ 0 := by have := h_lt i hi; omega
    cases Int.mul_eq_zero.mp hall with
    | inl h0 => exact absurd h0 hne
    | inr hns0 => exact (GaussInt.normSq_eq_zero_iff (z i)).mp hns0
  · intro hvan
    have hsum0 : intSum n (fun j => (lamMax - eigs j) * (z j).normSq) = 0 := by
      apply (intSum_eq_zero_iff_of_nonneg hterm_nonneg).mpr
      intro j
      by_cases hj : j.val < m
      · rw [h_eq j hj]; simp
      · rw [hvan j (by omega)]; simp [GaussInt.normSq, GaussInt.zero]
    omega

/-- As a complex (`ℤ[i]`) module, the complex eigenspace has exact complex dimension `m`. -/
theorem complexEigenspace_hasCDim_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    CMod.HasCDim (cVecCMod n) (ComplexEigenspace (cDiagMat eigs) lamMax) m := by
  have hmn : m ≤ n := hspec.2.1
  let b : Fin m → CVec n := fun j => cStdBasis n ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩
  let coord : CVec n → Fin m → GaussInt := fun z j => z ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩
  apply CMod.hasCDim_of_coords (cVecCMod n) b coord
  · intro j
    rw [cEigvec_diag_iff_vanish_above hspec]
    intro i hi
    simp only [b, cStdBasis]
    have hne : i ≠ ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp at hv; omega
    simp [hne]
  · intro c j
    unfold coord CMod.clinComb
    simp only [cVecCMod]
    rw [cVecFinSum_apply]
    ext
    · rw [gaussSum_re]
      have hcong : intSum m (fun k => (cSmulCVec (c k) (b k) ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩).re) =
          intSum m (fun k => if k = j then (c k).re else 0) := by
        apply intSum_congr
        intro k
        simp only [cSmulCVec, b, cStdBasis]
        by_cases hkj : k = j
        · subst hkj; simp [GaussInt.mul_one]
        · have hne : (⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩ : Fin n) ≠
              ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
            intro heq; apply hkj; exact Fin.ext (congrArg Fin.val heq).symm
          simp [hkj, hne, GaussInt.mul, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
    · rw [gaussSum_im]
      have hcong : intSum m (fun k => (cSmulCVec (c k) (b k) ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩).im) =
          intSum m (fun k => if k = j then (c k).im else 0) := by
        apply intSum_congr
        intro k
        simp only [cSmulCVec, b, cStdBasis]
        by_cases hkj : k = j
        · subst hkj; simp [GaussInt.mul_one]
        · have hne : (⟨j.val, Nat.lt_of_lt_of_le j.isLt hmn⟩ : Fin n) ≠
              ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
            intro heq; apply hkj; exact Fin.ext (congrArg Fin.val heq).symm
          simp [hkj, hne, GaussInt.mul, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
  · intro _j; rfl
  · intro z hz
    have hvan := (cEigvec_diag_iff_vanish_above hspec z).mp hz
    funext i
    unfold CMod.clinComb coord
    simp only [cVecCMod]
    rw [cVecFinSum_apply]
    by_cases hi : i.val < m
    · let j₀ : Fin m := ⟨i.val, hi⟩
      ext
      · rw [gaussSum_re]
        have hcong : intSum m (fun k => (cSmulCVec (z ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k) i).re) =
            intSum m (fun k => if k = j₀ then (z i).re else 0) := by
          apply intSum_congr
          intro k
          simp only [cSmulCVec, b, cStdBasis]
          by_cases hkj : k = j₀
          · subst hkj
            have heq : i = ⟨j₀.val, Nat.lt_of_lt_of_le j₀.isLt hmn⟩ := Fin.ext rfl
            simp [← heq, GaussInt.mul_one]
          · have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
              intro heq; apply hkj; exact Fin.ext (congrArg Fin.val heq).symm
            simp [hkj, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
      · rw [gaussSum_im]
        have hcong : intSum m (fun k => (cSmulCVec (z ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k) i).im) =
            intSum m (fun k => if k = j₀ then (z i).im else 0) := by
          apply intSum_congr
          intro k
          simp only [cSmulCVec, b, cStdBasis]
          by_cases hkj : k = j₀
          · subst hkj
            have heq : i = ⟨j₀.val, Nat.lt_of_lt_of_le j₀.isLt hmn⟩ := Fin.ext rfl
            simp [← heq, GaussInt.mul_one]
          · have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
              intro heq; apply hkj; exact Fin.ext (congrArg Fin.val heq).symm
            simp [hkj, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
    · rw [hvan i (by omega)]
      ext
      · rw [gaussSum_re]
        have hcong : intSum m (fun k => (cSmulCVec (z ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k) i).re) =
            intSum m (fun _ => 0) := by
          apply intSum_congr
          intro k
          have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
      · rw [gaussSum_im]
        have hcong : intSum m (fun k => (cSmulCVec (z ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩) (b k) i).im) =
            intSum m (fun _ => 0) := by
          apply intSum_congr
          intro k
          have hne : i ≠ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hmn⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp [cSmulCVec, b, cStdBasis, hne, GaussInt.mul, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl

/-- As a real (`ℤ`) module, the complex eigenspace has exact real dimension `2m` (`≠ m` for all `m ≥ 1`). -/
theorem complexEigenspace_hasRDim_two_m {n : Nat} {eigs : Fin n → Int} {lamMax : Int} {m : Nat}
    (hspec : HasMaxMult eigs lamMax m) :
    ZMod.HasDim (cVecRMod n) (ComplexEigenspace (cDiagMat eigs) lamMax) (2 * m) := by
  have hmn : m ≤ n := hspec.2.1
  let b : Fin (2 * m) → CVec n := fun k =>
    let j : Fin n := ⟨k.val / 2, by omega⟩
    if k.val % 2 = 0 then cStdBasis n j else cImagBasis n j
  let coord : CVec n → Fin (2 * m) → Int := fun z k =>
    let j : Fin n := ⟨k.val / 2, by omega⟩
    if k.val % 2 = 0 then (z j).re else (z j).im
  apply ZMod.hasDim_of_coords (cVecRMod n) b coord
  · intro k
    rw [cEigvec_diag_iff_vanish_above hspec]
    intro i hi
    simp only [b]
    by_cases hmod : k.val % 2 = 0
    · simp only [hmod, ↓reduceIte, cStdBasis]
      have hne : i ≠ ⟨k.val / 2, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [hne]
    · simp only [hmod, ↓reduceIte, cImagBasis]
      have hne : i ≠ ⟨k.val / 2, by omega⟩ := by
        intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
      simp [hne]
  · intro c k
    dsimp only [coord]
    unfold ZMod.linComb
    by_cases hmod : k.val % 2 = 0
    · simp only [hmod, ↓reduceIte]
      rw [cVecFinSum_apply, gaussSum_re]
      have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul (c r) (b r) ⟨k.val / 2, by omega⟩).re) =
          intSum (2 * m) (fun r => if r = k then c r else 0) := by
        apply intSum_congr
        intro r
        simp only [cVecRMod, rSmulCVec, b]
        by_cases hr_mod : r.val % 2 = 0
        · simp only [hr_mod, ↓reduceIte, cStdBasis]
          by_cases hrk : r = k
          · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.one]
          · have hdiv_ne : (⟨k.val / 2, by omega⟩ : Fin n) ≠ ⟨r.val / 2, by omega⟩ := by
              intro heq
              have hv := congrArg Fin.val heq; simp at hv
              apply hrk
              ext; omega
            simp [hrk, hdiv_ne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hr_mod, ↓reduceIte, cImagBasis]
          have hrk : r ≠ k := by intro heq; subst heq; exact hr_mod hmod
          by_cases hdiv : (⟨k.val / 2, by omega⟩ : Fin n) = ⟨r.val / 2, by omega⟩
          · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
          · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
    · simp only [hmod, ↓reduceIte]
      rw [cVecFinSum_apply, gaussSum_im]
      have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul (c r) (b r) ⟨k.val / 2, by omega⟩).im) =
          intSum (2 * m) (fun r => if r = k then c r else 0) := by
        apply intSum_congr
        intro r
        simp only [cVecRMod, rSmulCVec, b]
        by_cases hr_mod : r.val % 2 = 0
        · simp only [hr_mod, ↓reduceIte, cStdBasis]
          have hrk : r ≠ k := by intro heq; subst heq; exact hmod hr_mod
          by_cases hdiv : (⟨k.val / 2, by omega⟩ : Fin n) = ⟨r.val / 2, by omega⟩
          · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one]
          · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        · simp only [hr_mod, ↓reduceIte, cImagBasis]
          by_cases hrk : r = k
          · subst hrk; simp [GaussInt.mul, GaussInt.ofInt, GaussInt.I]
          · have hdiv_ne : (⟨k.val / 2, by omega⟩ : Fin n) ≠ ⟨r.val / 2, by omega⟩ := by
              intro heq
              have hv := congrArg Fin.val heq; simp at hv
              apply hrk
              ext; omega
            simp [hrk, hdiv_ne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
      rw [hcong, intSum_ite_eq]
  · intro k
    simp only [coord, cVecRMod, zeroCVec, GaussInt.zero]
    by_cases hmod : k.val % 2 = 0 <;> simp [hmod]
  · intro z hz
    have hvan := (cEigvec_diag_iff_vanish_above hspec z).mp hz
    funext i
    unfold ZMod.linComb coord
    rw [cVecFinSum_apply]
    by_cases hi : i.val < m
    · let k_re : Fin (2 * m) := ⟨2 * i.val, by omega⟩
      let k_im : Fin (2 * m) := ⟨2 * i.val + 1, by omega⟩
      ext
      · rw [gaussSum_re]
        have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (z ⟨r.val / 2, by omega⟩).re else (z ⟨r.val / 2, by omega⟩).im) (b r) i).re) =
            intSum (2 * m) (fun r => if r = k_re then (z i).re else 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr_mod : r.val % 2 = 0
          · simp only [hr_mod, ↓reduceIte, cStdBasis]
            by_cases hrk : r = k_re
            · subst hrk
              have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i := by ext; simp
              simp [k_re, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one]
            · have hne : i ≠ ⟨r.val / 2, by omega⟩ := by
                intro heq
                have hv := congrArg Fin.val heq; simp at hv
                apply hrk; ext; simp [k_re]; omega
              simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          · simp only [hr_mod, ↓reduceIte, cImagBasis]
            have hrk : r ≠ k_re := by
              intro heq; subst heq; simp [k_re] at hr_mod
            by_cases hdiv : i = ⟨r.val / 2, by omega⟩
            · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
            · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
      · rw [gaussSum_im]
        have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (z ⟨r.val / 2, by omega⟩).re else (z ⟨r.val / 2, by omega⟩).im) (b r) i).im) =
            intSum (2 * m) (fun r => if r = k_im then (z i).im else 0) := by
          apply intSum_congr
          intro r
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr_mod : r.val % 2 = 0
          · simp only [hr_mod, ↓reduceIte, cStdBasis]
            have hrk : r ≠ k_im := by
              intro heq; subst heq; simp [k_im] at hr_mod
            by_cases hdiv : i = ⟨r.val / 2, by omega⟩
            · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.one]
            · simp [hrk, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
          · simp only [hr_mod, ↓reduceIte, cImagBasis]
            by_cases hrk : r = k_im
            · subst hrk
              have hdiv : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := by ext; simp; omega
              simp [k_im, hdiv, GaussInt.mul, GaussInt.ofInt, GaussInt.I]
            · have hne : i ≠ ⟨r.val / 2, by omega⟩ := by
                intro heq
                have hv := congrArg Fin.val heq; simp at hv
                apply hrk; ext; simp [k_im]; omega
              simp [hrk, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_ite_eq]
    · rw [hvan i (by omega)]
      ext
      · rw [gaussSum_re]
        have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (z ⟨r.val / 2, by omega⟩).re else (z ⟨r.val / 2, by omega⟩).im) (b r) i).re) =
            intSum (2 * m) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : i ≠ ⟨r.val / 2, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr_mod : r.val % 2 = 0 <;>
            simp [hr_mod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl
      · rw [gaussSum_im]
        have hcong : intSum (2 * m) (fun r => ((cVecRMod n).smul
            (if r.val % 2 = 0 then (z ⟨r.val / 2, by omega⟩).re else (z ⟨r.val / 2, by omega⟩).im) (b r) i).im) =
            intSum (2 * m) (fun _ => 0) := by
          apply intSum_congr
          intro r
          have hne : i ≠ ⟨r.val / 2, by omega⟩ := by
            intro heq; have hv := congrArg Fin.val heq; simp at hv; omega
          simp only [cVecRMod, rSmulCVec, b]
          by_cases hr_mod : r.val % 2 = 0 <;>
            simp [hr_mod, cStdBasis, cImagBasis, hne, GaussInt.mul, GaussInt.ofInt, GaussInt.zero]
        rw [hcong, intSum_zero_fn]; rfl

end Conjecture00000007165
