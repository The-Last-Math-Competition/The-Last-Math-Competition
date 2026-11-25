import Conjecture00000004759.Basic

/-
  Conjecture 00000004759 — Concrete Operator-Valued Fock Space Model over `Mat2 Int`
  Core Lean 4.19.0 (zero external dependencies).

  Constructs:
  1. `Mat2 R`: `2 × 2` matrices over any `AssocRing R`, proved to form an `AssocRing`.
  2. `FockOp`: `ℤ`-linear operators on the two-generator full Fock space `List Bool → Int`,
     with creation/annihilation operators `createOp c`, `annihilateOp c`, semicirculars
     `semiOp c`, and vacuum expectation `phi : FockOp → Int`.
  3. All-order Voiculescu scalar freeness of `InColor false` and `InColor true` (`scalar_isBFree`),
     and its matrix lift `mat2FockSpace : OpValProbSpace (Mat2 FockOp) (Mat2 Int)` with
     proved all-order `B`-freeness (`mat2Fock_isBFree`)!
-/

namespace Conjecture00000004759

/-- `2 × 2` matrices over `R`. -/
structure Mat2 (R : Type u) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R
  deriving DecidableEq, Repr

namespace Mat2

@[ext]
theorem ext {R : Type u} {M N : Mat2 R}
    (h11 : M.a11 = N.a11) (h12 : M.a12 = N.a12)
    (h21 : M.a21 = N.a21) (h22 : M.a22 = N.a22) : M = N := by
  cases M; cases N; simp_all

section RingOps
variable {R : Type u} [AssocRing R]

def zeroMat : Mat2 R := ⟨0, 0, 0, 0⟩
def oneMat : Mat2 R := ⟨1, 0, 0, 1⟩
def addMat (M N : Mat2 R) : Mat2 R :=
  ⟨M.a11 + N.a11, M.a12 + N.a12, M.a21 + N.a21, M.a22 + N.a22⟩
def negMat (M : Mat2 R) : Mat2 R := ⟨-M.a11, -M.a12, -M.a21, -M.a22⟩
def subMat (M N : Mat2 R) : Mat2 R :=
  ⟨M.a11 - N.a11, M.a12 - N.a12, M.a21 - N.a21, M.a22 - N.a22⟩
def mulMat (M N : Mat2 R) : Mat2 R :=
  ⟨M.a11 * N.a11 + M.a12 * N.a21,
   M.a11 * N.a12 + M.a12 * N.a22,
   M.a21 * N.a11 + M.a22 * N.a21,
   M.a21 * N.a12 + M.a22 * N.a22⟩

private theorem four_add_rearrange (x₁ x₂ y₁ y₂ : R) :
    (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := by
  rw [AssocRing.add_assoc x₁ x₂ (y₁ + y₂),
      ← AssocRing.add_assoc x₂ y₁ y₂,
      AssocRing.add_comm x₂ y₁,
      AssocRing.add_assoc y₁ x₂ y₂,
      ← AssocRing.add_assoc x₁ y₁ (x₂ + y₂)]

instance : AssocRing (Mat2 R) where
  zero := zeroMat
  one := oneMat
  add := addMat
  sub := subMat
  neg := negMat
  mul := mulMat
  add_assoc a b c := by
    ext <;> exact AssocRing.add_assoc _ _ _
  add_comm a b := by
    ext <;> exact AssocRing.add_comm _ _
  zero_add a := by
    ext <;> exact AssocRing.zero_add _
  add_zero a := by
    ext <;> exact AssocRing.add_zero _
  add_left_neg a := by
    ext <;> exact AssocRing.add_left_neg _
  sub_eq_add_neg a b := by
    ext <;> exact AssocRing.sub_eq_add_neg _ _
  one_mul a := by
    change mulMat oneMat a = a
    ext <;> simp [oneMat, mulMat, one_mul_ring, zero_mul_ring,
      add_zero_ring, zero_add_ring]
  mul_one a := by
    change mulMat a oneMat = a
    ext <;> simp [oneMat, mulMat, mul_one_ring, mul_zero_ring,
      add_zero_ring, zero_add_ring]
  left_distrib a b c := by
    change mulMat a (addMat b c) = addMat (mulMat a b) (mulMat a c)
    ext <;> {
      dsimp [mulMat, addMat]
      rw [AssocRing.left_distrib, AssocRing.left_distrib, four_add_rearrange]
    }
  right_distrib a b c := by
    change mulMat (addMat a b) c = addMat (mulMat a c) (mulMat b c)
    ext <;> {
      dsimp [mulMat, addMat]
      rw [AssocRing.right_distrib, AssocRing.right_distrib, four_add_rearrange]
    }
  mul_assoc a b c := by
    change mulMat (mulMat a b) c = mulMat a (mulMat b c)
    ext <;> {
      dsimp [mulMat]
      rw [AssocRing.right_distrib, AssocRing.right_distrib,
          AssocRing.left_distrib, AssocRing.left_distrib,
          AssocRing.mul_assoc, AssocRing.mul_assoc,
          AssocRing.mul_assoc, AssocRing.mul_assoc,
          four_add_rearrange]
    }

def E11 : Mat2 R := ⟨1, 0, 0, 0⟩
def E12 : Mat2 R := ⟨0, 1, 0, 0⟩
def E21 : Mat2 R := ⟨0, 0, 1, 0⟩
def E22 : Mat2 R := ⟨0, 0, 0, 1⟩
def I2 : Mat2 R := ⟨1, 0, 0, 1⟩
def sigmaX : Mat2 R := ⟨0, 1, 1, 0⟩
def diagMat (d₁ d₂ : R) : Mat2 R := ⟨d₁, 0, 0, d₂⟩

end RingOps
end Mat2

/-! ### Full Fock Space Over Two Orthogonal Generators (`false`, `true`) -/

abbrev FockVec := List Bool → Int

def vacVec : FockVec
  | [] => 1
  | _ :: _ => 0

/-- `ℤ`-linear endomorphisms of `FockVec`. -/
structure FockOp where
  fn : FockVec → FockVec
  map_zero : fn (fun _ => 0) = fun _ => 0
  map_add : ∀ u v : FockVec, fn (fun w => u w + v w) = fun w => fn u w + fn v w
  map_smul : ∀ (c : Int) (u : FockVec), fn (fun w => c * u w) = fun w => c * fn u w

namespace FockOp

@[ext]
theorem ext {T₁ T₂ : FockOp} (h : ∀ v w, T₁.fn v w = T₂.fn v w) : T₁ = T₂ := by
  cases T₁; cases T₂; simp only [mk.injEq]
  funext v w; exact h v w

def constOp (c : Int) : FockOp where
  fn v w := c * v w
  map_zero := by funext w; exact Int.mul_zero c
  map_add u v := by funext w; exact Int.mul_add c (u w) (v w)
  map_smul d u := by
    funext w
    rw [← Int.mul_assoc c d (u w), Int.mul_comm c d, Int.mul_assoc d c (u w)]

instance : AssocRing FockOp where
  zero := constOp 0
  one := {
    fn := fun v => v
    map_zero := rfl
    map_add := fun _ _ => rfl
    map_smul := fun _ _ => rfl
  }
  add T₁ T₂ := {
    fn := fun v w => T₁.fn v w + T₂.fn v w
    map_zero := by funext w; simp [T₁.map_zero, T₂.map_zero]
    map_add := fun u v => by
      funext w
      have h1 := congrFun (T₁.map_add u v) w
      have h2 := congrFun (T₂.map_add u v) w
      omega
    map_smul := fun c u => by
      funext w
      have h1 := congrFun (T₁.map_smul c u) w
      have h2 := congrFun (T₂.map_smul c u) w
      rw [h1, h2, Int.mul_add]
  }
  neg T := {
    fn := fun v w => -(T.fn v w)
    map_zero := by funext w; simp [T.map_zero]
    map_add := fun u v => by
      funext w
      have h1 := congrFun (T.map_add u v) w
      omega
    map_smul := fun c u => by
      funext w
      have h1 := congrFun (T.map_smul c u) w
      rw [h1, Int.mul_neg]
  }
  sub T₁ T₂ := {
    fn := fun v w => T₁.fn v w - T₂.fn v w
    map_zero := by funext w; simp [T₁.map_zero, T₂.map_zero]
    map_add := fun u v => by
      funext w
      have h1 := congrFun (T₁.map_add u v) w
      have h2 := congrFun (T₂.map_add u v) w
      omega
    map_smul := fun c u => by
      funext w
      have h1 := congrFun (T₁.map_smul c u) w
      have h2 := congrFun (T₂.map_smul c u) w
      rw [h1, h2, Int.mul_sub]
  }
  mul T₁ T₂ := {
    fn := fun v => T₁.fn (T₂.fn v)
    map_zero := by rw [T₂.map_zero, T₁.map_zero]
    map_add := fun u v => by rw [T₂.map_add, T₁.map_add]
    map_smul := fun c u => by rw [T₂.map_smul, T₁.map_smul]
  }
  add_assoc a b c := by ext v w; exact Int.add_assoc _ _ _
  add_comm a b := by ext v w; exact Int.add_comm _ _
  zero_add a := by ext v w; change 0 * v w + a.fn v w = a.fn v w; omega
  add_zero a := by ext v w; change a.fn v w + 0 * v w = a.fn v w; omega
  add_left_neg a := by ext v w; change -(a.fn v w) + a.fn v w = 0 * v w; omega
  sub_eq_add_neg a b := by ext v w; exact Int.sub_eq_add_neg
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  left_distrib a b c := by ext v w; exact congrFun (a.map_add (b.fn v) (c.fn v)) w
  right_distrib _ _ _ := rfl

/-- Creation operator `ℓ_c^*` prepending letter `c`. -/
def createFn (c : Bool) (v : FockVec) : FockVec
  | [] => 0
  | b :: rest => if b == c then v rest else 0

def createOp (c : Bool) : FockOp where
  fn := createFn c
  map_zero := by funext w; cases w <;> simp [createFn]
  map_add u v := by
    funext w; cases w with
    | nil => simp [createFn]
    | cons b rest => by_cases h : (b == c) = true <;> simp [createFn, h]
  map_smul d u := by
    funext w; cases w with
    | nil => simp [createFn]
    | cons b rest => by_cases h : (b == c) = true <;> simp [createFn, h]

/-- Annihilation operator `ℓ_c` stripping leading letter `c`. -/
def annihilateOp (c : Bool) : FockOp where
  fn v rest := v (c :: rest)
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl

/-- Standard `(0, 1)`-semicircular operator `s_c = ℓ_c + ℓ_c^*`. -/
def semiOp (c : Bool) : FockOp := annihilateOp c + createOp c

/-- Vacuum state expectation `φ(T) = ⟨Ω, T Ω⟩`. -/
def phi (T : FockOp) : Int := T.fn vacVec []

theorem phi_zero : phi 0 = 0 := by change 0 * vacVec [] = 0; omega
theorem phi_one : phi 1 = 1 := rfl
theorem phi_const (c : Int) : phi (constOp c) = c := by
  change c * 1 = c; exact Int.mul_one c
theorem phi_add (T₁ T₂ : FockOp) : phi (T₁ + T₂) = phi T₁ + phi T₂ := rfl
theorem phi_neg (T : FockOp) : phi (-T) = -(phi T) := rfl

theorem phi_bimod (b₁ b₂ : Int) (T : FockOp) :
    phi (constOp b₁ * T * constOp b₂) = b₁ * phi T * b₂ := by
  unfold phi
  have h1 : (constOp b₁ * T * constOp b₂).fn vacVec [] =
      b₁ * (T * constOp b₂).fn vacVec [] := rfl
  have h2 : (T * constOp b₂).fn vacVec [] = b₂ * T.fn vacVec [] :=
    congrFun (T.map_smul b₂ vacVec) []
  rw [h1, h2]
  rw [Int.mul_assoc b₁ (T.fn vacVec []) b₂, Int.mul_comm (T.fn vacVec []) b₂,
      ← Int.mul_assoc b₁ b₂ (T.fn vacVec [])]

theorem constOp_zero : constOp 0 = (0 : FockOp) := rfl
theorem constOp_one : constOp 1 = (1 : FockOp) := by
  ext v w; exact Int.one_mul (v w)
theorem constOp_add (a b : Int) : constOp (a + b) = constOp a + constOp b := by
  ext v w; exact Int.add_mul a b (v w)
theorem constOp_neg (a : Int) : constOp (-a) = -(constOp a) := by
  ext v w; exact Int.neg_mul a (v w)
theorem constOp_mul_hom (a b : Int) : constOp (a * b) = constOp a * constOp b := by
  ext v w; exact Int.mul_assoc a b (v w)

/-- Scalar probability space `(FockOp, Int, constOp, phi)`. -/
def scalarFockSpace : OpValProbSpace FockOp Int where
  iota := constOp
  iota_zero := constOp_zero
  iota_one := constOp_one
  iota_add := constOp_add
  iota_neg := constOp_neg
  iota_mul := constOp_mul_hom
  exp := phi
  exp_zero := phi_zero
  exp_add := phi_add
  exp_neg := phi_neg
  exp_iota := phi_const
  exp_bimod := phi_bimod

/-! ### All-Order Scalar Freeness of `InColor false` and `InColor true` -/

/-- Subalgebra of `FockOp` generated by scalars, `createOp c`, and `annihilateOp c`. -/
inductive InColor (c : Bool) : FockOp → Prop
  | const (n : Int) : InColor c (constOp n)
  | create : InColor c (createOp c)
  | annihilate : InColor c (annihilateOp c)
  | add {x y} : InColor c x → InColor c y → InColor c (x + y)
  | neg {x} : InColor c x → InColor c (-x)
  | mul {x y} : InColor c x → InColor c y → InColor c (x * y)

theorem inColor_isSubalgebra (c : Bool) : IsSubalgebra scalarFockSpace (InColor c) where
  has_iota := InColor.const
  has_add := InColor.add
  has_neg := InColor.neg
  has_mul := InColor.mul

theorem inColor_semiOp (c : Bool) : InColor c (semiOp c) :=
  InColor.add InColor.annihilate InColor.create

/-- Number of leading copies of `c` at the front of `w`. -/
def leadCount (c : Bool) : List Bool → Nat
  | [] => 0
  | b :: ws => if b == c then leadCount c ws + 1 else 0

/-- Remainder of `w` after stripping all leading copies of `c`. -/
def leadRest (c : Bool) : List Bool → List Bool
  | [] => []
  | b :: ws => if b == c then leadRest c ws else b :: ws

theorem leadCount_cons_same (c : Bool) (ws : List Bool) :
    leadCount c (c :: ws) = leadCount c ws + 1 := by
  simp [leadCount]

theorem leadRest_cons_same (c : Bool) (ws : List Bool) :
    leadRest c (c :: ws) = leadRest c ws := by
  simp [leadRest]

theorem leadCount_replicate (c : Bool) : ∀ k : Nat, leadCount c (List.replicate k c) = k
  | 0 => rfl
  | k + 1 => by simp [List.replicate, leadCount, leadCount_replicate c k]

theorem leadRest_replicate (c : Bool) : ∀ k : Nat, leadRest c (List.replicate k c) = []
  | 0 => rfl
  | k + 1 => by simp [List.replicate, leadRest, leadRest_replicate c k]

private theorem inColor_factor_gen {c : Bool} {T : FockOp} (hT : InColor c T) :
    ∀ (v : FockVec) (f : Nat → Int) (u u₀ : FockVec),
      (∀ z, u z = f (leadCount c z) * v (leadRest c z)) →
      (∀ z, u₀ z = f (leadCount c z) * vacVec (leadRest c z)) →
      ∀ w, T.fn u w = T.fn u₀ (List.replicate (leadCount c w) c) * v (leadRest c w) := by
  induction hT with
  | const n =>
      intro v f u u₀ hu hu₀ w
      change n * u w = (n * u₀ (List.replicate (leadCount c w) c)) * v (leadRest c w)
      rw [hu w, hu₀ (List.replicate (leadCount c w) c),
          leadCount_replicate, leadRest_replicate, vacVec, Int.mul_one, Int.mul_assoc]
  | create =>
      intro v f u u₀ hu hu₀ w
      cases w with
      | nil => simp [createOp, createFn, leadCount]
      | cons b ws =>
          by_cases hbc : (b == c) = true
          · have hb : b = c := beq_iff_eq.mp hbc
            rw [hb, leadCount_cons_same, leadRest_cons_same]
            simp [List.replicate, createOp, createFn, hu ws, hu₀ (List.replicate (leadCount c ws) c),
              leadCount_replicate, leadRest_replicate, vacVec]
          · change (if b == c then u ws else 0) =
              createFn c u₀ (List.replicate (if b == c then leadCount c ws + 1 else 0) c) *
                v (if b == c then leadRest c ws else b :: ws)
            simp [hbc, createFn]
  | annihilate =>
      intro v f u u₀ hu hu₀ w
      change u (c :: w) = u₀ (c :: List.replicate (leadCount c w) c) * v (leadRest c w)
      rw [hu (c :: w), hu₀ (c :: List.replicate (leadCount c w) c),
          leadCount_cons_same, leadRest_cons_same,
          leadCount_cons_same, leadRest_cons_same,
          leadCount_replicate, leadRest_replicate, vacVec, Int.mul_one]
  | add _ _ ihx ihy =>
      intro v f u u₀ hu hu₀ w
      change _ + _ = (_ + _) * v (leadRest c w)
      rw [ihx v f u u₀ hu hu₀ w, ihy v f u u₀ hu hu₀ w, Int.add_mul]
  | neg _ ihx =>
      intro v f u u₀ hu hu₀ w
      change -(_) = -(_) * v (leadRest c w)
      rw [ihx v f u u₀ hu hu₀ w, Int.neg_mul]
  | @mul x y _ _ ihx ihy =>
      intro v f u u₀ hu hu₀ w
      let f' : Nat → Int := fun k => y.fn u₀ (List.replicate k c)
      have hu' : ∀ z, y.fn u z = f' (leadCount c z) * v (leadRest c z) := ihy v f u u₀ hu hu₀
      have hu₀' : ∀ z, y.fn u₀ z = f' (leadCount c z) * vacVec (leadRest c z) :=
        ihy vacVec f u₀ u₀ hu₀ hu₀
      exact ihx v f' (y.fn u) (y.fn u₀) hu' hu₀' w

/-- Key tensor-factorization lemma: any `T ∈ InColor c` acting on a vector `v` that has
    no top-letter `c` (`∀ ws, v (c :: ws) = 0`) factors as `(T Ω)(c^k) * v(rest)`. -/
theorem inColor_action_factor {c : Bool} {T : FockOp} (hT : InColor c T)
    {v : FockVec} (hv : ∀ ws : List Bool, v (c :: ws) = 0) :
    ∀ w : List Bool,
      T.fn v w = T.fn vacVec (List.replicate (leadCount c w) c) * v (leadRest c w) := by
  apply inColor_factor_gen hT v (fun k => if k == 0 then 1 else 0) v vacVec
  · intro z; cases z with
    | nil => simp [leadCount, leadRest]
    | cons b ws =>
        by_cases hbc : (b == c) = true
        · have hb : b = c := beq_iff_eq.mp hbc
          rw [hb]; simp [leadCount, hv]
        · simp [leadCount, leadRest, hbc]
  · intro z; cases z with
    | nil => simp [leadCount, leadRest, vacVec]
    | cons b ws =>
        by_cases hbc : (b == c) = true
        · simp [leadCount, hbc, vacVec]
        · simp [leadCount, leadRest, hbc, vacVec]

/-- Step lemma for Voiculescu freeness: if `T ∈ InColor c` is centered (`phi T = 0`)
    and `v` has no top-letter `c`, then `T v` has zero vacuum component AND no top-letter `!c`. -/
theorem inColor_centered_step {c : Bool} {T : FockOp} (hT : InColor c T) (hphi : phi T = 0)
    {v : FockVec} (hv : ∀ ws : List Bool, v (c :: ws) = 0) :
    T.fn v [] = 0 ∧ ∀ ws : List Bool, T.fn v ((!c) :: ws) = 0 := by
  constructor
  · rw [inColor_action_factor hT hv []]
    simp [leadCount, List.replicate]
    change phi T * v (leadRest c []) = 0
    rw [hphi, Int.zero_mul]
  · intro ws
    rw [inColor_action_factor hT hv ((!c) :: ws)]
    have hneq : ((!c) == c) = false := by cases c <;> rfl
    simp [leadCount, hneq, List.replicate]
    change phi T * v (leadRest c ((!c) :: ws)) = 0
    rw [hphi, Int.zero_mul]

private theorem alt_scalar_vec_props :
    ∀ {start : Bool} {as : List FockOp},
      AltMem (InColor false) (InColor true) start as →
      AllCentered scalarFockSpace as →
      (listProd as).fn vacVec [] = 0 ∧
        ∀ ws : List Bool, (listProd as).fn vacVec ((!start) :: ws) = 0
  | false, [a], AltMem.single_false ha, hc => by
      simp only [listProd, mul_one_ring]
      exact inColor_centered_step ha (hc a (List.Mem.head [])) (fun _ => rfl)
  | true, [a], AltMem.single_true ha, hc => by
      simp only [listProd, mul_one_ring]
      exact inColor_centered_step ha (hc a (List.Mem.head [])) (fun _ => rfl)
  | false, a :: as, AltMem.cons_false ha hrest, hc => by
      have hc' : AllCentered scalarFockSpace as := fun x hx => hc x (List.Mem.tail a hx)
      have ih := alt_scalar_vec_props hrest hc'
      have hv : ∀ ws : List Bool, (listProd as).fn vacVec (false :: ws) = 0 := ih.2
      exact inColor_centered_step ha (hc a (List.Mem.head as)) hv
  | true, a :: as, AltMem.cons_true ha hrest, hc => by
      have hc' : AllCentered scalarFockSpace as := fun x hx => hc x (List.Mem.tail a hx)
      have ih := alt_scalar_vec_props hrest hc'
      have hv : ∀ ws : List Bool, (listProd as).fn vacVec (true :: ws) = 0 := ih.2
      exact inColor_centered_step ha (hc a (List.Mem.head as)) hv

/-- Voiculescu's all-order scalar freeness of `InColor false` and `InColor true`. -/
theorem scalar_isBFree : IsBFree scalarFockSpace (InColor false) (InColor true) where
  sub₀ := inColor_isSubalgebra false
  sub₁ := inColor_isSubalgebra true
  vanish _ _ halt hc := (alt_scalar_vec_props halt hc).1

end FockOp

/-! ### Lifting to Operator-Valued Free Probability Over `B = Mat2 Int` -/

def iotaMat2Fock (B : Mat2 Int) : Mat2 FockOp :=
  ⟨FockOp.constOp B.a11, FockOp.constOp B.a12, FockOp.constOp B.a21, FockOp.constOp B.a22⟩

def expMat2Fock (M : Mat2 FockOp) : Mat2 Int :=
  ⟨FockOp.phi M.a11, FockOp.phi M.a12, FockOp.phi M.a21, FockOp.phi M.a22⟩

/-- The canonical operator-valued probability space `(Mat2 FockOp, Mat2 Int, ι, E)`. -/
def mat2FockSpace : OpValProbSpace (Mat2 FockOp) (Mat2 Int) where
  iota := iotaMat2Fock
  iota_zero := rfl
  iota_one := by
    apply Mat2.ext
    · exact FockOp.constOp_one
    · exact FockOp.constOp_zero
    · exact FockOp.constOp_zero
    · exact FockOp.constOp_one
  iota_add b₁ b₂ := by
    apply Mat2.ext <;> exact FockOp.constOp_add _ _
  iota_neg b := by
    apply Mat2.ext <;> exact FockOp.constOp_neg _
  iota_mul b₁ b₂ := by
    apply Mat2.ext <;> {
      change FockOp.constOp (_ * _ + _ * _) =
        FockOp.constOp _ * FockOp.constOp _ + FockOp.constOp _ * FockOp.constOp _
      rw [FockOp.constOp_add, FockOp.constOp_mul_hom, FockOp.constOp_mul_hom]
    }
  exp := expMat2Fock
  exp_zero := by
    apply Mat2.ext <;> exact FockOp.phi_zero
  exp_add _ _ := rfl
  exp_neg _ := rfl
  exp_iota b := by
    apply Mat2.ext <;> exact FockOp.phi_const _
  exp_bimod b₁ b₂ x := by
    apply Mat2.ext <;> {
      change FockOp.phi ((FockOp.constOp _ * _ + FockOp.constOp _ * _) * FockOp.constOp _ +
        (FockOp.constOp _ * _ + FockOp.constOp _ * _) * FockOp.constOp _) =
        (_ * FockOp.phi _ + _ * FockOp.phi _) * _ + (_ * FockOp.phi _ + _ * FockOp.phi _) * _
      rw [AssocRing.right_distrib, AssocRing.right_distrib,
          FockOp.phi_add, FockOp.phi_add, FockOp.phi_add,
          FockOp.phi_bimod, FockOp.phi_bimod, FockOp.phi_bimod, FockOp.phi_bimod,
          Int.add_mul, Int.add_mul]
    }

/-- Entrywise `InColor c` subalgebra of `Mat2 FockOp`. -/
def InMat2Color (c : Bool) (M : Mat2 FockOp) : Prop :=
  FockOp.InColor c M.a11 ∧ FockOp.InColor c M.a12 ∧
  FockOp.InColor c M.a21 ∧ FockOp.InColor c M.a22

theorem inMat2Color_isSubalgebra (c : Bool) :
    IsSubalgebra mat2FockSpace (InMat2Color c) where
  has_iota _ := ⟨FockOp.InColor.const _, FockOp.InColor.const _,
                 FockOp.InColor.const _, FockOp.InColor.const _⟩
  has_add hx hy := ⟨FockOp.InColor.add hx.1 hy.1, FockOp.InColor.add hx.2.1 hy.2.1,
                    FockOp.InColor.add hx.2.2.1 hy.2.2.1, FockOp.InColor.add hx.2.2.2 hy.2.2.2⟩
  has_neg hx := ⟨FockOp.InColor.neg hx.1, FockOp.InColor.neg hx.2.1,
                 FockOp.InColor.neg hx.2.2.1, FockOp.InColor.neg hx.2.2.2⟩
  has_mul hx hy :=
    ⟨FockOp.InColor.add (FockOp.InColor.mul hx.1 hy.1) (FockOp.InColor.mul hx.2.1 hy.2.2.1),
     FockOp.InColor.add (FockOp.InColor.mul hx.1 hy.2.1) (FockOp.InColor.mul hx.2.1 hy.2.2.2),
     FockOp.InColor.add (FockOp.InColor.mul hx.2.2.1 hy.1) (FockOp.InColor.mul hx.2.2.2 hy.2.2.1),
     FockOp.InColor.add (FockOp.InColor.mul hx.2.2.1 hy.2.1) (FockOp.InColor.mul hx.2.2.2 hy.2.2.2)⟩

/-- Tensor product `B ⊗ T` of a `2 × 2` integer matrix `B` and scalar operator `T : FockOp`. -/
def tensorMat (B : Mat2 Int) (T : FockOp) : Mat2 FockOp :=
  ⟨FockOp.constOp B.a11 * T, FockOp.constOp B.a12 * T,
   FockOp.constOp B.a21 * T, FockOp.constOp B.a22 * T⟩

theorem tensorMat_inMat2Color {c : Bool} (B : Mat2 Int) {T : FockOp} (hT : FockOp.InColor c T) :
    InMat2Color c (tensorMat B T) :=
  ⟨FockOp.InColor.mul (FockOp.InColor.const _) hT,
   FockOp.InColor.mul (FockOp.InColor.const _) hT,
   FockOp.InColor.mul (FockOp.InColor.const _) hT,
   FockOp.InColor.mul (FockOp.InColor.const _) hT⟩

private def entryAt (M : Mat2 FockOp) : Bool → Bool → FockOp
  | false, false => M.a11
  | false, true  => M.a12
  | true,  false => M.a21
  | true,  true  => M.a22

private theorem entryAt_inColor {c : Bool} {M : Mat2 FockOp} (hM : InMat2Color c M)
    (i j : Bool) : FockOp.InColor c (entryAt M i j) := by
  cases i <;> cases j
  · exact hM.1
  · exact hM.2.1
  · exact hM.2.2.1
  · exact hM.2.2.2

private theorem entryAt_centered {M : Mat2 FockOp} (hM : mat2FockSpace.exp M = 0)
    (i j : Bool) : FockOp.phi (entryAt M i j) = 0 := by
  cases i <;> cases j
  · exact congrArg Mat2.a11 hM
  · exact congrArg Mat2.a12 hM
  · exact congrArg Mat2.a21 hM
  · exact congrArg Mat2.a22 hM

private theorem entryAt_mul (M N : Mat2 FockOp) (i j : Bool) :
    entryAt (M * N) i j = entryAt M i false * entryAt N false j + entryAt M i true * entryAt N true j := by
  cases i <;> cases j <;> rfl

/-- Expanding `(listProd Ms)` entrywise shows every matrix entry is a sum of scalar alternating
    centered products, hence has zero vacuum expectation! -/
private theorem mat2_alt_vec_props :
    ∀ {start : Bool} {Ms : List (Mat2 FockOp)},
      AltMem (InMat2Color false) (InMat2Color true) start Ms →
      AllCentered mat2FockSpace Ms →
      ∀ (i j : Bool),
        (entryAt (listProd Ms) i j).fn vacVec [] = 0 ∧
          ∀ ws : List Bool, (entryAt (listProd Ms) i j).fn vacVec ((!start) :: ws) = 0
  | false, [M], AltMem.single_false hM, hc, i, j => by
      simp only [listProd, mul_one_ring]
      exact FockOp.inColor_centered_step (entryAt_inColor hM i j)
        (entryAt_centered (hc M (List.Mem.head [])) i j) (fun _ => rfl)
  | true, [M], AltMem.single_true hM, hc, i, j => by
      simp only [listProd, mul_one_ring]
      exact FockOp.inColor_centered_step (entryAt_inColor hM i j)
        (entryAt_centered (hc M (List.Mem.head [])) i j) (fun _ => rfl)
  | false, M :: Ms, AltMem.cons_false hM hrest, hc, i, j => by
      have hc' : AllCentered mat2FockSpace Ms := fun x hx => hc x (List.Mem.tail M hx)
      have hM_c := hc M (List.Mem.head Ms)
      have ih0 := mat2_alt_vec_props hrest hc' false j
      have ih1 := mat2_alt_vec_props hrest hc' true j
      have step0 := FockOp.inColor_centered_step (entryAt_inColor hM i false)
        (entryAt_centered hM_c i false) ih0.2
      have step1 := FockOp.inColor_centered_step (entryAt_inColor hM i true)
        (entryAt_centered hM_c i true) ih1.2
      have hmul : entryAt (listProd (M :: Ms)) i j =
          entryAt M i false * entryAt (listProd Ms) false j +
            entryAt M i true * entryAt (listProd Ms) true j :=
        entryAt_mul M (listProd Ms) i j
      rw [hmul]
      refine ⟨?_, ?_⟩
      · change (entryAt M i false).fn ((entryAt (listProd Ms) false j).fn vacVec) [] +
          (entryAt M i true).fn ((entryAt (listProd Ms) true j).fn vacVec) [] = 0
        rw [step0.1, step1.1]; rfl
      · intro ws
        change (entryAt M i false).fn ((entryAt (listProd Ms) false j).fn vacVec) ((!false) :: ws) +
          (entryAt M i true).fn ((entryAt (listProd Ms) true j).fn vacVec) ((!false) :: ws) = 0
        rw [step0.2 ws, step1.2 ws]; rfl
  | true, M :: Ms, AltMem.cons_true hM hrest, hc, i, j => by
      have hc' : AllCentered mat2FockSpace Ms := fun x hx => hc x (List.Mem.tail M hx)
      have hM_c := hc M (List.Mem.head Ms)
      have ih0 := mat2_alt_vec_props hrest hc' false j
      have ih1 := mat2_alt_vec_props hrest hc' true j
      have step0 := FockOp.inColor_centered_step (entryAt_inColor hM i false)
        (entryAt_centered hM_c i false) ih0.2
      have step1 := FockOp.inColor_centered_step (entryAt_inColor hM i true)
        (entryAt_centered hM_c i true) ih1.2
      have hmul : entryAt (listProd (M :: Ms)) i j =
          entryAt M i false * entryAt (listProd Ms) false j +
            entryAt M i true * entryAt (listProd Ms) true j :=
        entryAt_mul M (listProd Ms) i j
      rw [hmul]
      refine ⟨?_, ?_⟩
      · change (entryAt M i false).fn ((entryAt (listProd Ms) false j).fn vacVec) [] +
          (entryAt M i true).fn ((entryAt (listProd Ms) true j).fn vacVec) [] = 0
        rw [step0.1, step1.1]; rfl
      · intro ws
        change (entryAt M i false).fn ((entryAt (listProd Ms) false j).fn vacVec) ((!true) :: ws) +
          (entryAt M i true).fn ((entryAt (listProd Ms) true j).fn vacVec) ((!true) :: ws) = 0
        rw [step0.2 ws, step1.2 ws]; rfl

/-- Voiculescu's all-order `Mat2 Int`-freeness of `InMat2Color false` and `InMat2Color true`! -/
theorem mat2Fock_isBFree :
    IsBFree mat2FockSpace (InMat2Color false) (InMat2Color true) where
  sub₀ := inMat2Color_isSubalgebra false
  sub₁ := inMat2Color_isSubalgebra true
  vanish _ _ halt hc := by
    apply Mat2.ext
    · exact (mat2_alt_vec_props halt hc false false).1
    · exact (mat2_alt_vec_props halt hc false true).1
    · exact (mat2_alt_vec_props halt hc true false).1
    · exact (mat2_alt_vec_props halt hc true true).1

end Conjecture00000004759
