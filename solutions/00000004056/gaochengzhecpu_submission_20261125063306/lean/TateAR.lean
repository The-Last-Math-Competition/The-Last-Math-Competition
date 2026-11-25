import Std

namespace TateAR

abbrev F3 := Fin 3
abbrev Pair := F3 × F3
abbrev Triple := F3 × F3 × F3

local instance decidableForallProd {α β : Type} (p : α × β → Prop)
    [Decidable (∀ a b, p (a, b))] : Decidable (∀ x, p x) :=
  decidable_of_iff _ ⟨fun h x => h x.1 x.2, fun h a b => h (a, b)⟩

def uOnPair (x : Pair) : Pair := (0, x.1)
def uOnTriple (x : Triple) : Triple := (0, x.1, x.2.1)
def uSquaredOnTriple (x : Triple) : Triple := uOnTriple (uOnTriple x)
def topQuotient (x : Triple) : F3 := x.1
def idealQuotient (x : Triple) : Pair := (x.1, x.2.1)
def embedU (x : Pair) : Triple := (0, x.1, x.2)
def embedUSquared (x : F3) : Triple := (0, 0, x)

theorem complete_resolution_exact :
    (∀ x : Triple, uOnTriple x = (0, 0, 0) ↔
      ∃ y : Triple, uSquaredOnTriple y = x) ∧
    (∀ x : Triple, uSquaredOnTriple x = (0, 0, 0) ↔
      ∃ y : Triple, uOnTriple y = x) := by
  constructor
  · rintro ⟨a, b, c⟩
    constructor
    · intro h
      have ha : a = 0 := congrArg (fun v : Triple => v.2.1) h
      have hb : b = 0 := congrArg (fun v : Triple => v.2.2) h
      subst a
      subst b
      exact ⟨(c, 0, 0), rfl⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      rfl
  · rintro ⟨a, b, c⟩
    constructor
    · intro h
      have ha : a = 0 := congrArg (fun v : Triple => v.2.2) h
      subst a
      exact ⟨(b, c, 0), rfl⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      rfl

/-- The indicated embeddings identify the kernels of the two free covers. -/
theorem two_covers :
    (∀ x : Triple, topQuotient x = 0 ↔
      ∃ y : Pair, embedU y = x) ∧
    (∀ x : Triple, idealQuotient x = (0, 0) ↔
      ∃ y : F3, embedUSquared y = x) ∧
    (∀ y : F3, ∃ x : Triple, topQuotient x = y) ∧
    (∀ y : Pair, ∃ x : Triple, idealQuotient x = y) ∧
    (∀ x y : Pair, embedU x = embedU y → x = y) ∧
    (∀ x y : F3, embedUSquared x = embedUSquared y → x = y) ∧
    (∀ x : Triple, embedU (idealQuotient x) = uOnTriple x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    constructor
    · intro h
      change a = 0 at h
      subst a
      exact ⟨(b, c), rfl⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      rfl
  · rintro ⟨a, b, c⟩
    constructor
    · intro h
      have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst a
      subst b
      exact ⟨c, rfl⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      rfl
  · intro y
    exact ⟨(y, 0, 0), rfl⟩
  · intro y
    exact ⟨(y.1, y.2, 0), rfl⟩
  · intro x y h
    exact congrArg Prod.snd h
  · intro x y h
    exact congrArg (fun v : Triple => v.2.2) h
  · intro x
    rfl

/-- A concrete coefficient model with the generator u acting by a shift. -/
structure ModuleModel where
  Carrier : Type
  zero : Carrier
  add : Carrier → Carrier → Carrier
  smul : F3 → Carrier → Carrier
  u : Carrier → Carrier
  add_zero : ∀ x, add x zero = x

def simple : ModuleModel where
  Carrier := F3
  zero := 0
  add := (· + ·)
  smul := (· * ·)
  u := fun _ => 0
  add_zero := by decide

def radical : ModuleModel where
  Carrier := Pair
  zero := (0, 0)
  add x y := (x.1 + y.1, x.2 + y.2)
  smul c x := (c * x.1, c * x.2)
  u := uOnPair
  add_zero := by decide

def regular : ModuleModel where
  Carrier := Triple
  zero := (0, 0, 0)
  add x y := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)
  smul c x := (c * x.1, c * x.2.1, c * x.2.2)
  u := uOnTriple
  add_zero := by decide

structure ModuleMap (X Y : ModuleModel) where
  toFun : X.Carrier → Y.Carrier
  map_zero : toFun X.zero = Y.zero
  map_add : ∀ x y, toFun (X.add x y) = Y.add (toFun x) (toFun y)
  map_smul : ∀ c x, toFun (X.smul c x) = Y.smul c (toFun x)
  map_u : ∀ x, toFun (X.u x) = Y.u (toFun x)

def quotientToSimple : ModuleMap regular simple where
  toFun := topQuotient
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_u _ := rfl

def quotientToRadical : ModuleMap regular radical where
  toFun := idealQuotient
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_u _ := rfl

def radicalEmbedding : ModuleMap radical regular where
  toFun := embedU
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_u _ := rfl

def simpleEmbedding : ModuleMap simple regular where
  toFun := embedUSquared
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_u _ := rfl

theorem composite_through_radical_is_zero (f : ModuleMap simple radical)
    (g : ModuleMap radical simple) (x : simple.Carrier) :
    g.toFun (f.toFun x) = simple.zero := by
  have h := (f.map_u x).symm.trans f.map_zero
  change uOnPair (f.toFun x) = (0, 0) at h
  let y : Pair := ((f.toFun x).2, 0)
  have hy : uOnPair y = f.toFun x :=
    Prod.ext (congrArg Prod.snd h).symm rfl
  rw [← hy]
  exact g.map_u y

theorem composite_through_regular_is_zero (f : ModuleMap simple regular)
    (g : ModuleMap regular simple) (x : simple.Carrier) :
    g.toFun (f.toFun x) = simple.zero := by
  have h := (f.map_u x).symm.trans f.map_zero
  change uOnTriple (f.toFun x) = (0, 0, 0) at h
  obtain ⟨y, hy⟩ := (complete_resolution_exact.1 (f.toFun x)).1 h
  change uOnTriple (uOnTriple y) = f.toFun x at hy
  rw [← hy]
  exact g.map_u (uOnTriple y)

/-- Such a finite sum is the composite through a finite free module. -/
def factorSum (X : ModuleModel)
    (maps : List (ModuleMap X regular × ModuleMap regular X)) (x : X.Carrier) :
    X.Carrier :=
  maps.foldr (fun (f, g) sum => X.add (g.toFun (f.toFun x)) sum) X.zero

theorem simple_projective_factors_zero
    (maps : List (ModuleMap simple regular × ModuleMap regular simple))
    (x : simple.Carrier) : factorSum simple maps x = simple.zero := by
  induction maps with
  | nil => rfl
  | cons head tail ih =>
    change simple.add (head.2.toFun (head.1.toFun x)) (factorSum simple tail x) =
      simple.zero
    rw [composite_through_regular_is_zero, ih, simple.add_zero]

/-- Two-sided inverse modulo the maps that factor through projectives. -/
def StablyIsomorphic (X Y : ModuleModel) : Prop :=
  ∃ (f : ModuleMap X Y) (g : ModuleMap Y X)
    (leftFactors : List (ModuleMap X regular × ModuleMap regular X))
    (rightFactors : List (ModuleMap Y regular × ModuleMap regular Y)),
      (∀ x, g.toFun (f.toFun x) = X.add x (factorSum X leftFactors x)) ∧
      (∀ y, f.toFun (g.toFun y) = Y.add y (factorSum Y rightFactors y))

def identityMap (X : ModuleModel) : ModuleMap X X where
  toFun := id
  map_zero := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_u _ := rfl

theorem stable_refl (X : ModuleModel) : StablyIsomorphic X X := by
  refine ⟨identityMap X, identityMap X, [], [], ?_, ?_⟩
  all_goals
    intro x
    exact (X.add_zero x).symm

theorem radical_not_stably_simple : ¬ StablyIsomorphic simple radical := by
  rintro ⟨f, g, leftFactors, _, hleft, _⟩
  let x : simple.Carrier := (1 : F3)
  have h := hleft x
  rw [composite_through_radical_is_zero, simple_projective_factors_zero, simple.add_zero] at h
  exact (by decide : (0 : F3) ≠ 1) h

/-- The phase with a single coefficient is S, and the other phase is uA. -/
def phaseModule : Bool → ModuleModel
  | false => simple
  | true => radical

def syzygyPhase : Bool → Bool := Bool.not

def arPhase (b : Bool) : Bool := syzygyPhase (syzygyPhase b)

def phaseCover (b : Bool) : ModuleMap regular (phaseModule b) :=
  match b with
  | false => quotientToSimple
  | true => quotientToRadical

def phaseKernel (b : Bool) : ModuleMap (phaseModule (syzygyPhase b)) regular :=
  match b with
  | false => radicalEmbedding
  | true => simpleEmbedding

def RealizesSyzygy (b : Bool) : Prop :=
  (∀ x : Triple, (phaseCover b).toFun x = (phaseModule b).zero ↔
    ∃ y, (phaseKernel b).toFun y = x) ∧
  (∀ y, ∃ x : Triple, (phaseCover b).toFun x = y) ∧
  (∀ x y, (phaseKernel b).toFun x = (phaseKernel b).toFun y → x = y)

theorem covers_realize_syzygy (b : Bool) : RealizesSyzygy b := by
  obtain ⟨simpleKer, radicalKer, simpleSurj, radicalSurj, radicalInj, simpleInj, _⟩ := two_covers
  cases b
  · exact ⟨simpleKer, simpleSurj, radicalInj⟩
  · exact ⟨radicalKer, radicalSurj, simpleInj⟩

def advance (step : Bool → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => step (advance step n)

def Period (step : Bool → Bool) (n : Nat) : Prop :=
  0 < n ∧ StablyIsomorphic simple (phaseModule (advance step n)) ∧
    ∀ m, 0 < m → m < n → ¬ StablyIsomorphic simple (phaseModule (advance step m))

theorem periods_differ :
    Period syzygyPhase 2 ∧ Period arPhase 1 ∧ (2 : Nat) ≠ 1 := by
  refine ⟨⟨by decide, stable_refl simple, ?_⟩, ⟨by decide, stable_refl simple, ?_⟩, by decide⟩
  · intro m hp hn
    have : m = 1 := by omega
    subst m
    exact radical_not_stably_simple
  · intro m hp hn
    omega

theorem group_block_counterexample :
    (∀ b, RealizesSyzygy b) ∧ Period syzygyPhase 2 ∧ Period arPhase 1 ∧ (2 : Nat) ≠ 1 :=
  ⟨covers_realize_syzygy, periods_differ⟩

#print axioms complete_resolution_exact
#print axioms two_covers
#print axioms radical_not_stably_simple
#print axioms group_block_counterexample

end TateAR
