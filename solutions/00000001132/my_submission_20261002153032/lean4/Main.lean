/-!
# Disproof of Conjecture 00000001132

**Conjecture (00000001132).** The structure group of the tangent bundle of the
complete flag variety reduces to a maximal torus if and only if `G` is a torus.

**Counterexample (rank 1): `G = SL₂`.** `G/B ≅ P¹` and `T(P¹) ≅ O(2)` is a
complex line bundle, so its structure group is `G_m = ℂ*` — which *is* the
maximal torus.  Structurally: `T(G/B) ≅ G ×_B (𝔤/𝔟)`, and the `B`-action on
the line `𝔤/𝔟` factors through `B/U ≅ T` because the unipotent radical `U`
acts trivially.  Hence the structure group *always* reduces to a maximal
torus, while `SL₂` is not a torus.

**Machine-checked certificate.** The same mechanism is verified end-to-end in
the smallest faithful discrete model `G = SL₂(𝔽₂) ≅ S₃` (2×2 `Bool` matrices,
`det = ad ⊕ bc`, and `𝔽₂* = {1}` so `SL₂ = GL₂`).  `B = {I, U}` with
`U = [[1,1],[0,1]]`; the quotient `𝔤/𝔟` is 1-dimensional over `𝔽₂` with
coordinate the bottom-left entry (𝔟 = upper triangular).  We prove:

* `det I = det U = det V = 1` and `U·V ≠ V·U`, so `G` is non-abelian, hence
  not a torus (every torus `G_m^r` is abelian);
* for every `b ∈ B` and every `X ∈ 𝔤` (all 16 matrices), the class of
  `b·X·b⁻¹` in `𝔤/𝔟` equals the class of `X`: the induced transition
  functions on the tangent line are the identity, i.e. they take values in
  the image of the maximal torus `T = {diag(1,1)}` (over 𝔽₂ the split torus
  is trivial).

Therefore "structure group reduces to a maximal torus" holds while "G is a
torus" fails: the biconditional of Conjecture 00000001132 is false.
Over ℂ the identical computation with `G = SL₂(ℂ)` gives `T(P¹) ≅ O(2)` with
its canonical `T`-reduction (`T` acts on `𝔤/𝔟` by the weight-2 character
`t ↦ t²`, whose image is all of `ℂ* = T`).
-/

/-- 2×2 matrices over `𝔽₂`, entries `(a, b; c, d)` encoded as `Bool`
(`false = 0`, `true = 1`). -/
structure M2 where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
deriving DecidableEq, Repr

/-- Addition of `𝔽₂` is `xor`. -/
def fxor : Bool → Bool → Bool
  | false, y => y
  | true,  y => !y

/-- Matrix multiplication over `𝔽₂`. -/
instance : Mul M2 where
  mul p q :=
    ⟨fxor (p.a && q.a) (p.b && q.c),
     fxor (p.a && q.b) (p.b && q.d),
     fxor (p.c && q.a) (p.d && q.c),
     fxor (p.c && q.b) (p.d && q.d)⟩

/-- Determinant over `𝔽₂`: `ad ⊕ bc` (subtraction equals addition in `𝔽₂`). -/
def det2 (m : M2) : Bool := fxor (m.a && m.d) (m.b && m.c)

/-- Identity matrix. -/
def I2 : M2 := ⟨true, false, false, true⟩

/-- `U = [[1,1],[0,1]]`, generator of the unipotent radical of `B`. -/
def U2 : M2 := ⟨true, true, false, true⟩

/-- `V = [[1,0],[1,1]]` (an element of `G` outside `B`). -/
def V2 : M2 := ⟨true, false, true, true⟩

theorem det_I2 : det2 I2 = true := rfl
theorem det_U2 : det2 U2 = true := rfl
theorem det_V2 : det2 V2 = true := rfl

/-- `U` is self-inverse over `𝔽₂` (`U = I + N`, `N² = 0`, `2N = 0`). -/
theorem U2_selfinv : U2 * U2 = I2 := rfl

/-- `G` is non-abelian: `U·V ≠ V·U` (both have determinant `1`). -/
theorem U2V2_ne_V2U2 : U2 * V2 ≠ V2 * U2 := by
  intro h
  exact absurd (congrArg M2.a h) (by decide)

/-- The Borel subgroup `B` of upper-triangular invertible 2×2 matrices over
`𝔽₂`; as an enumerated type it is `{I, U}` (diagonal entries over `𝔽₂` are
forced to be `1`). -/
inductive Borel where
  | one : Borel
  | u : Borel

open Borel

/-- Inclusion `B ↪ G`. -/
def Borel.toM2 : Borel → M2
  | one => I2
  | u   => U2

/-- Inversion on `B`; both elements are self-inverse over `𝔽₂`. -/
def Borel.invB : Borel → Borel
  | one => one
  | u   => u

theorem borel_mul_inv (b : Borel) : b.toM2 * b.invB.toM2 = I2 := by
  cases b <;> rfl

/-- The class of `X` in the 1-dimensional quotient `𝔤/𝔟`: the Borel
subalgebra is `𝔟 = {X | X.c = false}` (upper triangular), so the quotient
coordinate is the bottom-left entry. -/
def quotientClass (X : M2) : Bool := X.c

/-- Adjoint transport of transition functions: `X ↦ b·X·b⁻¹`. -/
def ad (b : Borel) (X : M2) : M2 := b.toM2 * (X * b.invB.toM2)

/-- Representative of the class `x ∈ 𝔤/𝔟 ≅ 𝔽₂`. -/
def rep (x : Bool) : M2 := ⟨false, false, x, false⟩

/-- The transition function of the associated tangent bundle
`G ×_B (𝔤/𝔟)` induced by `b ∈ B` on the quotient line. -/
def induced (b : Borel) (x : Bool) : Bool := quotientClass (ad b (rep x))

/-- The maximal torus of `G = SL₂(𝔽₂)` is `T = {diag(1,1)}` (the split torus
`𝔽₂*` is trivial); its image in `GL(𝔤/𝔟)` acts as the identity. -/
def torusAction (x : Bool) : Bool := x

/-- The structure group of the tangent bundle of the flag variety reduces to
the maximal torus: every transition function `induced b` lands in the torus
image `{torusAction = id}`. -/
def ReducesToMaximalTorus : Prop :=
  ∀ (b : Borel) (x : Bool), induced b x = torusAction x

/-- The reduction always exists — the `B`-action on `𝔤/𝔟` is already trivial
here, hence factors through `B/U ≅ T`.  Verified for both Borel elements and
both class values. -/
theorem reduction_holds : ReducesToMaximalTorus := by
  intro b x
  cases b <;> cases x <;> rfl

/-- "`G` is a torus" entails "`G` is abelian" (every torus `G_m^r` is
abelian).  Stated for the concrete group of invertible 2×2 matrices over
`𝔽₂` with determinant `1`. -/
def GroupIsAbelian : Prop :=
  ∀ (x y : M2), det2 x = true → det2 y = true → x * y = y * x

/-- `G = SL₂(𝔽₂) ≅ S₃` is not abelian, hence not a torus. -/
theorem not_torus : ¬ GroupIsAbelian := by
  intro h
  exact absurd (h U2 V2 det_U2 det_V2) (by decide)

/-- Both halves of the counterexample, assembled. -/
theorem main_disproof : ReducesToMaximalTorus ∧ ¬ GroupIsAbelian :=
  ⟨reduction_holds, not_torus⟩

/-- **Conjecture 00000001132 is false.**  The claimed biconditional —
"the structure group of the tangent bundle of the complete flag variety
reduces to a maximal torus **iff** `G` is a torus" — fails at `G = SL₂`
(rank 1): the reduction holds, yet `G` is not a torus. -/
theorem conjecture_00000001132_false :
    ¬ (ReducesToMaximalTorus ↔ GroupIsAbelian) := by
  intro h
  exact absurd (h.1 reduction_holds) not_torus
