import Mathlib

namespace Submission00000004225

/-!
# Refutation of TLMC conjecture 00000004225

Conjecture (verbatim): "The higher Dirichlet–Neumann operator is the boundary
response operator on k-chains.  The multiplicity of its zero eigenvalue equals
exactly the count of k-spanning trees of the boundary, and the multiplicity is
one if and only if the boundary is a sphere triangulation."

Standard reading (Hodge theory): the zero eigenspace of the boundary-response /
higher Dirichlet–Neumann operator on `k`-chains of a boundary complex `B = ∂M`
is the space of harmonic `k`-chains of `B`, so

    mult_k(B) = dim ker Δ_k(B) = β_k(B) = f_k − rank ∂_k − rank ∂_{k+1},

whereas the simplicial spanning-tree count τ_k(B) is a *determinantal* quantity
(Kalai's matrix-tree theorem: a weighted product of the NONZERO eigenvalues of
the Laplacian), not a kernel dimension.  Hence the identity `mult_k = τ_k`
fails generically, and the "multiplicity one iff sphere" clause fails in both
directions.

Counterexamples proved below:

(A) `∂Δ³` = boundary of the tetrahedron, a triangulation of `S²`, at `k = 1`:
    `Δ₁ = 4·I₆` (det `4096`), so `mult₁ = 0` while `τ₁ = τ(K₄) = 16`.
    `mult₁ ≠ τ₁` falsifies clause 1, and a sphere boundary with `mult ≠ 1`
    falsifies the "if" direction of clause 2.

(B) `T²` = the 7-vertex minimal triangulation of the torus (boundary of a
    solid torus), at `k = 2`: `Δ₂ = ∂₂ᵀ∂₂` has nullity `1` (explicit harmonic
    `2`-cycle `c` plus the dual-tree elimination of all other kernel
    directions), so `mult₂ = 1` although `T²` (χ = 0) is not a sphere —
    falsifying the "only if" direction.  (Also `τ₂ = 0`: a closed surface
    with `β₂ = 1` admits no simplicial `2`-trees.)

All incidence data are stored over `ℤ` (so every concrete computation is a
fast `decide`); `zeroMult` is measured over `ℚ` via `Matrix.map Int.cast`.
Every `decide`/`norm_num`/`linarith` proof is axiom-free — see `Check.lean`.
-/

open Matrix Finset

/-- Cast of an integer matrix into the rationals. -/
noncomputable def toQ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) ℚ :=
  M.map (Int.castRingHom ℚ)

/-! ## The higher Dirichlet–Neumann operator on `k`-chains -/

/-- The combinatorial higher Dirichlet–Neumann (boundary-response) operator on
`k`-chains of a boundary complex: `Δ_k = ∂_{k+1} ∂_{k+1}ᵀ + ∂_kᵀ ∂_k`,
where `Bup : C_{k+1} → C_k` and `Bdn : C_k → C_{k-1}` are the signed
incidence (boundary) matrices.  Its zero eigenspace is the space of harmonic
`k`-chains of the boundary, i.e. `ker Δ_k ≅ H_k(∂M; ℚ)`. -/
def dnOperator {p q r : ℕ} (Bup : Matrix (Fin p) (Fin q) ℤ)
    (Bdn : Matrix (Fin r) (Fin p) ℤ) : Matrix (Fin p) (Fin p) ℤ :=
  Bup * Bupᵀ + Bdnᵀ * Bdn

/-- The multiplicity of the zero eigenvalue of a `k`-chain DN operator:
the `ℚ`-dimension of the kernel of `x ↦ L *ᵥ x`. -/
noncomputable def zeroMult {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Module.finrank ℚ (LinearMap.ker (Matrix.mulVecLin (toQ L)))

/-- A finite simplicial surface presented by face counts and incidence data;
`closed` asserts every edge lies in exactly two triangles. -/
structure FinSurface where
  numVerts : ℕ
  numEdges : ℕ
  numTris : ℕ
  closed : Prop

/-- Euler characteristic of a `FinSurface`. -/
def FinSurface.eulerChar (S : FinSurface) : ℤ :=
  (S.numVerts : ℤ) - S.numEdges + S.numTris

/-- A closed surface is a sphere triangulation iff its Euler characteristic
is `2` (classification of closed surfaces). -/
def FinSurface.IsTwoSphere (S : FinSurface) : Prop :=
  S.closed ∧ S.eulerChar = 2

/-! ## Example A: the boundary of the tetrahedron (a triangulation of `S²`) -/

/-- The six edges of `K₄`, enumerated lexicographically. -/
def tetEdgeList : Fin 6 → Finset (Fin 4)
  | ⟨0, _⟩ => {0, 1}
  | ⟨1, _⟩ => {0, 2}
  | ⟨2, _⟩ => {0, 3}
  | ⟨3, _⟩ => {1, 2}
  | ⟨4, _⟩ => {1, 3}
  | ⟨5, _⟩ => {2, 3}

/-- All six edges as a `Finset`. -/
def tetEdges : Finset (Finset (Fin 4)) :=
  Finset.univ.image tetEdgeList

/-- The four triangles `(012), (013), (023), (123)`. -/
def tetTriList : Fin 4 → Finset (Fin 4)
  | ⟨0, _⟩ => {0, 1, 2}
  | ⟨1, _⟩ => {0, 1, 3}
  | ⟨2, _⟩ => {0, 2, 3}
  | ⟨3, _⟩ => {1, 2, 3}

/-- All four triangles as a `Finset`. -/
def tetTris : Finset (Finset (Fin 4)) :=
  Finset.univ.image tetTriList

/-- Boundary of the tetrahedron as a `FinSurface`: `(f₀,f₁,f₂) = (4,6,4)`,
closed because every edge is in exactly two triangles. -/
def tetBoundary : FinSurface where
  numVerts := 4
  numEdges := 6
  numTris := 4
  closed := ∀ e ∈ tetEdges, (tetTris.filter (fun t => e ⊆ t)).card = 2

/-- The boundary matrix `∂₁ : C₁ → C₀` of `∂Δ³` (vertices × edges). -/
def tetB1 : Matrix (Fin 4) (Fin 6) ℤ :=
  !![-1, -1, -1,  0,  0,  0;
      1,  0,  0, -1, -1,  0;
      0,  1,  0,  1,  0, -1;
      0,  0,  1,  0,  1,  1]

/-- The boundary matrix `∂₂ : C₂ → C₁` of `∂Δ³` (edges × triangles). -/
def tetB2 : Matrix (Fin 6) (Fin 4) ℤ :=
  !![ 1,  1,  0,  0;
     -1,  0,  1,  0;
      0, -1, -1,  0;
      1,  0,  0,  1;
      0,  1,  0, -1;
      0,  0,  1,  1]

/-- The `k = 1` DN operator `Δ₁` on `C₁(∂Δ³) ≅ ℤ⁶`. -/
def tetDN1 : Matrix (Fin 6) (Fin 6) ℤ := dnOperator tetB2 tetB1

/-- `∂Δ³` is a sphere triangulation: it is closed and `χ = 4 − 6 + 4 = 2`. -/
theorem tet_isTwoSphere : tetBoundary.IsTwoSphere := by
  constructor
  · show ∀ e ∈ tetEdges, (tetTris.filter (fun t => e ⊆ t)).card = 2
    decide
  · show tetBoundary.eulerChar = 2
    decide

/-- `Δ₁ = 4·I₆` on `C₁(∂Δ³)` (integer check). -/
theorem tetDN1_eq : tetDN1 = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

/-- `Δ₁` has nonzero determinant over `ℚ`, so it is injective over `ℚ`. -/
theorem tetDN1_det : (toQ tetDN1).det ≠ 0 := by
  have h : (toQ tetDN1).det = (tetDN1.det : ℚ) := by
    rw [toQ]
    exact (RingHom.map_det _ _).symm
  have hd : tetDN1.det = 4096 := by
    rw [tetDN1_eq, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    norm_num
  rw [h, hd]
  norm_num

/-- The kernel of `Δ₁ *ᵥ ·` over `ℚ` is trivial. -/
theorem tetDN1_ker_bot :
    LinearMap.ker (Matrix.mulVecLin (toQ tetDN1)) = ⊥ := by
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  exact Matrix.eq_zero_of_mulVec_eq_zero tetDN1_det hv

/-- The zero multiplicity of the `k = 1` DN operator on `∂Δ³` is `0`. -/
theorem zeroMult_tet : zeroMult tetDN1 = 0 := by
  rw [zeroMult, tetDN1_ker_bot]
  simp

/-- The spanning-tree count of the boundary's 1-skeleton `K₄`:
the number of `3`-edge subsets of the six edges covering all four vertices
(a spanning tree is a connected graph on `4` vertices with `3` edges,
equivalently a `3`-edge subset on which every vertex is incident). -/
def tetTreeCount : ℕ :=
  ((Finset.univ.powersetCard 3).filter
    (fun S : Finset (Fin 6) =>
      ∀ v : Fin 4, ∃ e ∈ S, v ∈ tetEdgeList e)).card

theorem tetTreeCount_eq : tetTreeCount = 16 := by
  decide

/-- Clause 1 of the conjecture fails on `∂Δ³` at `k = 1`: `0 ≠ 16`. -/
theorem clause1_tet_fails : zeroMult tetDN1 ≠ tetTreeCount := by
  rw [zeroMult_tet, tetTreeCount_eq]
  norm_num

/-- Clause 2 "if" fails: a sphere boundary need not have multiplicity `1`. -/
theorem clause2_if_fails : tetBoundary.IsTwoSphere ∧ zeroMult tetDN1 ≠ 1 :=
  ⟨tet_isTwoSphere, by rw [zeroMult_tet]; norm_num⟩

/-! ## Example B: the 7-vertex minimal triangulation of the torus `T²` -/

/-- The torus boundary as a `FinSurface`: `(7,21,14)`, `χ = 0`. -/
def torusBoundary : FinSurface where
  numVerts := 7
  numEdges := 21
  numTris := 14
  closed := True   -- every edge lies in exactly two triangles (see reproduce.py)

/-- The boundary matrix `∂₂ : C₂ → C₁` of the 7-vertex torus triangulation
(edges × triangles, `21 × 14`).  Edges and triangles are enumerated
lexicographically (see `reproduce.py` for the face lists). -/
def torusB2 : Matrix (Fin 21) (Fin 14) ℤ :=
  !![ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0,-1, 0, 0, 0, 0, 0, 0,-1;
      0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]

/-- The `k = 2` DN operator `Δ₂ = ∂₂ᵀ∂₂` on `C₂(T²) ≅ ℚ¹⁴`
(there are no `3`-faces on a surface, so the down term vanishes). -/
def torusDN2 : Matrix (Fin 14) (Fin 14) ℤ := torusB2ᵀ * torusB2

/-- The oriented fundamental `2`-cycle of the torus over `ℤ`. -/
def torusHarmonicZ : Fin 14 → ℤ := fun i => if i.val < 7 then -1 else 1

/-- The same cycle over `ℚ`. -/
noncomputable def torusHarmonic : Fin 14 → ℚ := fun i => (torusHarmonicZ i : ℚ)

theorem torusB2_harmonic : torusB2 *ᵥ torusHarmonicZ = 0 := by
  decide

theorem torusB2_harmonic_Q :
    (toQ torusB2) *ᵥ torusHarmonic = 0 := by
  funext i
  rw [Pi.zero_apply]
  show ((torusB2.map (Int.castRingHom ℚ)) *ᵥ torusHarmonic) i = 0
  have hc : torusHarmonic = (Int.castRingHom ℚ) ∘ torusHarmonicZ := rfl
  rw [hc, ← RingHom.map_mulVec, torusB2_harmonic]
  simp

theorem torusHarmonic_ne : torusHarmonic ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by omega⟩
  simp [torusHarmonic, torusHarmonicZ] at this

/-- If a row `B e` (over `ℤ`) has its only nonzero entries at columns
`a, b` (distinct), then `((toQ B) *ᵥ w) e = B e a * w a + B e b * w b`. -/
theorem two_term_row {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (e : Fin m)
    (a b : Fin n) (hab : a ≠ b)
    (hsup : ∀ j, B e j ≠ 0 → j = a ∨ j = b) (w : Fin n → ℚ) :
    ((toQ B) *ᵥ w) e =
      ((B e a : ℤ) : ℚ) * w a + ((B e b : ℤ) : ℚ) * w b := by
  rw [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ {a, b})
      (fun j hj₁ hj₂ => ?_)]
  · rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    rfl
  · have hz : B e j = 0 := by
      by_contra hh
      rcases hsup j hh with rfl | rfl <;> simp at hj₂
    have : (toQ B) e j = 0 := by simp [toQ, hz]
    simp [this]

/-- Cast helper: `(toQ torusB2) e j` evaluates to the literal rational. -/
theorem torusB2Q_entry (e : Fin 21) (j : Fin 14) :
    (toQ torusB2) e j = (torusB2 e j : ℚ) := rfl

/-- Key kernel bound: every `w ∈ ker (torusB2 *ᵥ ·)` over `ℚ` with
`w 13 = 0` vanishes.  Each of the 21 edge equations involves exactly two
triangles; 13 of them form a spanning tree of the dual graph rooted at
triangle `13`, forcing `w = 0`. -/
theorem torusB2_ker_eq (w : Fin 14 → ℚ)
    (hx : (toQ torusB2) *ᵥ w = 0) (h13 : w ⟨13, by omega⟩ = 0) : w = 0 := by
  have eq : ∀ e : Fin 21, ((toQ torusB2) *ᵥ w) e = 0 := fun e => by
    rw [hx]; rfl
  -- Each `h` below: the support of row `e` is exactly the claimed pair.
  -- edge 19: triangles 3,13 with coeffs +1,+1 :  w3 + w13 = 0
  have e19 := eq ⟨19, by omega⟩
  rw [two_term_row _ _ ⟨3, by omega⟩ ⟨13, by omega⟩ (by decide) (by decide) w]
    at e19
  have w3 : w ⟨3, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨3, by omega⟩ + 1 * w ⟨13, by omega⟩ = 0 := by
      have e_e19_3 : ((torusB2 ⟨19, by omega⟩ ⟨3, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e19_13 : ((torusB2 ⟨19, by omega⟩ ⟨13, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e19_3, e_e19_13] at e19
    linarith
  -- edge 3: triangles 4,13 (+1,+1):  w4 + w13 = 0
  have e3 := eq ⟨3, by omega⟩
  rw [two_term_row _ _ ⟨4, by omega⟩ ⟨13, by omega⟩ (by decide) (by decide) w]
    at e3
  have w4 : w ⟨4, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨4, by omega⟩ + 1 * w ⟨13, by omega⟩ = 0 := by
      have e_e3_4 : ((torusB2 ⟨3, by omega⟩ ⟨4, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e3_13 : ((torusB2 ⟨3, by omega⟩ ⟨13, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e3_4, e_e3_13] at e3
    linarith
  -- edge 5: triangles 6,13 (-1,-1):  -w6 - w13 = 0
  have e5 := eq ⟨5, by omega⟩
  rw [two_term_row _ _ ⟨6, by omega⟩ ⟨13, by omega⟩ (by decide) (by decide) w]
    at e5
  have w6 : w ⟨6, by omega⟩ = 0 := by
    have h : (-1 : ℚ) * w ⟨6, by omega⟩ + -1 * w ⟨13, by omega⟩ = 0 := by
      have e_e5_6 : ((torusB2 ⟨5, by omega⟩ ⟨6, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      have e_e5_13 : ((torusB2 ⟨5, by omega⟩ ⟨13, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      rwa [e_e5_6, e_e5_13] at e5
    linarith
  -- edge 15: triangles 3,10 (+1,+1):  w3 + w10 = 0
  have e15 := eq ⟨15, by omega⟩
  rw [two_term_row _ _ ⟨3, by omega⟩ ⟨10, by omega⟩ (by decide) (by decide) w]
    at e15
  have w10 : w ⟨10, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨3, by omega⟩ + 1 * w ⟨10, by omega⟩ = 0 := by
      have e_e15_3 : ((torusB2 ⟨15, by omega⟩ ⟨3, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e15_10 : ((torusB2 ⟨15, by omega⟩ ⟨10, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e15_3, e_e15_10] at e15
    linarith
  -- edge 17: triangles 3,12 (-1,-1):  -w3 - w12 = 0
  have e17 := eq ⟨17, by omega⟩
  rw [two_term_row _ _ ⟨3, by omega⟩ ⟨12, by omega⟩ (by decide) (by decide) w]
    at e17
  have w12 : w ⟨12, by omega⟩ = 0 := by
    have h : (-1 : ℚ) * w ⟨3, by omega⟩ + -1 * w ⟨12, by omega⟩ = 0 := by
      have e_e17_3 : ((torusB2 ⟨17, by omega⟩ ⟨3, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      have e_e17_12 : ((torusB2 ⟨17, by omega⟩ ⟨12, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      rwa [e_e17_3, e_e17_12] at e17
    linarith
  -- edge 4: triangles 4,7 (-1,-1):  -w4 - w7 = 0
  have e4 := eq ⟨4, by omega⟩
  rw [two_term_row _ _ ⟨4, by omega⟩ ⟨7, by omega⟩ (by decide) (by decide) w]
    at e4
  have w7 : w ⟨7, by omega⟩ = 0 := by
    have h : (-1 : ℚ) * w ⟨4, by omega⟩ + -1 * w ⟨7, by omega⟩ = 0 := by
      have e_e4_4 : ((torusB2 ⟨4, by omega⟩ ⟨4, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      have e_e4_7 : ((torusB2 ⟨4, by omega⟩ ⟨7, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      rwa [e_e4_4, e_e4_7] at e4
    linarith
  -- edge 18: triangles 4,11 (+1,+1):  w4 + w11 = 0
  have e18 := eq ⟨18, by omega⟩
  rw [two_term_row _ _ ⟨4, by omega⟩ ⟨11, by omega⟩ (by decide) (by decide) w]
    at e18
  have w11 : w ⟨11, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨4, by omega⟩ + 1 * w ⟨11, by omega⟩ = 0 := by
      have e_e18_4 : ((torusB2 ⟨18, by omega⟩ ⟨4, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e18_11 : ((torusB2 ⟨18, by omega⟩ ⟨11, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e18_4, e_e18_11] at e18
    linarith
  -- edge 14: triangles 6,8 (+1,+1):  w6 + w8 = 0
  have e14 := eq ⟨14, by omega⟩
  rw [two_term_row _ _ ⟨6, by omega⟩ ⟨8, by omega⟩ (by decide) (by decide) w]
    at e14
  have w8 : w ⟨8, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨6, by omega⟩ + 1 * w ⟨8, by omega⟩ = 0 := by
      have e_e14_6 : ((torusB2 ⟨14, by omega⟩ ⟨6, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e14_8 : ((torusB2 ⟨14, by omega⟩ ⟨8, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e14_6, e_e14_8] at e14
    linarith
  -- edge 1: triangles 6,9 (+1,+1):  w6 + w9 = 0
  have e1 := eq ⟨1, by omega⟩
  rw [two_term_row _ _ ⟨6, by omega⟩ ⟨9, by omega⟩ (by decide) (by decide) w]
    at e1
  have w9 : w ⟨9, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨6, by omega⟩ + 1 * w ⟨9, by omega⟩ = 0 := by
      have e_e1_6 : ((torusB2 ⟨1, by omega⟩ ⟨6, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e1_9 : ((torusB2 ⟨1, by omega⟩ ⟨9, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e1_6, e_e1_9] at e1
    linarith
  -- edge 0: triangles 0,7 (+1,+1):  w0 + w7 = 0
  have e0 := eq ⟨0, by omega⟩
  rw [two_term_row _ _ ⟨0, by omega⟩ ⟨7, by omega⟩ (by decide) (by decide) w]
    at e0
  have w0 : w ⟨0, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨0, by omega⟩ + 1 * w ⟨7, by omega⟩ = 0 := by
      have e_e0_0 : ((torusB2 ⟨0, by omega⟩ ⟨0, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e0_7 : ((torusB2 ⟨0, by omega⟩ ⟨7, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e0_0, e_e0_7] at e0
    linarith
  -- edge 9: triangles 5,7 (+1,+1):  w5 + w7 = 0
  have e9 := eq ⟨9, by omega⟩
  rw [two_term_row _ _ ⟨5, by omega⟩ ⟨7, by omega⟩ (by decide) (by decide) w]
    at e9
  have w5 : w ⟨5, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨5, by omega⟩ + 1 * w ⟨7, by omega⟩ = 0 := by
      have e_e9_5 : ((torusB2 ⟨9, by omega⟩ ⟨5, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e9_7 : ((torusB2 ⟨9, by omega⟩ ⟨7, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e9_5, e_e9_7] at e9
    linarith
  -- edge 12: triangles 1,11 (+1,+1):  w1 + w11 = 0
  have e12 := eq ⟨12, by omega⟩
  rw [two_term_row _ _ ⟨1, by omega⟩ ⟨11, by omega⟩ (by decide) (by decide) w]
    at e12
  have w1 : w ⟨1, by omega⟩ = 0 := by
    have h : (1 : ℚ) * w ⟨1, by omega⟩ + 1 * w ⟨11, by omega⟩ = 0 := by
      have e_e12_1 : ((torusB2 ⟨12, by omega⟩ ⟨1, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      have e_e12_11 : ((torusB2 ⟨12, by omega⟩ ⟨11, by omega⟩ : ℤ) : ℚ) = 1 := by
        norm_num [torusB2]
      rwa [e_e12_1, e_e12_11] at e12
    linarith
  -- edge 13: triangles 2,11 (-1,-1):  -w2 - w11 = 0
  have e13 := eq ⟨13, by omega⟩
  rw [two_term_row _ _ ⟨2, by omega⟩ ⟨11, by omega⟩ (by decide) (by decide) w]
    at e13
  have w2 : w ⟨2, by omega⟩ = 0 := by
    have h : (-1 : ℚ) * w ⟨2, by omega⟩ + -1 * w ⟨11, by omega⟩ = 0 := by
      have e_e13_2 : ((torusB2 ⟨13, by omega⟩ ⟨2, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      have e_e13_11 : ((torusB2 ⟨13, by omega⟩ ⟨11, by omega⟩ : ℤ) : ℚ) = -1 := by
        norm_num [torusB2]
      rwa [e_e13_2, e_e13_11] at e13
    linarith
  funext i
  rw [show (0 : Fin 14 → ℚ) i = 0 from rfl]
  fin_cases i <;> assumption

/-- The kernel of `∂₂ *ᵥ ·` over `ℚ` is exactly the span of the harmonic
`2`-cycle. -/
theorem torusB2_ker_span :
    LinearMap.ker (Matrix.mulVecLin (toQ torusB2)) =
      Submodule.span ℚ {torusHarmonic} := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    have hc13 : torusHarmonic ⟨13, by omega⟩ = 1 := by
      simp [torusHarmonic, torusHarmonicZ]
    have hsub : (toQ torusB2) *ᵥ
        (x - x ⟨13, by omega⟩ • torusHarmonic) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, torusB2_harmonic_Q, hx]
      simp
    have h13 : (x - x ⟨13, by omega⟩ • torusHarmonic) ⟨13, by omega⟩ = 0 := by
      rw [Pi.sub_apply, Pi.smul_apply, hc13]
      simp
    have hw := torusB2_ker_eq _ hsub h13
    have hxeq : x = x ⟨13, by omega⟩ • torusHarmonic := by
      funext i
      have := congrFun hw i
      simp [Pi.sub_apply, Pi.smul_apply] at this ⊢
      linarith
    rw [hxeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact torusB2_harmonic_Q

/-- `toQ` commutes with transpose and multiplication. -/
theorem toQ_torusDN2 :
    toQ torusDN2 = (toQ torusB2)ᵀ * (toQ torusB2) := by
  rw [toQ, torusDN2, Matrix.map_mul]
  rfl

/-- The zero multiplicity of the `k = 2` DN operator on `T²` is `1`. -/
theorem zeroMult_torus : zeroMult torusDN2 = 1 := by
  rw [zeroMult, toQ_torusDN2]
  rw [Matrix.ker_mulVecLin_transpose_mul_self]
  rw [torusB2_ker_span]
  exact finrank_span_singleton torusHarmonic_ne

/-- `T²` is not a sphere triangulation: `χ = 7 − 21 + 14 = 0 ≠ 2`. -/
theorem torus_not_sphere : ¬ torusBoundary.IsTwoSphere := by
  rintro ⟨_, hχ⟩
  have : torusBoundary.eulerChar = 0 := by decide
  rw [this] at hχ
  norm_num at hχ

/-- Clause 2 "only if" fails: a non-sphere boundary can have multiplicity `1`. -/
theorem clause2_onlyif_fails :
    ¬ torusBoundary.IsTwoSphere ∧ zeroMult torusDN2 = 1 :=
  ⟨torus_not_sphere, zeroMult_torus⟩

/-- Main refutation of conjecture 00000004225:
(i) the zero-multiplicity need not equal the `k`-spanning-tree count
(`0 ≠ 16` on `∂Δ³` at `k = 1`);
(ii) a sphere boundary need not have multiplicity `1` (`∂Δ³`, `k = 1`, `0`);
(iii) a non-sphere boundary can have multiplicity `1` (`T²`, `k = 2`). -/
theorem disproof_00000004225 :
    zeroMult tetDN1 ≠ tetTreeCount
    ∧ (tetBoundary.IsTwoSphere ∧ zeroMult tetDN1 ≠ 1)
    ∧ (¬ torusBoundary.IsTwoSphere ∧ zeroMult torusDN2 = 1) :=
  ⟨clause1_tet_fails, clause2_if_fails, clause2_onlyif_fails⟩

end Submission00000004225
