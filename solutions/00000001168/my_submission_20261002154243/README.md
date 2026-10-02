# Disproof of TLMC Conjecture 00000001168

**Verdict: FALSE.** The round metric on SU(2) ≅ S³ is itself a Zoll metric,
and its first nonzero Laplace eigenvalue has multiplicity 4 > 2.

## The conjecture

> Definition: A Zoll metric is one all of whose geodesics are closed.
> Conjecture: The spectral multiplicity upper bound for Zoll metrics on
> SU(2) is two; and the counterexample to multiplicity rigidity is the
> family of rotated round metrics. (Zoll multiplicity rigidity)

(原文:「Zoll 度量为一切测地线闭的度量。猜想：SU(2) 上 Zoll 度量的谱重数上界为二；且重数刚性的反例为圆度量旋转族。」)

## Attack: the conjecture's own example violates its own bound

Identify SU(2) with the unit quaternions, i.e. the round unit sphere
S³ ⊂ R⁴.

- **The round metric is Zoll by the conjecture's own definition.** Every
  geodesic is a great circle γ(t) = cos(t)u + sin(t)v with u, v orthonormal,
  closed with the common period 2π (`reproduce.py` verifies unit speed, the
  geodesic equation γ″ + γ = 0, and 2π-periodicity for 200 sampled great
  circles).
- **Spectrum of the round S³.** The eigenvalues are λ_k = k(k+2) with
  multiplicities (k+1)²: the λ_k-eigenspace is the restriction of the
  degree-k harmonic homogeneous polynomials on R⁴, of dimension
  C(k+3,3) − C(k+1,3) = (k+1)².
- **Independent recomputation.** Rather than trusting the formula,
  `reproduce.py` assembles the flat Laplacian Δ: Hom_k → Hom_{k−2} as an
  explicit matrix over Q (via ∂²/∂x_i² x^a = a_i(a_i−1) x^{a−2e_i}) and
  computes kernel dimensions by exact rational Gaussian elimination for
  k = 0..8. Every Δ is surjective and every kernel has dimension exactly
  (k+1)²: multiplicities **1, 4, 9, 16, 25, 36, 49, 64, 81** at λ = 0, 3, 8,
  15, 24, 35, 48, 63, 80.
- **The k = 1 case explicitly.** λ₁ = 3; the eigenspace contains the four
  coordinate functions x₁,…,x₄ restricted to S³ (linear forms are harmonic),
  and they are linearly independent — the evaluation matrix at the four axis
  points e₁,…,e₄ is the identity. So mult(λ₁) = 4 > 2.
- **Every nonzero eigenvalue violates the bound:** multiplicities
  4, 9, 16, … for k = 1, 2, 3, … are all > 2. The claimed "upper bound two"
  is false.

## The "counterexample family" clause is also broken

A rotation Q ∈ SO(4) preserves round distances (QᵀQ = I; verified for 50
sampled rotations at 20 point pairs each), so Q*g_r = g_r **identically**:
the "family of rotated round metrics" is a single isometry class with a
single spectrum, mult(λ_k) = (k+1)² on every member. The conjecture's
proposed counterexample family therefore violates the claimed upper bound on
every member — the two clauses of the conjecture are jointly inconsistent,
and each fails: the bound is false, and the cited family witnesses against
it rather than for it. One Zoll metric on SU(2) with an eigenvalue
multiplicity of 4 refutes the universal claim.

## Boundary

- **Scale:** a round metric of any radius has eigenvalues k(k+2)/r² with the
  same multiplicities (k+1)²; every bi-invariant metric on SU(2) is round.
- The attack does not say all Zoll metrics on SU(2) have large multiplicities
  (generically one expects simple spectrum); it refutes the *universal upper
  bound of two* using a Zoll metric the conjecture itself points at.

## Reproduction

- `python3 reproduce.py` — recomputes every number above (exact rational
  kernel dimensions, monomial counts, axis evaluation identity, great-circle
  sampling, rotation sampling); exits 0 on success.
- `lean4/` — machine-checked formalization in pure Lean 4 (no Mathlib, no
  axioms, no `sorry`): eigenvalue/multiplicity tables, the explicit k = 1
  case, coordinate-function independence, and the rotation isometry; see
  `lean4/README.md`.
- `main.tex` / `build/main.pdf` — full write-up.
