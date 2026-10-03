# Refutation of TLMC Conjecture 00000004225

**Claim.** For the higher Dirichlet–Neumann (boundary-response) operator on
`k`-chains of a boundary complex `B = ∂M`:
1. `mult_0(B) = τ_k(B)` — the multiplicity of the zero eigenvalue equals the
   count of `k`-spanning trees of `B`; and
2. the multiplicity is `1` iff `B` is a sphere triangulation.

**Verdict: FALSE** — refuted on both clauses and in both directions of the
biconditional.

## Mathematical idea

The higher DN operator on `k`-chains is the Hodge Laplacian
`Δ_k = ∂_{k+1} ∂_{k+1}ᵀ + ∂_kᵀ ∂_k`. Its kernel is the space of harmonic
`k`-chains, so `mult_k(B) = β_k(B)` (a *kernel dimension*), whereas the
simplicial spanning-tree count `τ_k(B)` is *determinantal* (Kalai's
matrix-tree theorem: a weighted product of the nonzero eigenvalues). The two
quantities differ in type and value.

### Counterexample A — `∂Δ³`, a sphere, at `k = 1`
`(f₀,f₁,f₂) = (4,6,4)`, `χ = 2`. Direct computation:
`Δ₁ = 4·I₆`, `det = 4096`, so `mult₁ = 0`; but `τ₁ = τ(K₄) = 16` (Cayley).
- Clause 1 fails: `0 ≠ 16`.
- "If" direction of clause 2 fails: a sphere boundary has `mult₁ = 0 ≠ 1`.

### Counterexample B — 7-vertex torus `T²` (boundary of solid torus), `k = 2`
`(f₀,f₁,f₂) = (7,21,14)`, `χ = 0 ≠ 2`, so `T²` is not a sphere.
`Δ₂ = ∂₂ᵀ∂₂` on `C₂ ≅ ℚ¹⁴`; explicit harmonic `2`-cycle
`c = (-1,…,-1,+1,…,+1)` plus a dual-tree elimination over the 21 edge
equations gives `ker Δ₂ = span{c}`, hence `mult₂ = β₂(T²) = 1`.
- "Only if" direction fails: a non-sphere boundary attains multiplicity `1`.
- Clause 1 fails again: `τ₂ = 0` (a `2`-tree would need `rank ∂₂ = f₂ = 14`,
  but `rank ∂₂ = 13`), so `1 ≠ 0`.

## Layout

```
README.md            this file
main.tex             write-up source
build/main.pdf       compiled write-up (tectonic)
reproduce.py         exact-arithmetic verification (sympy)
lean4/               Lean 4 + Mathlib v4.33.1 project
  Main.lean          definitions + disproof_00000004225
  Check.lean         #print axioms audit
  lakefile.toml      Mathlib v4.33.1 pin
  lean-toolchain     leanprover/lean4:v4.33.1
  .gitignore         .lake/ and lake-manifest.json
```

## Reproduce

```bash
# Numerical check (stdlib + sympy)
python3 reproduce.py          # prints "ALL CHECKS PASSED -- conjecture is FALSE"

# Lean 4 + Mathlib
cd lean4
export ELAN_HOME=... ; export PATH="$ELAN_HOME/bin:$PATH"
lake build                    # builds Main (mathlib is a required dependency)
lake env lean Check.lean      # axiom audit: propext, Classical.choice, Quot.sound

# PDF
tectonic main.tex --outdir build
```

## Axiom audit

`Check.lean` prints axioms for every theorem. All depend only on the ambient
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no
`ofReduceBool`, no `trustCompiler`.
