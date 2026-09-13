# Submission: refutation of conjecture 00000000807

**Conjecture (quoted).** Definition: The multiplicity of λ₁ on the torus T².
Conjecture: The maximal multiplicity of λ₁(T²) is 4 (attained only on the
square torus), and at most 3 for general lattices (multiplicity rigidity of
lattice spectra, partially known).

**Verdict: FALSE.**

## Summary of the refutation

For a flat two-torus `R²/Λ`, the Laplace eigenvalues are `4π²|k|²`, `k ∈ Λ*`,
so the multiplicity of the first non-zero eigenvalue equals the number of
shortest non-zero vectors of the dual lattice `Λ*`.

* Square lattice: `Λ* = Z²`, four shortest vectors `±e₁, ±e₂` → multiplicity **4**.
* Triangular lattice `Λ = Z(1,0) ⊕ Z(½, √3/2)`: the dual lattice has Gram
  matrix `G⁻¹ = [[4/3, -2/3], [-2/3, 4/3]]` and the six shortest non-zero
  vectors `±d₁, ±d₂, ±(d₁+d₂)`, all of squared length `4/3` → multiplicity **6**.
* The true maximum over all flat tori is **6**, attained exactly by lattices
  similar to the triangular one. Proof: all shortest vectors have equal length
  `r`; for distinct shortest `u, v`, `u − v` is a non-zero lattice vector, so
  `|u−v|² ≥ r²`, giving `⟨u,v⟩ ≤ r²/2`, i.e. the angle between any two is at
  least 60°. At most six points on a circle can be pairwise separated by at
  least 60° (2-dimensional kissing number). Equality forces all gaps to be 60°,
  hence the triangular lattice. Multiplicities are always even, so the only
  possible values are 2 (generic), 4 (square type), 6 (triangular type).
* Both clauses fail: the maximum is 6, not 4; the square torus is not the only
  maximiser (the triangular torus exceeds it); and "at most 3 for general
  lattices" is violated by the square torus (4) and the triangular torus (6).

## Files

| Path | Description |
|------|-------------|
| `README.md` | this file |
| `main.tex` | standalone article: dual-lattice computation, six shortest vectors, 60°/kissing-number argument, conclusion max = 6; compiled to `build/main.pdf` |
| `reproduce.py` | stdlib-only exact-arithmetic verification: triangular (6, |k|² = 4/3), square (4), generic (2), kissing-number check; prints PASS and exits 0 |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1` |
| `lean4/lakefile.toml` | Lake project `tlmc807` |
| `lean4/Main.lean` | core-Lean formalisation of the exact shortest-vector counts (no Mathlib, no `sorry`, no `axiom`, no `native_decide`) |
| `lean4/Check.lean` | `import Main` + `#print axioms` for each theorem |
| `lean4/README.md` | precise scope of the Lean formalisation |

## Reproduce

```bash
# exact-arithmetic verification (stdlib only)
python3 reproduce.py

# Lean formalisation
export PATH="$HOME/.elan/bin:$PATH"
cd lean4 && lake build
lake env lean Check.lean

# article
export PATH="/opt/homebrew/bin:$PATH"
mkdir -p build && tectonic --outdir build main.tex
```

## Formalisation scope

The Lean file formalises the exact integer shortest-vector counts for the
quadratic forms `Q(a,b) = a² + ab + b²` (triangular) and `S(a,b) = a² + b²`
(square):

* `tri_min`: `Q(a,b) ≥ 1` for every non-zero integer pair (positive
  definiteness), via the identity `4Q = (2a+b)² + 3b²`.
* `tri_six_shortest`: `Q(a,b) = 1` has exactly six solutions.
* `square_four_shortest`: `S(a,b) = 1` has exactly four solutions.
* `conjecture_00000000807_false`: `4 < 6`, plus a multiplicity strictly
  larger than 4.

The dual-lattice ↔ eigenvalue-multiplicity correspondence and the
60°/kissing-number bound are stated and proved in `main.tex` and checked
numerically in `reproduce.py`; they are **not** formalised in Lean (see
`lean4/README.md`).

## Uncertainty

The multiplicities are established unconditionally. The only non-Lean step is
the standard identification of the eigenvalue multiplicity with the number of
shortest dual vectors and the 60° bound; both are elementary and are written
out in `main.tex`. Verified by the project owner with exact arithmetic.
