# Disproof of conjecture 00000002160: the Higman–Sims graph does not attain the Hoffman bound

- **Conjecture.** "The independence number [of the Higman–Sims graph] equals the Hoffman bound, and the kernel of the bound is the Delsarte semilattice." The first conjunct is refuted, so the conjunction is false. The second conjunct has no standard meaning and is not used.
- **Hoffman bound.** For a `k`-regular graph on `n` vertices with least adjacency eigenvalue `λ_min`, the bound is `n·(−λ_min)/(k − λ_min)`. Hoffman's theorem says `α(G)` is at most this; "α equals the Hoffman bound" means equality.
- **Witness.** The Higman–Sims graph, built from S(3,6,22): `∞`, 22 points and 77 hexads. `∞` is adjacent to the points, a point to the hexads containing it, and two hexads are adjacent when they are disjoint. Lean checks (kernel `decide`, no `native_decide`) that the hexads form an S(3,6,22) and that the graph is `IsSRGWith 100 22 0 6`.
- **Spectrum.** For any srg(100,22,0,6), `A² = 22I + 6(J − I − A)` forces every eigenvalue into {22, 2, −8}. Since `tr A = 0`, the value −8 must occur. So `λ_min = −8`, and the Hoffman bound is `100·8/30 = 80/3`.
- **Conclusion.** `80/3` is not an integer, but `α(HS)` is, so `α(HS) ≠ 80/3`. Lean also checks that `α(HS) ≥ 22`. The known value `α(HS) = 22` is not formalised.
- **Main theorem.** `Conjecture2160.conjecture_2160_false : higmanSims.IsRegularOfDegree 22 ∧ (higmanSims.indepNum : ℝ) ≠ hoffmanBound higmanSims 22`.
- **Lean.** Lean 4.28.0, Mathlib v4.28.0. Axioms are only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no `native_decide`.

## Contents

| path | content |
|---|---|
| `main.tex` | full report (LaTeX source; the PDF was not compiled in this environment because no LaTeX bundle could be downloaded — run `pdflatex main.tex`) |
| `lean/` | Lean 4 project |
| `lean/Conjecture2160/HigmanSims.lean` | S(3,6,22) data, the graph `higmanSims`, `hexads_steiner`, `higmanSims_isSRG` |
| `lean/Conjecture2160/Spectral.lean` | `minAdjEigenvalue`, `hoffmanBound`, spectral lemmas for srg(100,22,0,6) |
| `lean/Conjecture2160/Main.lean` | `conjecture_2160_false`, `higmanSims_hoffmanBound`, `higmanSims_indepNum_ge` |
| `lean/Axioms.lean` | axiom audit |
| `gen_hs.py` | regenerates the hexads and adjacency bitmasks from the extended Golay code and re-checks S(3,6,22) and srg(100,22,0,6) |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002160.md` |
| `verification/` | build log and axiom output |

## Reproduce

```
cd lean
lake exe cache get
lake build          # HigmanSims.lean takes about 3 minutes (kernel computation)
lake env lean Axioms.lean
python3 ../gen_hs.py
```
