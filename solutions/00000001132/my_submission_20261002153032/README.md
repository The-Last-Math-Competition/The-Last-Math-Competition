# Disproof of Conjecture 00000001132

**Conjecture (verbatim from `tlmc-fork/conjectures/00000001132.md`):** "Conjecture: The structure group of the tangent bundle of the complete flag variety reduces to a maximal torus if and only if G is a torus (a characterization of tangent-bundle triviality)."

**Verdict: FALSE.** Counterexample in rank 1: take **G = SL₂**.

## The mathematics

For any reductive `G` with Borel `B`, unipotent radical `U` and maximal torus `T = B/U`:

- The tangent bundle of the complete flag variety is the homogeneous bundle
  `T(G/B) ≅ G ×_B (𝔤/𝔟)`.
- The adjoint action of `B` on the line (rank `r₁`) space `𝔤/𝔟` factors through
  `B → B/U ≅ T`, because the unipotent radical `U` acts trivially on `𝔤/𝔟`.
- Hence **the structure group of `T(G/B)` reduces canonically to a maximal
  torus `T`, for every `G`** — the reduction exists even when `G` is far from
  being a torus.

For `G = SL₂(ℂ)`: `G/B ≅ P¹(ℂ)` and `T(P¹) ≅ O(2)` is a complex line bundle,
so its structure group is `ℂ* = G_m` — which *is* the maximal torus of `SL₂`
acting by the weight-2 character `t ↦ t²` (surjective onto `ℂ*`).  The
canonical `T`-reduction exists, yet `SL₂(ℂ)` is non-abelian and therefore not
a torus.  The "if and only if" fails; note also that the conjecture indeed
mischaracterizes triviality: `O(2)` has `c₁ = 2 ≠ 0` (non-trivial bundle) even
though its structure group is a torus.

## Machine-checked discrete certificate

The same algebraic mechanism is verified end-to-end, with zero axioms and zero
`sorry`, in the smallest faithful discrete model `G = SL₂(𝔽₂) = GL₂(𝔽₂)`
(`|G| = 6 ≅ S₃`, `𝔽₂* = {1}`; 3-point flag set):

- `U = [[1,1],[0,1]]`, `V = [[1,0],[1,1]]` ∈ G, and `U·V ≠ V·U` ⇒ G is
  non-abelian, hence **not a torus**;
- `B = {I, U}` (both self-inverse); `𝔤/𝔟` is 1-dimensional over `𝔽₂` with
  coordinate the bottom-left entry; for **all 16** `X ∈ 𝔤` and both `b ∈ B`,
  the class of `b·X·b⁻¹` equals the class of `X` ⇒ the transition functions of
  the associated tangent bundle `G ×_B (𝔤/𝔟)` are the identity, i.e. take
  values in the image of the maximal torus `T = {diag(1,1)}` ⇒ **the structure
  group reduces to a maximal torus**.

Main Lean theorem: `conjecture_00000001132_false : ¬ (ReducesToMaximalTorus ↔ GroupIsAbelian)`.

## Files

- `main.tex` — the disproof note (build: `tectonic main.tex`).
- `reproduce.py` — recomputes every attack number; run `python3 reproduce.py`.
- `lean4/Main.lean` — self-contained Lean 4 (no dependencies), all proofs by
  `rfl`/`decide` on explicit `Bool` data.
- `lean4/Check.lean` — `#print axioms` audit of every theorem.

## Reproduce

```bash
python3 reproduce.py                              # all checks PASS
cd lean4 && lake build && lake env lean Check.lean # every theorem: "does not depend on any axioms"
```

## Axiom audit

`#print axioms` on all ten theorems reports **"does not depend on any axioms"**
— no `propext`, no `Classical.choice`, no `Quot.sound`, zero `sorry`.
