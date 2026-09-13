# Lean 4 formalisation (tlmc1096)

Lean 4 development refuting conjecture 00000001096. Core Lean + `Std` only —
**no Mathlib, no `sorry`, no `axiom`, no `native_decide`**. Since `ZMod` lives
in Mathlib, all arithmetic is done on `Nat` residues modulo 5.

Toolchain: `leanprover/lean4:v4.33.1` (pinned in `lean-toolchain`).

## Build

    export PATH="/opt/homebrew/bin:$PATH"
    cd lean4
    lake build                 # builds the `Main` library; exit 0
    lake env lean Check.lean   # prints the axiom dependencies

## Files

- `Main.lean` — all definitions and theorems (namespace `Tlmc1096`).
- `Check.lean` — `import Main`; `#print axioms` for each theorem.

## Mathematical set-up

n = 2, d = 2, q = 5. Six monomials `1, x, y, x², xy, y²` evaluated at the six
points `(0,0), (0,1), (0,2), (1,0), (1,1), (2,0)`, giving the 6×6
`Nat`-valued entry function `evalM : Fin 6 → Fin 6 → Nat`, each entry reduced
mod 5.

## What is formalised

1. `insertEverywhere`, `perms`, `permLists : List (List (Fin 6))` — the 720
   permutations of `Fin 6`, enumerated as lists.
2. `inversionsL`, `permSignL`, `prodOf`, and `detMod5 : Nat` — the determinant
   mod 5 via the Leibniz formula
   ∑_σ sign(σ)·∏_i M[i][σ(i)] mod 5.
3. `det_is_one : detMod5 = 1` — proved by `decide` (kernel computation over the
   720 permutations).
4. `f5`, `mkFun5`, `mkFun5_eta` — embedding of a 6-tuple of `Fin 5` into
   `Fin 6 → Fin 5`, and the eta lemma `mkFun5 (y 0) … (y 5) = y`.
5. `solveFun : (Fin 6 → Fin 5) → (Fin 6 → Fin 5)` — the explicit coefficient
   realiser taken from `M⁻¹` mod 5, i.e.
   `c = (y₀, y₀+2y₃+2y₅, y₀+2y₁+2y₂, 3y₀+4y₃+3y₅, y₀+4y₁+4y₃+y₄, 3y₀+4y₁+3y₂)`.
6. `shatters_components` — the **finite shattering check**, stated component-wise
   and proved by `decide`: for every labelling `(a₀,…,a₅) : Fin 5^6` and every
   point `i : Fin 6`, `evalAt (solveFun …) i = (labelling i)` — so the explicit
   coefficient vector realises the labelling. This covers all 5^6 = 15625
   labellings without search.
7. `shatters_six` — function-level restatement `evalAt (solveFun y) i = y i`,
   obtained from `shatters_components` by rewriting with `mkFun5_eta`.
8. `eval_map_bijective : ∀ y : Fin 6 → Fin 5, ∃ c : Fin 6 → Fin 5, ∀ i, …` —
   the generalised shattering statement (evaluation map surjective), with the
   explicit witness `solveFun y`.
9. `vc_at_least_six : 4 < 6`.
10. `conjecture_00000001096_false` — conjunction of (3), (8) and (9):
    `detMod5 = 1 ∧ (∀ y, ∃ c, …) ∧ 4 < 6`.

### Chosen form of the surjectivity proof

The task offered two options: a general `eval_map_bijective : ∀ y, ∃ x, …`, or,
if that is too hard without linear algebra, an explicit finite shattering check
over the 5^6 labellings. We do **both**, in the natural order: a closed
component-wise `decide` check (`shatters_components`) establishes that the
explicit inverse-matrix coefficients realise every labelling, and
`eval_map_bijective` is then derived with that explicit witness. We do **not**
derive surjectivity from `det ≠ 0` abstractly (that would need linear algebra
over `ZMod`/`Fintype`, unavailable in core Lean + `Std`); instead the inverse
matrix is exhibited explicitly.

## What is documented but not formalised

- The general definition of VC dimension for F_q-valued classes, and the
  claim that the VC dimension is **exactly** 6 (the Lean file proves ≥ 6; the
  matching upper bound is the dimension-count argument that a 6-dimensional
  function space cannot surject onto F_5^m for m > 6, stated in `main.tex` and
  the top-level `README.md`).
- The prose point that the classical VC notion is binary-only, so the conjecture
  requires the generalised reading (Definition 1 of `main.tex`).
- The explicit determinant/inverse computations in `reproduce.py` (independent
  cross-check of the Lean `decide` results).

## Axiom output

`lake env lean Check.lean` reports:

```
'Tlmc1096.det_is_one' depends on axioms: [propext]
'Tlmc1096.shatters_six' depends on axioms: [propext, Quot.sound]
'Tlmc1096.eval_map_bijective' depends on axioms: [propext, Quot.sound]
'Tlmc1096.vc_at_least_six' does not depend on any axioms
'Tlmc1096.conjecture_00000001096_false' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `ofReduceBool`; `propext` and `Quot.sound` are the standard
Lean axioms introduced by `decide`/`Fin`/list reasoning, not `sorry`.
