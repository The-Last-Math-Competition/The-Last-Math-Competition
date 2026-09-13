# Lean formalisation (`tlmc982`)

Core Lean 4 only (`import Std`), **no Mathlib**, no `sorry`, no `axiom`, no
`native_decide` / `ofReduceBool`. Toolchain:
`leanprover/lean4:v4.33.1` (see `lean-toolchain`).

## Build

```sh
lake build                  # builds library Main (default target)
lake env lean Check.lean    # prints #print axioms for every theorem
```

## Files

* `Main.lean` — the lattice model and all theorems.
* `Check.lean` — `import Main` plus one `#print axioms` per theorem.

## Scope: what is formalised vs. what is documented

Core Lean 4 has **no `ℝ`/`ℂ` and no integration**, so the Fock-space integral
and the convolution identity `B = e^{Δ/4}` cannot be formalised here. This file
therefore splits the refutation into:

* **Formalised (kernel-checked, `decide`):** the two structural facts the
  refutation turns on, over the integer lattice `ℤ × ℤ ⊂ ℂ` (which already
  suffices for the distinguishing computations):
  * `nonradial_witness` / `z_not_radial`: there exist two lattice points with
    equal squared modulus but different values under `z ↦ z`, so `z` is not
    radial;
  * `one_ne_z`, `one_ne_sq`, `z_ne_sq` / `three_distinct_functions`: the
    functions `1`, `z`, `z²` are pairwise distinct; hence any fixed set
    containing them has cardinality at least `3 > 2`.
* **Documented (not formalised here):** the convolution identity
  `B f(z) = (1/π)∫ f(z+u)e^{-|u|²}dA(u) = e^{Δ/4} f(z)`, the fact that
  `e^{Δ/4}` fixes every harmonic function (hence every holomorphic function in
  `F²`), and therefore that `z`, `z²`, … are fixed. These are proved in
  `../main.tex` and verified numerically in `../reproduce.py`. The Lean file
  cannot prove them because core Lean lacks the real/complex numbers and
  measure/integration theory.

The theorem `conjecture_00000000982_false` below is therefore a *conditional*
encapsulation: given the documented analytic fact that `B` fixes every
holomorphic function in `F²` (so `z`, `z²` are fixed points), the Lean-proved
non-radiality of `z` and the pairwise distinctness of `1, z, z²` show that both
claims of the conjecture fail (non-radial fixed point; fixed set of size
`≥ 3 > 2`).

## Model

* Points are `Int × Int`, with squared modulus
  `sqmod p = p.1*p.1 + p.2*p.2`.
* `RadialInt g` is the literal predicate `∀ p q, sqmod p = sqmod q → g p = g q`
  on `Int`-valued functions; `Radial g` is the same definition with an
  arbitrary codomain, used for the `ℂ`-valued coordinate functions modelled as
  `Int × Int`-valued (real and imaginary parts).
* `idZ p = p` models `z ↦ z`; `constOne = (1,0)` models the constant `1`;
  `sqZ p = (p.1² − p.2², 2 p.1 p.2)` models `z ↦ z²`.

## Theorems

| Theorem | Statement |
| --- | --- |
| `nonradial_witness` | `∃ p q : Int × Int, sqmod p = sqmod q ∧ p ≠ q` (witness `(1,0)`, `(0,1)`) |
| `z_not_radial` | `¬ Radial idZ` |
| `one_ne_z` | `constOne ≠ idZ` (differ at `(0,0)`) |
| `one_ne_sq` | `constOne ≠ sqZ` (differ at `(0,0)`) |
| `z_ne_sq` | `idZ ≠ sqZ` (differ at `(2,0)`) |
| `three_distinct_functions` | `constOne ≠ idZ ∧ constOne ≠ sqZ ∧ idZ ≠ sqZ` |
| `conjecture_00000000982_false` | conjunction of the above |

## Axiom audit

Running `lake env lean Check.lean` prints

```
'Tlmc982.nonradial_witness' does not depend on any axioms
'Tlmc982.z_not_radial' does not depend on any axioms
'Tlmc982.one_ne_z' does not depend on any axioms
'Tlmc982.one_ne_sq' does not depend on any axioms
'Tlmc982.z_ne_sq' does not depend on any axioms
'Tlmc982.three_distinct_functions' does not depend on any axioms
'Tlmc982.conjecture_00000000982_false' does not depend on any axioms
```

In particular there is no `sorryAx` and no `ofReduceBool`.
