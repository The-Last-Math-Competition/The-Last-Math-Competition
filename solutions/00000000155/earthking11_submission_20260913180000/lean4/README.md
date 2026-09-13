# Lean 4 formalization (conjecture 00000000155)

Core Lean 4 only: `import Std`, no Mathlib, no `sorry`, no `axiom`, no
`native_decide`.  Toolchain: `leanprover/lean4:v4.33.1`.

## Build

```sh
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
```

Expected final line:

```
Build completed successfully (3 jobs).
```

## Contents of `Main.lean` (namespace `Tlmc155`)

* `bellRows` / `bell` — Bell numbers `B₀, B₁, …` computed with the Bell
  triangle (Aitken's array), structurally recursive so the kernel can reduce
  up to `n = 13`.
* `trialDiv` / `isPrimeB` — computable trial-division primality predicate.
  `trialDiv` recurses on an explicit fuel argument, so no well-founded
  recursion or tactic proof is needed and it reduces in the kernel.
* Theorems (all `by decide`):
  * `bell_two : bell 2 = 2`
  * `bell_three : bell 3 = 5`
  * `bell_seven : bell 7 = 877`
  * `bell_thirteen : bell 13 = 27644437`
  * `prime_877 : isPrimeB 877 = true`
  * `prime_27644437 : isPrimeB 27644437 = true`
  * `conjecture_00000000155_false : bell 2 = 2 ∧ bell 3 = 5 ∧
    isPrimeB (bell 7) = true ∧ isPrimeB (bell 13) = true ∧
    bell 7 ≠ bell 2 ∧ bell 7 ≠ bell 3 ∧ bell 13 ≠ bell 2 ∧
    bell 13 ≠ bell 3`

`set_option maxRecDepth 100000` is used to allow the kernel to reduce
`isPrimeB 27644437` (trial division up to `√27644437 < 5258`).

## Axiom audit

```sh
lake env lean Check.lean
```

Output:

```
'Tlmc155.bell_two' depends on axioms: [propext]
'Tlmc155.bell_three' depends on axioms: [propext]
'Tlmc155.bell_seven' depends on axioms: [propext]
'Tlmc155.bell_thirteen' depends on axioms: [propext]
'Tlmc155.prime_877' does not depend on any axioms
'Tlmc155.prime_27644437' does not depend on any axioms
'Tlmc155.conjecture_00000000155_false' depends on axioms: [propext]
```

Only `propext` appears (a standard Lean axiom, required by `decide` on `Nat`
equalities).  There is no `sorryAx` and no `ofReduceBool` (which would
indicate `native_decide`).
