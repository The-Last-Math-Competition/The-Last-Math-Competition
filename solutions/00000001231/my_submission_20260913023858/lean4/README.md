# Lean 4 verification — disproof of TLMC conjecture 00000001231

Core-only Lean 4 project (toolchain `leanprover/lean4:v4.33.1`, **no Mathlib**,
no external dependencies).

## What is proved

In namespace `Tlmc1231`:

- `tau_K4 : tau = 16` — the 3×3 principal minor `[[3,-1,-1],[-1,3,-1],[-1,-1,3]]`
  of the `K4` Laplacian (= `J(4,1)`) has determinant `16`; by the matrix-tree
  theorem this is the Jacobian order `|Jac(J(4,1))|`.
- `f_odd : ∀ i : Nat, (i * i - i + 1) % 2 = 1` — the parity lemma: every
  small factor `i² - i + 1` is odd (`i² - i` is a product of consecutive
  integers). **Unlimited version**, by induction.
- `prod_f4 : listProd ((List.range 4).map f) = 21` with `f i = i*i - i + 1`,
  `prod_f4_odd`, `sixteen_even : 16 % 2 = 0`, `prod_f4_ne_16`.
- `refute : ¬ (listProd (...) = 16 ∧ tau = 16)` — the parity-incompatible
  instance refuting the literal conjecture formula at `(n,k) = (4,1)`.

## Zero-axiom guarantee

Every theorem is proved with **zero axioms and no `sorry`**. To achieve this in
core Lean (where `omega`/`simp` would pull in `propext`/`Quot.sound`), the file
builds a small bespoke toolkit: `add_mul'`, `add_sub_cancel'`, `sub_add`, a
fuel-congruence theory of `Nat.modCore.go` (`go_congr`, `go_mod`,
`modCore_step`, `modCore_eq_mod`), and the `% 2` automaton
(`mod2_sub`, `mod2_step`, `mod2_add_dbl`), using only `rfl`, `rw` with
axiom-free core lemmas, `Nat.rec`-style induction and closed-term `decide`.

## Build and verify

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem and additionally runs a
`Lean.collectAxioms` meta-check that throws if any theorem depended on an
axiom. Expected output ends with:

```
'...' does not depend on any axioms   (for every theorem)
AXIOM CHECK PASSED: all theorems depend on no axioms
```

`.lake/` and `lake-manifest.json` are build artifacts and intentionally not
committed.
