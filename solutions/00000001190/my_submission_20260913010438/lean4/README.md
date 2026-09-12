# Lean 4 machine-checkable disproof (conjecture 00000001190)

Toolchain: `leanprover/lean4:v4.33.1` (core Lean only, no Mathlib).

## Model

`F_7` is represented by the residues `{0,1,…,6}` in `Nat` with explicit `% 7`
arithmetic in `mul` / `det` — the same ring as `ZMod 7`, so all element counts
coincide (core Lean has no `ZMod`; `Fin 7` would work too, but the residue
model keeps everything plain `Nat`). A 2x2 matrix is the nested pair
`(a, b, c, d)` standing for `[[a, b], [c, d]]`; multiplication and
`det = a*d - b*c (mod 7)` are plain `def`s (computable functions). The list
`matrices` enumerates all `7^4 = 2401` matrices by four-fold `List.range 7`
combination via `List.flatMap`.

## Checked statements (all by `decide`, zero axioms, zero `sorry`)

| theorem | statement | meaning |
|---|---|---|
| `count_gl2`  | `(matrices.filter isGl).length = 2016` | `|GL_2(F_7)| = 2016` |
| `count_order2` | `... length = 57` | 56 + 1 = 57 involutions |
| `count_order3` | `... length = 170` | 3 · 56 + 2 = 170 elements of order 3 |
| `formula2`   | `theta2 = 49` (`rfl`) | the conjecture claims `N_2 = Θ_2(7) = 49` |
| `refute`     | `57 ≠ 49 ∧ 170 ≠ 0` | the "zero error" claim fails twice |
| `refute_counts` | enumerated counts differ from 49 and 0 | same, tied to the enumeration |

## Build and audit

```bash
lake build            # compiles Main.lean; every theorem by decide
lake env lean Check.lean
```

`Check.lean` prints the three counts (2016, 57, 170), the formula value (49),
and for every theorem:

```
'Tlmc1190.count_order2' does not depend on any axioms
...
```

`set_option maxHeartbeats 1000000` and `set_option maxRecDepth 100000` are set
at file level for the kernel evaluation of the 2401-element enumeration.
