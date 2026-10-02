# lean4 — zero-axiom Lean formalization of the disproof of 00000001046

Core Lean only (no Mathlib).  `GF(2^m) = GF(2)[α]/(f)` elements are encoded
as `Nat` literals in the polynomial basis (`α^i ↦ bit i`); field addition is
bitwise XOR, implemented by structural recursion on a fuel parameter so that
every definition reduces by plain kernel evaluation.

Contents of `Main.lean`:

| theorem | statement | meaning |
|---|---|---|
| `gf_inv16_ok` | table `gfInv16` matches carry-less `gfMul16` | the `GF(16)` model is a field |
| `attack_instance_16` | `diffCount16 1 0 = 4` | `a = 1, b = 0` has 4 solutions ⇒ `δ ≥ 4 > 2` |
| `attack_solutions_16` | solutions of `F16(x+1)+F16 x = 0` are exactly `{0,1,6,7}` | = `{0, 1, α^5, α^10}` in `GF(4) ⊂ GF(16)` |
| `delta_16` | `delta16 = 4` | full enumeration: differential uniformity over `GF(16)` is exactly 4 |
| `gf_inv32_ok` | table `gfInv32` matches carry-less `gfMul32` | the `GF(32)` model is a field |
| `attack_instance_32` | `diffCount32 1 0 = 2` | odd-`m` control |
| `attack_solutions_32` | solutions are exactly `{0,1}` | odd-`m` control |
| `delta_32` | `delta32 = 2` | full enumeration over `GF(32)`: exactly 2 (odd `m`) |

Build and audit (expect every theorem to report "does not depend on any
axioms"):

```sh
lake build
lake env lean Check.lean
```

Toolchain: `leanprover/lean4:v4.33.1`.  No `sorry`; no `decide` instances
(all proofs are `rfl` over closed literal computations); `#print axioms`
reports zero axioms for every theorem.
