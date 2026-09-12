# lean4 certification for the disproof of conjecture 00000000427

Toolchain: `leanprover/lean4:v4.33.1` (no external dependencies).

`Main.lean` (namespace `Tlmc0427`) enumerates all height functions of the
cubes, filters the monotone ones (recovering MacMahon's totals 2 and 20), and
proves, entirely by kernel `decide`/`rfl`:

- `macMahon2 : (planes.filter monoB).length = 20`
- `symCount2 : (planes.filter (fun t => monoB t && symB t)).length = 5`
  (mirror reading of diagonal symmetry)
- `cycSymCount2 : (planes.filter (fun t => monoB t && cycB t)).length = 5`
  (cyclic reading of diagonal symmetry)
- `formula2 : 2^{floor(4/4)} * (1!!/1!) * (3!!/2!) = 3` over `Q`
- `refute2 : the symmetric counts (5 and 5) differ from the formula value 3`
- `macMahon1`, `symCount1`, `formula1`, `refute1`: the `n = 1` case `2 != 1`

Zero axioms, zero `sorry`.

## Build and check

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem; each must report
"does not depend on any axioms".
