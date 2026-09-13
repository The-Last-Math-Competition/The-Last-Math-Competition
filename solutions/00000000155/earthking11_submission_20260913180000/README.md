# Submission: disproof of conjecture 00000000155

**Conjecture (00000000155, English).** The only Bell primes are `B₂ = 2` and
`B₃ = 5`.

**Verdict: FALSE (refuted).**

## Summary

Using the *same* 0-indexed convention that the conjecture file itself fixes
(it writes `B₂ = 2`, `B₃ = 5`, matching OEIS A000110), the Bell numbers begin

| n | B_n | |
|---|-----|---|
| 0 | 1 | |
| 1 | 1 | |
| 2 | 2 | prime |
| 3 | 5 | prime |
| 4 | 15 | |
| 5 | 52 | |
| 6 | 203 | |
| 7 | 877 | **prime** |
| 8 | 4140 | |
| 9 | 21147 | |
| 10 | 115975 | |
| 11 | 678570 | |
| 12 | 4213597 | |
| 13 | 27644437 | **prime** |

The prime Bell numbers among `B₀..B₂₀` occur exactly at indices
`2, 3, 7, 13`. Hence the set of Bell primes is not `{2, 5}`: it also contains
`877` and `27644437`. There is no indexing shift that rescues the claim,
because the file's own equations `B₂ = 2` and `B₃ = 5` pin the convention.

## Files

| Path | Description |
|------|-------------|
| `main.tex` | Standalone article: Bell-number table, primality certificates for 877 and 27644437, refutation theorem. `tectonic --outdir build main.tex` produces `build/main.pdf`. |
| `reproduce.py` | Stdlib-only reproduction: Bell numbers to `n = 20`, trial-division primality, prints prime indices and PASS/FAIL (exit 0). |
| `lean4/Main.lean` | Core Lean 4 formalization (only `import Std`, no Mathlib, no `sorry`/`axiom`/`native_decide`). |
| `lean4/Check.lean` | `import Main` + `#print axioms` audit. |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1` |
| `lean4/lakefile.toml` | Lake package `tlmc155` (library `Main`). |
| `lean4/README.md` | Lean build instructions and audit output. |

## Reproduce

```sh
python3 reproduce.py                 # prints PASS, exits 0
cd lean4 && lake build               # exits 0
lake env lean Check.lean             # axiom audit
cd .. && tectonic --outdir build main.tex
```

## Formalized statement

`lean4/Main.lean` proves, in namespace `Tlmc155`:

* `bell_two : bell 2 = 2`
* `bell_three : bell 3 = 5`
* `bell_seven : bell 7 = 877`
* `bell_thirteen : bell 13 = 27644437`
* `prime_877 : isPrimeB 877 = true`
* `prime_27644437 : isPrimeB 27644437 = true`
* `conjecture_00000000155_false`, asserting that `bell 2 = 2`,
  `bell 3 = 5`, `bell 7` and `bell 13` are prime, and that `bell 7` and
  `bell 13` differ from both `bell 2` and `bell 3`.

All are closed by kernel reduction with `decide`; the axiom audit shows only
`propext` (for the `Nat` equalities) and no `sorryAx` or `ofReduceBool`.
