# Submission for conjecture 00000000750 — verdict: FALSE

**Claim under test.** For the `mod p^k` reduction of a `1`-Lipschitz map on
`Z_p`, the Mahler coefficient sequence `(a_n mod p^k)` is eventually periodic
with *exact* period `p^{k-1}(p-1)`, which cannot be shortened; this period is
attained simultaneously with the measure-preserving property of minimal maps.

**Result.** The conjecture is refuted by the map `f(x) = x + 1`.

- `f` is an isometry of `Z_p` (hence `1`-Lipschitz), preserves Haar measure,
  and is minimal (the orbit of `0` is `Z`).
- Its Mahler coefficients are `a_n = Δⁿ f(0)`, and since `Δ(x+1) = 1` is
  constant, `a_n = 0` for all `n ≥ 2`. Hence
  `(a_n) = (1, 1, 0, 0, 0, …)`, i.e. `x + 1 = C(x,0) + C(x,1)`.
- Reduced modulo `p^k` this sequence is eventually constant `0`, so its
  **minimal eventual period is 1**.
- The claimed value `p^{k-1}(p-1)` equals `2, 4, 2, 6, 4, 20` for
  `(p,k) = (2,2), (2,3), (3,1), (3,2), (5,1), (5,2)` — never `1`.
- More generally `p^{k-1}(p-1) = 1` (with `p > 1`, `k ≥ 1`) only for
  `(p,k) = (2,1)`.

**Supporting observation (not the refutation).** The conjecture quotes
Anashin's criterion as `p^n | a_n`. The criterion is actually
`p^{ν_p(n!)} | a_n`. The quoted form already fails for `f = x+1`, since
`p ∤ a_1 = 1` for every `p > 1`. This is only a remark on the wording; the
counterexample above refutes the period claim regardless.

## Contents

| Path | Description |
|------|-------------|
| `main.tex` | Standalone article: Mahler expansion, coefficient computation, periodicity argument, Anashin-criterion remark. |
| `reproduce.py` | Stdlib-only numeric check: finite-difference Mahler coefficients and period comparison; prints PASS, exits 0. |
| `lean4/Main.lean` | Core Lean 4 formalisation of the finite-difference core (`Int`/`Nat`, `import Std`, no Mathlib, no `sorry`/`axiom`/`native_decide`). |
| `lean4/Check.lean` | `#print axioms` for every theorem. |
| `lean4/lakefile.toml`, `lean4/lean-toolchain` | Build configuration; toolchain `leanprover/lean4:v4.33.1`. |
| `lean4/README.md` | Formalisation scope and build instructions. |

## Reproduce

```
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
tectonic --outdir build main.tex
```

`main.tex` builds to `build/main.pdf`.

## Honesty note

The Lean development covers the finite-difference / Mahler-coefficient core and
the period mismatch over `Int`/`Nat`. The `p`-adic topology, Haar measure,
the `1`-Lipschitz/isometry property, minimality of `x+1`, and the convergence of
the Mahler series are argued in `main.tex` and checked numerically in
`reproduce.py`, not formalised in Lean.
