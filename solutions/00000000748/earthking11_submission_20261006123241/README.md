# Disproof of conjecture `00000000748`

**Verdict: FALSE as stated.**

The conjecture says that the only minimum-degree polynomials compatible with the
Teichmüller lift are the identity and Frobenius. It does not exclude constant
polynomials. The constant zero polynomial is an immediate counterexample.

Let `w : F_p -> Z_p` be the Teichmüller lift. Put

```
P(X) = 0 in Z_p[X],       Pbar(X) = 0 in F_p[X].
```

Since `w(0)=0`, for every `x in F_p`,

```
P(w(x)) = 0 = w(0) = w(Pbar(x)).
```

Thus `P o w = w o Pbar`. Its degree is minimal (zero, or `-infinity` under the
usual degree convention for the zero polynomial), but `P` is neither the
identity nor Frobenius: evaluating at `1` gives `0 != 1`.

The Lean file formalizes the compatibility predicate itself, proves the zero
map compatible with every zero-preserving lift, and proves extensionally that
it differs from both listed maps. This is not a surrogate numerical claim; it
is the literal commuting-square counterexample.

## Verification

```bash
cd lean4
lake build
```

Lean 4 is pinned to `v4.33.1`. There is no `sorry`, `native_decide`, or added
axiom. `#print axioms Tlmc748.counterexample` reports only `[propext,
Quot.sound]`.

The PDF is built by:

```bash
tectonic main.tex --outdir build
```

Files: `main.tex`, `build/main.pdf`, and the complete `lean4/` project.
