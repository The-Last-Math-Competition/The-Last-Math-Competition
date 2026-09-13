# Refutation of conjecture 00000000982

**Verdict: FALSE.**

Conjecture (from `conjectures/00000000982.md`): *Fixed points of the Berezin
transform on Fock space are radial functions, and the cardinality of the
fixed-point set is at most 2.*

On the Fock space with the Gaussian measure `(1/π) e^{-|w|²} dA(w)`, the
(diagonal) Berezin transform is the Gaussian convolution

```
B f(z) = (1/π) ∫_ℂ f(w) e^{-|w-z|²} dA(w) = (1/π) ∫_ℂ f(z+u) e^{-|u|²} dA(u)
       = e^{Δ/4} f(z).
```

Expanding `f(z+u)` in Taylor series and using the Gaussian moments
`(1/π)∫ u^m ū^n e^{-|u|²} dA = m! δ_{mn}` (proved in `main.tex`) gives the
identity. Consequences:

1. **The fixed set is not contained in the radial functions.** The function
   `f(z) = z` lies in the holomorphic Fock space `F²` (indeed `‖z‖² = 1`), is
   holomorphic hence harmonic, and is fixed (`Bz = z`). It is manifestly not
   radial: `|1| = |i| = 1` but `z(1) = 1 ≠ i = z(i)`.
2. **The cardinality is not at most 2.** Every entire function is harmonic and
   is fixed; in particular `1, z, z²` are three distinct fixed points, and `z^k`
   is fixed for every `k ≥ 0`, so the fixed set is infinite.

**Correction / caution.** Do *not* cite `Re z` or `Im z` as elements of the
holomorphic Fock space `F²`. They are harmonic (and fixed), but they lie only in
the ambient `L²(ℂ, (1/π)e^{-|w|²} dA)` and *not* in `F²`. The correct in-`F²`
witness is `f(z) = z`.

**Strongest objection (stated honestly).** If "on Fock space" were read as the
space of *bounded symbols* (the Toeplitz algebra), then bounded harmonic
functions on `ℂ` are constant by Liouville's theorem, so the fixed set would be
the constants — radial, of cardinality `1` — and the conjecture would be a
garbled statement of a true fact. Under the literal reading ("on Fock space",
i.e. in `F²`), the statement is false as shown.

## Contents

| Path | Description |
| --- | --- |
| `main.tex` | Standalone article: Fock space, the convolution identity, the harmonic-kernel characterisation, the non-radial witness `z`, the infinite fixed set, and the bounded-symbol objection. |
| `reproduce.py` | Stdlib-only numerical evaluation of `B` by tensor Gauss–Hermite quadrature; verifies `B(1)=1`, `B(z)=z`, `B(z²)=z²`, `B(z³)=z³`, the harmonic cross-check `B(z+z̄)=z+z̄`, the negative control `B(|z|²)=|z|²+1`, and the non-radiality of `z`. Prints errors and `PASS`/`FAIL`, exits `0`. |
| `lean4/` | Core-Lean (no Mathlib) machine-checked formalisation of the distinguishing finite facts. |
| `build/main.pdf` | Compiled article. |

## Reproduce

```sh
python3 reproduce.py                    # numerical checks, PASS/FAIL, exit 0
cd lean4 && lake build                  # builds the formalisation
lake env lean Check.lean                # prints the axiom audit
tectonic --outdir build main.tex        # from the submission root; writes build/main.pdf
```

## Lean formalisation

`lean4/Main.lean` models lattice points as `Int × Int ⊂ ℂ` and proves, by
kernel `decide` (no `sorry`, no `axiom`, no `native_decide`):

* `nonradial_witness` — `∃ p q, p.1*p.1 + p.2*p.2 = q.1*q.1 + q.2*q.2 ∧ p ≠ q`;
* `z_not_radial` — the coordinate function `z(p) = p` is not radial;
* `one_ne_z`, `one_ne_sq`, `z_ne_sq` — `1`, `z`, `z²` are pairwise distinct
  (evaluated at `(0,0)`, `(0,0)`, `(2,0)` respectively);
* `three_distinct_functions` and the collected
  `conjecture_00000000982_false`.

Core Lean has no `ℝ`/`ℂ` and no integrals, so the analytic content (the identity
`B = e^{Δ/4}` and "`B` fixes every holomorphic function in `F²`") is *documented*
in `lean4/README.md`, proved in `main.tex`, and checked numerically in
`reproduce.py`; the Lean file formalises only the distinguishing structural
facts that the refutation turns on. See `lean4/README.md` for the exact scope.
