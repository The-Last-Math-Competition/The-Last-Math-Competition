# Lean 4 formalisation — disproof of conjecture `00000001075`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can
confirm the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

`ZMod`, `Finset`, `Fintype`, `Complex`, and `Rat` are not available under
`import Std`, so the arithmetic is carried out in the ring of integers of
`Q(omega)` for `omega` a primitive fifth root of unity:
`Z[omega] = Z[x]/(x^4+x^3+x^2+x+1)`, represented as integer `4`-tuples
`(c0,c1,c2,c3)` standing for `c0 + c1*w + c2*w^2 + c3*w^3`. Multiplication is
the exact reduction with `w^4 = -(1+w+w^2+w^3)`: with `r0..r6` the plain
convolution coefficients,

```lean
⟨r0 - r4 + r5, r1 - r4 + r6, r2 - r4, r3 - r4⟩
```

There is no floating point anywhere.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `witness_supp` | `suppInt witness = 2` | `#supp(f) = 2` for `f = delta_0 - delta_1` |
| `witness_fhat_supp` | `suppQ (dft witness) = 4` | `f_hat(xi) = 1 - w^xi` vanishes only at `xi = 0` |
| `witness_equality` | `suppInt witness + suppQ (dft witness) = 6` | equality `q + 1` at `q = 5` |
| `witness_fhat_values` | `dft witness = (0, 1-w, 1-w^2, 1-w^3, 1-w^4)` | the exact transform values |
| `not_tfTrans_affine` | `forall (a b alpha beta : Fin 5), not (forall x, tfTrans (affineVec a b) alpha beta x = scalar (witness x))` | `f` is not a time-frequency translate of any affine function |
| `not_tfTrans_affine_dft` | same with `dftQ (tfTrans (affineVec a b) alpha beta)` | the transform of such a translate is not `f` either |
| `conjecture_00000001075_refuted` | conjunction of the above | the collected disproof |

## Proof strategy

- `witness : Fin 5 -> Int` is `x |-> if x = 0 then 1 else if x = 1 then -1
  else 0`, i.e. `(1,-1,0,0,0) = delta_0 - delta_1`.
- `dft f xi = sum5 (fun x => scalar (f x) * wpow (xi.val * x.val))`, where
  `sum5` is the explicit five-term sum and `wpow k` is `w^(k % 5)` with
  `w^5 = 1`. `dftQ` is the same transform for `Z[omega]`-valued inputs.
- `suppInt`/`suppQ` count the nonzero coordinates as sums of `if _ = 0 then 0
  else 1`.
- `affineVec a b x = scalar (((a*x+b : Fin 5).val : Int))` and
  `tfTrans h alpha beta x = wpow (beta.val * x.val) * h (x + alpha)`.
- All theorems are closed by `decide` (the finite `Fin 5` quantifiers and the
  `Int` arithmetic are decidable) or by `rw` with a previously decided lemma.
  `DecidableEq (Fin 5 -> Int)` does not exist in core Lean, so every function
  equality is phrased pointwise with `forall x, ...`; this is why the
  non-membership statements have that shape.
- No `native_decide` is used: it would introduce `Lean.ofReduceBool`, which
  the axiom audit in `Check.lean` excludes. `decide` suffices at these sizes
  (the whole project builds in a few seconds).

## Scope note

What the formalisation establishes, exactly:

1. `f = (1,-1,0,0,0)` on the five residues has `#supp(f) = 2` and
   `#supp(f_hat) = 4`, hence `#supp(f) + #supp(f_hat) = 6 = 5 + 1`: an
   equality configuration of the entropic uncertainty bound at `q = 5`, with
   support pair `(2,4)`, not the claimed `(5,1)`.
2. For every affine function `a*x+b` and every time-frequency translate
   `x |-> w^(beta*x) * h(x+alpha)`, the translate is not the witness; the same
   holds for the transform of such a translate. This is a finite check over
   `5^4 = 625` tuples in each case.

Because the whole argument is a finite computation over `Fin 5`, `decide` is
the entire proof method; no group-theoretic or Fourier-analytic
infrastructure is required. The quantifier over "all affine functions and all
translates" is `forall (a b alpha beta : Fin 5)`, which is exhaustive for
`Z/5`. The enumeration of all `243` functions `Z/5 -> {0,+-1}` and the split
`10/20/2` by support pair are reproduced exactly and in more detail by
`../reproduce.py`; the Lean development formalises the witness, the equality,
and the non-membership, which is the load-bearing core of the refutation.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. Observed
build time about 10 s on first build (largely elaboration of the `decide`
proofs), under 1 s for `Check.lean`.
