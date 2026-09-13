# Disproof of conjecture `00000000747`

**Verdict: FALSE.** The claim that for `p ≥ 5` the fixed points of `x ↦ x^p` in
`Z_p` are only `0` and `1` is false: the fixed point set has **exactly `p`
elements**, namely `{0} ∪ μ_{p-1}` (the Teichmüller roots), one per residue class
modulo `p`. For `p ≥ 5` that is at least `5` fixed points, not `2`.

## The conjecture

> **Conjecture `00000000747`.** For `p ≥ 5`, the iterative fixed points of
> `x ↦ x^p` in `Z_p` are only `0` and `1` (rigidity of superattracting orbits).

## Why it is false

A fixed point of `x ↦ x^p` is a solution of `x^p = x`, i.e. a root of

```
f(x) = x^p − x.
```

**Modulo `p`, every residue is a root.** By Fermat's little theorem, `a^p ≡ a
(mod p)` for all `a`; equivalently `x^p − x = ∏_{a∈F_p}(x − a)` in `F_p[x]`.
So there are already `p` roots modulo `p`.

**Each residue class lifts uniquely to `Z_p`.** The derivative is

```
f'(x) = p·x^{p−1} − 1 ≡ −1 (mod p),
```

a unit modulo `p`; so every root modulo `p` is *simple*, and Hensel's lemma
(simple-root form) gives exactly one root in `Z_p` in each of the `p` residue
classes. Hence there are exactly `p` fixed points,

```
{ x ∈ Z_p : x^p = x } = {0} ∪ μ_{p−1},    |μ_{p−1}| = p − 1.
```

For `p ≥ 5` this is at least `5` points, and in particular the set is not
contained in `{0, 1}`. The negation is already visible modulo `p`: all `p`
residues are fixed points of `x ↦ x^p` on `F_p`.

### The explicit `p = 5` example

- The unique Hensel lift of the residue class `2 mod 5` is

  ```
  α ≡ 280182 (mod 5^8),      since  280182^5 ≡ 280182 (mod 390625).
  ```

  It is `≡ 2 (mod 5)`, hence neither `0` nor `1`.

- The integer `110443` also satisfies

  ```
  110443^5 ≡ 110443 (mod 5^8),     110443 ∉ {0, 1} (mod 5^8).
  ```

  Note honestly: `110443 ≡ 3 (mod 5)`, so it is the Hensel lift of the residue
  class `3 mod 5`, **not** of class `2` (that one is `280182`). Either explicit
  value already refutes "only `0` and `1`".

Modulo `5^8` the roots include `0`, `1`, `280182`, `110443`, and there are
exactly `5` of them in all.

### The alternative reading `Z_p = Z/pZ`

If `Z_p` is instead read as `Z/pZ = F_p`, then `x^p = x` has **all `p`
residues** as roots by Fermat. For `p ≥ 5` that is at least `5` roots, so the
claim is false under the modulo-`p` reading as well.

## On the iterative / superattracting wording

- If "iterative fixed points" is read as points fixed by the `n`-th iterate
  `x ↦ x^{p^n}`, the equation becomes `x^{p^n} = x`, whose `Z_p`-solutions are
  `0` together with the `p^n − 1` roots of unity of order dividing `p^n − 1`,
  i.e. `p^n` points — even more than `p`. The claim fails a fortiori.
- The map under iteration is `g(x) = x^p`, with multiplier `g'(x) = p x^{p−1}`.
  At `x = 0` this is `0` (superattracting), but at every `x ∈ μ_{p−1}` it is
  `g'(x) = p`, of `p`-adic absolute value `p^{−1} < 1` (attracting, not
  superattracting). So "superattracting" selects only `0` and does not pick out
  the pair `{0, 1}`; the dynamical vocabulary does not change the count.

## Files

| file | purpose |
|---|---|
| `README.md` | this file |
| `main.tex` | the proof (LaTeX), including Fermat, the derivative, Hensel's lemma, the count `p`, and the explicit `p = 5` example |
| `build/main.pdf` | compiled PDF, built with `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact |
| `reproduce.py` | Hensel lifting and root counts for `p = 5, 7, 11` up to `p^8`; `python3 reproduce.py` exits 0 and prints `PASS` |
| `lean4/` | Lean 4 formalisation of the finite residue shadow, core Lean only (no Mathlib), no `sorry`; built with `lake build` and axiom-checked with `lake env lean Check.lean` |

## Reproducing

Pure Python 3, standard library only:

```bash
python3 reproduce.py
```

It counts the roots of `x^p = x` modulo `p^k` for `p = 5, 7, 11` and `k = 1..8`
and reports exactly `p` roots at every level, cross-validates the Hensel lifter
against brute-force enumeration on small moduli, tracks the lift of the class
`2 mod 5` to `5^8` (getting `280182`), checks the explicit root `110443`, and
prints a final `PASS`/`FAIL` summary.

To rebuild the PDF (requires `tectonic`):

```bash
tectonic --outdir build main.tex     # writes build/main.pdf
```

To build and check the Lean 4 project (pinned to `leanprover/lean4:v4.33.1`):

```bash
cd lean4
lake build
lake env lean Check.lean             # prints the axiom dependencies
```

## Scope and caveats

- **The Lean development does not formalise `Z_p`.** Core Lean has no `p`-adic
  integers. It formalises the decidable finite residue shadow: Fermat modulo
  `5`, the explicit root `110443` modulo `5^8`, and one concrete Hensel lifting
  step. The Hensel lemma that upgrades these facts to `Z_p`, and the resulting
  count `p`, are proved in `main.tex` and checked numerically by
  `reproduce.py`. See `lean4/README.md`.
- The conjecture uses asymptotic/dynamical language ("iterative fixed points",
  "superattracting orbits"). We interpret "fixed points of `x ↦ x^p`" in the
  standard way as solutions of `x^p = x`; we also check the two natural
  alternative readings (finite `Z/pZ`, and periodic points of iterates), and the
  claim is false under each.
- The one nuance worth flagging: the value `110443` is a genuine non-trivial
  root modulo `5^8`, but it lies in the residue class `3 mod 5`; the lift of the
  class `2 mod 5` is `280182`. Both are exhibited above.

## Status against the submission rules

Rule 3 requires a LaTeX source, a compiled PDF, and a Lean 4 project. All three
are present.

- **LaTeX source:** `main.tex`.
- **Compiled PDF:** `build/main.pdf`, built with
  `tectonic --outdir build main.tex` (tectonic 0.17.0) and checked in.
- **Lean 4 project:** `lean4/`, pinned to `leanprover/lean4:v4.33.1`, core Lean
  only (`import Std`, no Mathlib) with no `sorry`. It builds with `lake build`
  (exit 0) and `lake env lean Check.lean` reports no `sorryAx` and no
  `Lean.ofReduceBool`; the three closed finite facts depend on no axioms and
  `hensel_step_k1` only on `[propext, Quot.sound]`.

The Python script is a numerical cross-check, not a proof; the proof is the
Fermat + derivative + Hensel argument in `main.tex`.
