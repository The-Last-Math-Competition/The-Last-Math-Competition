# Refutation of TLMC conjecture 00000004412

**Conjecture (verbatim).** The spectral distribution of an exchangeable
random graph limit is the spectral measure of its graphon integral operator.
*Conjecture:* The characteristic function of the expected spectral measure is
given explicitly by the **logarithm** of the Fredholm determinant of the
kernel, and the determinant series converges **if and only if** the kernel is
square integrable.

## Verdict: REFUTED (the conjunction fails)

### Conjunct (a): `φ(t) = log det(I − tT)` fails for every kernel

The two sides are structurally incompatible already at `t = 0`:

* `φ(0) = 1` — the characteristic function of *any* probability measure
  equals 1 at 0. For the graphon integral operator on a finite probability
  space `Fin m` (uniform measure, kernel `K`, `T = (1/m)K`) the expected
  spectral measure is the empirical eigenvalue law, so
  `φ(0) = (1/m) Tr I = 1`.
* `log det(I − 0·T) = log 1 = 0` — the log-determinant is *always* 0 at the
  expansion point.

So the conjectured identity reads `1 = 0` at `t = 0`, for **any** kernel —
exhibited on `completeGraphon` (the constant-1 graphon, complete-graph
limit). At nonzero `t` it is also impossible: `|φ(t)| ≤ 1` always, while
`Re log det(I − tT) = log∏|1 − tλⱼ|` is unbounded above as `|t|→∞` for any
`T` with a nonzero eigenvalue. (Numerically for a random 4×4 symmetric
kernel: `φ(20) ≈ 0.118 − 0.071i` while `Re log det(I − 20T) ≈ +6.74`.)

### Conjunct (b): "converges ⇒ square integrable" fails

For a rank-one kernel `K(x,y) = u(x)v(y)` every `n×n` determinant
`det[K(xᵢ,xⱼ)]` with `n ≥ 2` vanishes, so the Fredholm series collapses to
the polynomial `det(I − zT) = 1 − z∫uv`. Taking `u = 1`, `v(y) = y^{−3/4}`
on `[0,1]`: `∫v = 4` (finite) but `∫∫K² = ∫v² = ∫y^{−3/2}dy = +∞` — the
kernel is *not* square integrable, yet the Fredholm series (`1 − 4z`)
converges for all `z`. The "only if" direction is false.

## Files

* `lean4/Main.lean` — real definitions (`FiniteGraphon`, `intOp`,
  `spectralMoment`, `spectralCharFn`, `fredholmCoeff`, `fredholmDet`,
  `FredholmLogClaim`) and `theorem conjecture_refuted : ¬ FredholmLogClaim`.
* `lean4/Check.lean` — `#print axioms` audit (all theorems use only
  `propext`, `Classical.choice`, `Quot.sound`).
* `main.tex` / `build/main.pdf` — writeup.
* `reproduce.py` — numerical verification of both refutations.

## Reproduce

```bash
python3 reproduce.py            # prints VERDICT:REFUTED
cd lean4 && lake build          # builds Main.lean (Mathlib v4.33.1)
lake env lean Check.lean        # axiom audit
/opt/homebrew/bin/tectonic main.tex --outdir build
```
