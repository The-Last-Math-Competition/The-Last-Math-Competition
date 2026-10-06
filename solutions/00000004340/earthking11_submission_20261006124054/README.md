# Disproof of conjecture `00000004340`

**Verdict: false.** Every existing odd moment of a centrally symmetric measure
is zero.  If `mu` is invariant under `x -> -x`, then for every `k >= 0`,

```text
integral x^(2k+1) dmu(x)
  = integral (-x)^(2k+1) dmu(x)
  = - integral x^(2k+1) dmu(x),
```

so the moment equals its negative and is therefore `0`.  Thus two centrally
symmetric measures automatically have identical odd moments—all zero—whether
or not their even moments coincide.

A symmetry-breaking perturbation cannot repair the claimed example: once the
perturbation produces a nonzero odd moment, the resulting measure is no longer
centrally symmetric and has left the conjecture's stated class.

## Formal verification

`lean4/Main.lean` represents the moment sequence together with the consequence
of central symmetry that every odd-index moment vanishes.  It proves no pair
of such sequences can differ at an odd moment, and separately checks finite
paired supports `+a,-a` cancel in their first odd moment.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
