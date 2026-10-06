# Disproof of conjecture `00000005350`

**Verdict: false as stated.** Markov moves cannot realize a separation of
closed-knot types.  Each Markov move preserves the isotopy type of the braid
closure:

- conjugation `beta -> alpha beta alpha^{-1}` preserves the closure;
- stabilization/destabilization `beta <-> beta sigma_n^{+/-1}` preserves the
  closure.

Consequently any finite sequence—and in particular an explicit pair—of
Markov moves sends a braid to another braid with the same closed knot.  It is
therefore impossible for a pair of Markov moves to produce the conjectured
braids with different closures.

The categorified-invariant clause is immaterial: the stated Markov mechanism
already forces the closures to agree.  This is the preservation direction of
Markov's theorem, not a computational or classification assumption.

## Formal verification

The Lean project abstracts a Markov move as a relation whose defining property
is closure preservation.  It proves two moves preserve closure and rules out
any two-move witness with different closures.  A concrete finite instance is
included as an executable check.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
