# Conjecture 00000002821: nonconvex sublevels of a genuine good LDP rate

The proof uses the constant symmetric law on `{−1, 1}`, at speed `n+1`.
Its proper good rate is zero at the two atoms and infinity elsewhere.
Every finite nonnegative sublevel, and the exact zero level, is compact and
nonconvex. The full LDP, including probability-zero events, is formally proved.

Read `report.tex` for the full argument and the precise scope of the disproof.
The source's undefined extreme-point growth and affine-degeneration wording
is not silently assigned an invented definition.

## Build

Use the pinned `lean-toolchain` and `lake-manifest.json` with network access
or a locally available copy of the pinned packages. Run:

```sh
lake exe cache get
bash verify.sh
```

The cache step is optional when compiled dependencies are already available.
`verify.sh` runs `lake build`, then replays every authored Lean file with
warnings treated as errors. The main root also prints axiom dependencies.
All printed axiom lists are `propext`, `Classical.choice`, and `Quot.sound`.

The main theorem is `Conjecture2821.counterexample`; the explicit universal
negation is `Conjecture2821.not_all_good_ldp_sublevels_convex`.
There are no mathematical auxiliary computations.
