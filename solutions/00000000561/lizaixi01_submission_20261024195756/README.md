# Problem 00000000561: finite-denominator obstruction

The actual connected quadratic square-zero algebra is `A = TrivSqZeroExt Q (Fin 2 -> Q)`, with two degree-one generators. Its full minimal linear free resolution is constructed in every degree and packaged as a native `ProjectiveResolution`. Native Ext comparison and canonical Q-linear equivalences derive `finrank Ext_A^n(Q,Q)=2^n`; the genuine Hilbert formal power series satisfies `(1-2t)H=1`.

For every finite family of positive integers, allowing repetitions and the empty family, no polynomial numerator can satisfy `product_i(1-t^d_i) * H = P`. The actual polynomial identity forced by this equation is evaluated at `1/2` to give a contradiction.

**Scope:** the printed product has no index set. This submission uses the usual finite polynomial meaning of a rational-function denominator and attacks only that conjunct. It does not deny this example's rationality, or an infinite formal Euler-product representation. Ordinary `N=2` is not excluded by the printed source. The native resolution provides the defining linear/minimal graded criterion for 2-Koszul; no external Hilbert-series theorem is imported as an axiom. The formalization computes actual graded native Yoneda Ext spaces and includes native Yoneda composition; it does not need or construct a separate bundled total Yoneda ring.

`SOURCE.md` retains the complete original English and Chinese statement. `report.tex` and `report.pdf` contain the complete mathematical argument and the exact definition/model boundary. `lean/` is the complete pinned project. `evidence/` and `SHA256SUMS.json` retain source-bound verification and file hashes.

Runtime: Lean4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

From `lean/`, reproduce all four checks:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

After `lean --version`, `./verify.sh` runs the remaining three. The namespace audit enumerates all actual names, including generated helpers, and calls ordinary `#print axioms` for every one; its coverage and exact printed-name equality are checked. Allowed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

The original production verification uses CPUs0,2 with2 threads and preserves actual affinity observations. Production timing is diagnostic and does not establish a causal efficiency gain. This is a submitted disproof pending organizer review.
