# Problem 00000000025: incompatible exceptional-zero assertions

The printed per-character statement that an exceptional zero exists if and only if the associated character is real is incompatible with the printed exclusion of simultaneous window zeros for two non-overlapping irreducible characters of the same extension. The complete proof constructs the actual native CyclotomicField 8 Q, its Galois group and true isomorphism to (Z/8Z) units, native degree four and discriminant 256, and two distinct nonprincipal primitive conductor-eight real one-dimensional characters. Their native representations are irreducible, their trace characters are inequivalent and orthogonal, and every intertwiner is zero.

The zero condition is the actual existence of a real beta in the common interval (1-c/log D,1) with L(chi,beta)=0, for the same c>0 and actual D=abs(NumberField.discr K). The proof first excludes the printed conjunction for every genuine function family, then explicitly instantiates native DirichletCharacter.LFunction. No zeros, spectra, counts or analytic values are assigned. This disproves only the printed per-character sufficiency combined with pairwise exclusion. It does not decide whether any Siegel zero exists or refute the correct assertion that a possible exceptional character must be real, classical conditional repulsion, or GRH. A different global existential reading is outside the stated scope.

The full/depleted Artin distinction is handled explicitly. Lean constructs the actual prime (zeta8-1) over (2), native ramification index four and actual inertia subgroup equal to the full Galois group. Both genuine inertia-fixed spaces are zero, giving full local determinant factors one; the native Dirichlet local factors at 2 are also one. The standard cyclotomic Frobenius/Artin-Dirichlet Euler-product and analytic-continuation identification is an explicitly disclosed literature boundary, not an extra Lean premise. The universal-family formal contradiction is independent of that identification. Milne's displayed L_S is correctly described as depleted.

The whole proof is in `lean/Main.lean`, namespace `TLMC25`, ending in `complete_counterexample`. `SOURCE.md` preserves the complete original bilingual statement. `report.tex` and `report.pdf` give the argument and precise analytic recognition boundary; `SHA256SUMS.json` binds all other package files.

Run from `lean` using pinned Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

`verify.sh` runs the last three commands. The exhaustive Check uses ordinary `#print axioms` on every owned namespace declaration, including generated names, and verifies exact environment-enumeration coverage. Only propext, Classical.choice and Quot.sound are allowed. Original source-bound execution logs, actual complete job/result/thread-mask samples and qualification receipts accompany the package. Production timing is not controlled causal efficiency evidence. Organizer review remains pending.
