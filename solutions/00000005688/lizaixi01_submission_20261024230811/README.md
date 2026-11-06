# Problem 00000005688: the printed unit-length-two clause is false

The genuine category `Discrete (Fin 3) ⥤ FGModuleCat.{0} ℂ`, with componentwise tensor, is finite semisimple, complex-linear, abelian, rigid and bilinear, with finite-dimensional Hom spaces and enough projectives. Its actual non-simple tensor unit is the biproduct of three pairwise nonisomorphic simple coordinate objects. Every complete native composition series of the unit has length three.

This category is decomposable. No indecomposability premise is printed in the source; EGNO Definition 4.1.1 treats that property separately. Only the universal assertion that the unit has length two is refuted. No claim is made about the source's unspecified representation-dimension table, global-dimension formula or local-unit uniqueness clauses. The componentwise product here is not the matrix-category example in EGNO.

`SOURCE.md` retains the complete original bilingual text. Initial source: upstream `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, Git blob `ab38e5b5c36c538b0ce989cbf7ff0d9ea5fc4e8d`, LF SHA256 `c00514fcdfebc1cecdb9d5fd52b2122786b5acb10161b52d4d2ebdbcc0b15491`. Exact source bytes and qualification receipts are retained in `evidence/eligibility.json`.

The proof uses all triples of finite-dimensional complex spaces and all component linear maps. Basis vectors and coordinate functionals form actual finite biproduct bicones on every object. An order isomorphism identifies every categorical subobject with its three actual component subspaces. This proves native simplicity, classification of all simple isomorphism classes, finite length and a genuine unit subobject lattice isomorphic to `Fin 3 → Bool`. A transported saturated chain and native Jordan–Hölder prove length three for every complete unit composition series. Projectivity is proved by actual component linear lifting through all epimorphisms.

The 657-line `lean/Main.lean` has 112 explicit declarations: 64 theorems, 31 definitions, 4 abbreviations and 13 instances. `Check.lean` dynamically enumerates the entire owned namespace, including generated names, and invokes ordinary `#print axioms` on each. Complete namespace coverage and the three-foundation-axiom allowlist are checked against the real output.

Runtime: Lean 4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From `lean/`, run:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

Alternatively run `lean --version`, then `bash verify.sh` for the remaining three steps. The original full fresh-kernel replay, command logs, source bindings, exhaustive axiom output, actual thread-mask samples and resource receipts are retained in the evidence. Production timings are diagnostics and do not establish controlled efficiency gains.

The mathematical argument is in `report.tex` and `report.pdf`. The report cites EGNO's author final book, printed page 65, solely for standard definitions. All category, rigidity, finite semisimplicity, projectivity, subobject, simple-class and length bridges used in the result are Lean-proved. No extra axiom, unfinished proof or native decision shortcut occurs.
