# Problem 00000000614: unrestricted negative-q cable formula

For the standard zero-framed unknot cable convention, p=2 and q=-1 give an actual negative one-crossing closed two-braid. Both its rational unreduced Lee/Rasmussen invariant and the crossingless companion's invariant are computed as 0, while the printed formula gives -2. This addresses only the source's unrestricted-q formula. It makes no claim against positive-q repairs or another framing convention.

The exact bilingual source is included in SOURCE.md. Source LF SHA256: `97835a76f87f29b8e86fa67813de820b4383fea821914fcda3a084353b70d83b`; pinned source commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, blob `b0386088406555d282d476b45b81c702f21e924a`.

The Lean proof constructs the actual Circle curve z -> (z²,z^-1) on a product solid torus boundary, the entire continuous two-sheet braid, its unique projected crossing and negative native derivative determinant, analytic port/rotation/incidence identifications, and native smoothing component quotients 1 -> 2. The actual crossingless circle and native one-component quotient are also present.

The standard identification of the product solid torus with the zero-framed unknot neighbourhood, and the published convention C_(2,2t+1)(U)=T_(2,2t+1) for every integer t (Lewark–Zibrowius Definition3.13, printed259–260), form the explicitly disclosed geometric identification boundary. No additional Lean axiom, fabricated cable typeclass, or claimed formalization of general satellite topology, Reidemeister invariance or spectral sequences is used. The actual finite diagram and all its subsequent algebra are formalized; see report.tex/report.pdf for the precise boundary.

Native QuadraticAlgebra Q (omega²=1), actual basis/tensor maps, both full integer-indexed ModuleCat cochain complexes and native homology are used. The negative complex is Delta:A -> A tensor A in degrees -1 and0; all other native homology vanishes. Both normalization shifts are retained: its output q=p-1. Homology filtrations are actual images of filtered cycles at every integer threshold. A true quotient/coordinate isomorphism and genuine section yield the filtration profile, with nonempty bounded nonzero-class threshold sets and actual attained degrees {-1,1}. The extrema definitions, not assigned values, give smax-1=smin+1=0 for both diagrams.

`lean/Main.lean`: complete 969-line proof, 175 explicitly named declarations (85 theorem,74 def,15 abbrev,1 named instance), plus3 anonymous instance commands. `lean/Check.lean` dynamically enumerates all owned declarations, including private/generated/anonymous-instance names, and prints ordinary axioms for every one. Only propext/Classical.choice/Quot.sound are allowed. No sorry, native_decide or additional axiom.

Pins: Lean4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. In the lean project run:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

`verify.sh` runs the final three commands; version is checked separately. The evidence contains the complete original four-step logs, command/axiom/source receipts and thread-affinity observations, plus exact original job/result/all-thread-mask data. `SHA256SUMS.json` binds all other package files. These production timings are diagnostics, not controlled causal efficiency measurements. A submitted PR remains pending organizer review.

Primary definitions: Rasmussen, arXiv:math/0402131v1, printed3–4/6; Lewark–Zibrowius, J. reine angew. Math.816(2024),241–296, DOI10.1515/crelle-2024-0061, printed259–260. The latter's later characteristic-2 theory is not substituted for rational Lee homology.
