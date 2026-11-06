# Solution Review — Conjecture 00000005556 (PR 1089)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104953`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005556; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The Frobenius structure is the linearized operator of crystals. Conjecture: The characteristic polynomial is given explicitly by the Newton polygon, uniquely determined by the pure weight for unit-root crystals. (pure-weight uniqueness of Newton polygons) 定义：Frobenius 结构指晶体的线性化算子。猜想：特征多项式由牛顿多边形显式给出；单位根晶体时由纯权唯一决定。（牛顿多边形纯权唯一）

**Decisive results.** Over F_3, the actual free Z_3 lines with Frobenius +identity and -identity are unit-root crystals. Their rationalizations have characteristic polynomials X-1 and X+1, but the same horizontal Newton polygon and pure weight zero. Lean constructs actual integral and rational linear automorphisms with scalar extension compatibility; proves their actual matrix representation, p-adic unit norms and valuations, geometric Newton segments, pure-weight-zero complex embedding conditions, distinct Matrix.charpoly values and actual Frobenius non-conjugacy. It negates a universally quantified Newton-polygon determination proposition. The pure-weight determination negation is additional, conditional on reading the last source clause as about characteristic polynomials. The paper explicitly explains W(F_3)=Z_3, identity base Witt Frobenius, and the usual equivalence between crystals on the point and thi The decisive Lean declaration is `not_pure_weight_determines_characteristic_polynomial`, whose statement is: ¬ PureWeightDeterminesCharacteristicPolynomial := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1089. The submission gives a complete, formalised disproof of conjecture 00000005556.
