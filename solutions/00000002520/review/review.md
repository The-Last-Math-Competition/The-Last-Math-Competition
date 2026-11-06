# Solution Review — Conjecture 00000002520 (PR 1104)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022113257`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002520; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Fourier transform of tensors: higher dimensions. Conjecture: The tensor version of the Fourier transform is governed by separated bases: the multidimensional transform factorizes over product bases, and the version closes under separation. (tensor Fourier transform separated bases) 定义：张量的傅里叶变换：高维。猜想：张量的 Fourier：变换的张量版本且本的组合为分离基。（张量 Fourier 变换高维变换变换张量版本分离基组合张量 Fourier 分离基变换张量版本基分离变换张量版本分离基张量版本分离）

**Decisive results.** Lean proves that the multidimensional discrete Fourier transform over a product of cyclic groups factors as the tensor product of one-dimensional DFTs, including forward/inverse formulas, separation in both directions, the product Fourier basis, and tensor-product operator/basis compatibility. The theorem `conjecture : Conjecture` is the universal finite-dimensional statement. This establishes the filed conjecture under the stated finite tensor/DFT reading.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1104. The submission gives a complete, formalised proof of conjecture 00000002520.
