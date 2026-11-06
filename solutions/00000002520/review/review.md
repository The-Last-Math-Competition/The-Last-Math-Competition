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

**Conjecture as filed.** The filed statement says the tensor version of the Fourier transform is governed by separated bases: the multidimensional transform factorizes over product bases and closes under separation. The source fixes neither a domain nor a function space. I read it in the standard finite-dimensional complex tensor/DFT setting: a shape is a finite list of positive axis lengths, arrays are functions on the product of cyclic groups, and the transform is the actual multidimensional DFT built from Mathlib's ZMod.dft.

**Decisive results.** Lean builds the genuine multidimensional DFT as a complex linear equivalence on every finite shape, proves the forward and inverse character-sum formulas, proves pure-factor separation in both directions, identifies the Fourier basis with the product of one-dimensional Fourier basis vectors, and proves the tensor-product operator factorization for every tensor (not only pure tensors) together with the tensor-product basis compatibility. The statement is universal over all finite shapes, including unit axes and the empty shape. This establishes the finite discrete tensor-Fourier factorization and closure claims; continuous Fourier integrals are outside the stated interpretation.

**Report correspondence.** The report's Theorem 1 and its forward/inverse formulas, separated-input identities, product basis, and tensor factorization match the Lean `Conjecture` and `tensor_factorization`. The report explicitly states the finite discrete scope and makes no continuous claim.

## Disposition

APPROVED — merged as PR 1104. The submission gives a complete, formalised proof of conjecture 00000002520.
