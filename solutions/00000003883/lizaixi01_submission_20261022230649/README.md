# Conjecture 00000003883: F-pure threshold counterexample

In the regular polynomial ring F2[x,y], at its origin, the actual ideal (x,y) has F-pure threshold 2. The conjecture predicts 1 for a=b=1, although gcd(1,1)=1 and 2 does not divide 1. The Lean proof constructs the ideals and Frobenius homomorphism, computes every noncontainment exponent, proves the maximum and the real limit, and refutes the predicted value.

We use the standard Frobenius-limit definition for ideals at the origin, as stated in the introduction of Badilla-Cespedes and Leon-Cardenal, *F-Pure Thresholds and F-Volumes of Some Non-Principal Ideals*, https://doi.org/10.1007/s00009-025-02860-z (also https://arxiv.org/html/2305.00571v3). The conjecture's brief test-ideal wording is interpreted as this standard invariant. The general equivalence of definitions is not itself formalized here; the actual Frobenius-limit definition and its complete computation for this example are formalized. No test-ideal computation is assumed as an axiom.

Earlier PR283 was closed because its Lean file only proved disconnected arithmetic, with no actual polynomial ideals or F-pure threshold. Its proposed universal bound fpt(I)<=1 is false for non-principal ideals; (x,y) itself disproves that bound. We do not use that bound or a log-canonical-threshold comparison.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

The manifest pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and every transitive dependency. `verify.sh` compiles Main, prints all eleven key declarations' transitive axiom dependencies, and runs the official Lean kernel checker with `--fresh`. The optional cache contains public dependency artifacts. The final Main is newly built and checked in a separate project; no auxiliary numeric computation is required.

Compile `report.tex` twice with pdflatex to regenerate the PDF. The supplied two-page PDF was rendered and both pages visually checked. Source-bound verification logs and SHA256 checksums accompany the package.

## Provenance

SOURCE.md preserves the original bilingual statement at the exact upstream commit. This is a classical elementary example, not a claim to new mathematics. OpenAI Codex assisted mathematical reasoning, formalization and writing. A separate supervising Codex agent reviewed the original, standard-definition reference, and full Lean proof. This is AI review, not human certification. Organizer acceptance is pending.
