# Conjecture 00000000821: gradient lower bound

Under the standard positive Laplacian convention (-Delta f = lambda f), the proposed uniform lower bound fails even on a fixed flat circle. For each positive integer m, sin(m theta) is nonzero, smooth and has eigenvalue m^2. The actual absolute maxima of the function and gradient are 1 and m, so the ratio is 1/m. The Lean proof refutes every positive constant, with arbitrarily high modes.

The source does not name the operator or fix the spectral convention. This submission explicitly uses lambda as the positive Laplacian eigenvalue. It does not refute a reinterpreted formula using lambda as the frequency (the square root of the eigenvalue). The formal model is the genuine quotient AddCircle(2*pi), with the flat-circle arc-length derivative and Laplacian expressed through its real coordinate pullbacks. It does not claim to use a general Riemannian gradient API.

## Reproduce

Install elan, enter lean/, and run:

```sh
lake exe cache get
bash verify.sh
```

The manifest pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all transitive dependency commits. The optional cache is the public Mathlib build cache. verify.sh builds Main, prints transitive axiom dependencies for all eleven key declarations, and runs the official Lean kernel checker with --fresh. The official checker is not a separately implemented kernel. No auxiliary numerical computation is required.

Compile the report twice with pdflatex -interaction=nonstopmode -halt-on-error report.tex. Both pages of the supplied PDF were rendered and checked. Exact source-bound verification records and SHA256 checksums are included.

## Scope and attribution

SOURCE.md preserves the bilingual conjecture at upstream b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. The positive-eigenvalue convention is documented in Stefan Steinerberger, On the Spectral Resolution of Products of Laplacian Eigenfunctions (2017), https://arxiv.org/abs/1711.09826. The sine/cosine spectrum of the circle appears in Gantumur Tsogtgerel, Math 319 Lecture 25, McGill University (2011), https://www.math.mcgill.ca/gantumur/math319w11/downloads/slides25.pdf (opposite Laplacian sign). This is an elementary counterexample, not a claim to new mathematics.

OpenAI Codex assisted reasoning, Lean code and reports. A separate supervising Codex agent reviewed the original and full source, including an explicit nonzero-function requirement. This is AI review, not human certification. Organizer review and scoring remain pending.
