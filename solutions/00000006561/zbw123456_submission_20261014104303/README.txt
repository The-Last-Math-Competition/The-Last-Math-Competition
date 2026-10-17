Conjecture 00000006561: Symplectic composition and the pullback diagram

Read proof.tex / proof.pdf for the precise statement, interpretation and Lean
correspondence. The source question is included unchanged as conjecture.md.
Prepared for review. No official PR or Issue has been created.

Reproduction
Lean 4.19.0; Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.
All transitive dependency revisions are fixed by lake-manifest.json.
From lean/: lake build
Then: lake env lean -DwarningAsError=true SymplecticComposition.lean
With pdflatex on PATH, sh verify.sh builds the project and document.
A fresh checkout needs network access to download the pinned dependencies and
cache. The local audit shares an existing dependency checkout through ignored
.lake symlinks. No symlinks, cache files or absolute dependency paths are part
of the submission. The portable manifest uses Git URLs and commit revisions.
On this macOS host the cache executable failed in the dynamic loader; the
cache was downloaded using lake env lean --run Cache/Main.lean get instead.
The proof checker itself is the official Lean 4.19.0 executable.

Review
The final theorems print their axiom dependencies. Only Lean's standard
propext, Classical.choice and Quot.sound may occur. Mathematical limitations
or interpretation boundaries are stated explicitly in the report; compiling
a file is not itself official competition acceptance.
