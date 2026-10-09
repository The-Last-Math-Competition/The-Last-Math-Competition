# Fixed-alphabet A1 counterexample

Portable source package for conjecture 00000003825. Lean 4.33.0 and the exact Mathlib Git revision are pinned by `lean-toolchain` and `lakefile.toml`.

Fresh reproduction in this package directory:

```text
lake update
lake exe cache get
lake build Main
```

The author did not run a full shared dependency build. Local evidence uses existing pinned package build/lib directories, writes only private `.olean` module outputs, and runs the explicit options `autoImplicit=false,maxSynthPendingDepth=3`.

`Main.lean` imports the complete construction and prints the final theorem axioms. The final theorem is `FixedAlphabetA1.fixed_alphabet_finiteness_false`. The full source correspondence and proof PDF are outside this source-package directory.

Modules, in dependency order: Tensor, Words, A1Family, Family, Classes, Main. `A1Family` contains the basic finite-chain model; it is not used as a substitute for the ambient word/tensor proof. `Words` builds the whole fixed alphabet monoid crystal; `Family` proves the actual embedding and both-arrow compatibility; `Classes` defines the real isomorphism quotient and proves its infinite family image.
