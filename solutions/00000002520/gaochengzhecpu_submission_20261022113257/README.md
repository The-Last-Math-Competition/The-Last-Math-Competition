# Proof of Conjecture 00000002520

For every finite number of axes of arbitrary positive lengths, the complex multidimensional discrete Fourier transform factors as the tensor product of the one-dimensional DFTs. The proof includes the forward and inverse formulas for arbitrary arrays, separation in both directions, a real Mathlib Fourier basis with product-vector formulas, and compatibility with actual tensor products and tensor-product bases.

## Source interpretation

The English source does not fix a domain or a function space. This submission makes explicit the standard finite dimensional tensor/DFT interpretation. The Chinese source repeats terms without providing an additional coherent mathematical condition. Both languages were inspected. Continuous Fourier integrals, infinite tensor products, and analytic convergence are outside the claim. This scope is stated in the paper; a two-dimensional example is not substituted for the arbitrary finite-axis theorem.

## Formalization

`Grid ns` is the product of cyclic groups with lengths `n+1`, one for each list entry. Every finite positive shape is covered, including unit axes; the empty shape is the scalar space. `dftAll ns` is built from the genuine Mathlib `ZMod.dft` complex linear equivalence. Its full forward and inverse character formulas are derived, not postulated.

`TensorFourier.conjecture` proves a universal proposition over all shapes containing the forward/inverse sums, forward/inverse pure-factor separation, product Fourier basis, actual tensor-product operator factorization, and actual `Basis.tensorProduct` compatibility. `tensorCoordinates` uses the canonical `TensorProduct.piScalarRight` linear equivalence. The operator factorization is proved for all genuine tensors, including sums of pure tensors. The optional separate inverse tensor-product operator identity is also formally checked.

The complete finite discrete theorem is formalized. No continuous result is asserted. `verification/STRICT_CHECK.log` records the real warnings-as-errors check and principal axiom audits; only `propext`, `Classical.choice`, and `Quot.sound` occur. The coordinating agent performs the separate fresh build and all-page PDF verification.

## Reproduction and review

Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned in `lean/`. Obtain those dependencies and their cache, then run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Compile `main.tex` with Tectonic.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.
