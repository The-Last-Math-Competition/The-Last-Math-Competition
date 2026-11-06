# Self-review: conjecture 00000002520

Verdict: PASS for the explicitly stated finite dimensional discrete tensor Fourier interpretation; separate parent semantic review, fresh build, and PDF verification remain the coordinator's responsibility.

1. **Bilingual scope.** The coherent English source asserts tensor Fourier factorization over separated bases without specifying domain/function space. The Chinese text repeats the same terms in damaged prose. The paper explicitly selects finite complex tensor DFTs and makes no claim about continuous Fourier transforms or infinite tensor products. This is a declared interpretation, not a silently substituted assertion.
2. **All finite shapes.** Shapes are arbitrary lists, with an entry n denoting axis length n+1. `encode_positive_dimensions` proves every finite list of positive lengths is representable. There is no bound on dimension or axis size. Unit axes and the zero-axis scalar space are included.
3. **Real Fourier operator.** `dftAll` is constructed as a linear equivalence from actual Mathlib `ZMod.dft` maps plus currying and pointwise linear equivalences. Its character sum is then proved for arbitrary arrays. Thus an abstract transform was not defined only by the desired separation property.
4. **Sign and normalization.** The forward kernel uses `stdAddChar (-(j*k))`; the inverse uses the positive character and product factors (n+1)^(-1). The Fourier basis is the inverse image of delta vectors, so basis vectors have exactly that inverse normalization. Basis coefficients are forward Fourier values. The paper uses this same convention throughout.
5. **Pure factors.** Forward and inverse separation hold for arbitrary axis factors. Zero factors are allowed. For the empty shape, the empty pure product equals one, whereas the transform itself remains the identity on all complex scalars; the general forward/inverse sum formulas cover those arbitrary scalars.
6. **Actual tensor objects.** `tensorCoordinates` is a genuine linear equivalence from `(Grid rest → C) tensor (ZMod axis → C)` to the full array space, using Mathlib `TensorProduct.piScalarRight`. `tensor_factorization` proves the operator identity for every tensor by tensor induction, not just a hardcoded rank-one example. The inverse tensor-operator identity is proved separately.
7. **Actual bases.** `fourierBasis` is Mathlib `Basis.ofEquivFun` of the actual DFT equivalence. Its product character values are proved. `tensor_product_basis` uses actual Mathlib `Basis.tensorProduct` and proves its image under the coordinate equivalence is precisely the full Fourier basis. This supplies independence and spanning, not merely a product of formulas called a basis.
8. **Complete universal proposition.** `Conjecture` quantifies over every shape and includes forward/inverse formulas, both separability directions, separated basis values, actual tensor-operator factorization, and actual tensor-product basis compatibility. `conjecture` proves it. The optional inverse tensor-operator identity and basis-coordinate formula are independently checked supporting results.
9. **Trust boundary.** All finite discrete mathematics claimed in the theorem is formally checked. The warnings-as-errors log includes nine principal axiom audits, each restricted to `propext`, `Classical.choice`, and `Quot.sound`. No unproved placeholders, native decision oracles, extra axioms, or computation surrogates are present.
10. **Review provenance.** Developed by a delegated AI agent with this self-review; the coordinating agent reviews it separately. No external independent review or completed parent artifact review is claimed here.


Reviewed artifact hashes:

- Main.lean: `00799466912cc444161243bbbcbe0a4d8f029809edaca29994b174ee99993414`
- main.tex: `f01501c65cf5cd3020f59b5e1e4788d7f5c2f5eb1b410c6b4160813e1cb3cc47`
- main.pdf: `d68a1c7b135b599ff5b4e6410b60ecc3a9ae883c65925cdb7fd86932c448d6aa`
- SOURCE.md: `1a0863f999a313f0f9ba07783a20fca11d80a0276a8bbcf7318be10778852cca`
