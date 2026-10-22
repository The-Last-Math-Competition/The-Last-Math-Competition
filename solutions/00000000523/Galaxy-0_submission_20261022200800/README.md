# TLMC 00000000523: Frobenius need not have a minimal polynomial

Result: disproof, over the prime field F₂. Take the numerical semigroup N = <1>, whose multiplicity is one. For R = F₂[t] and m = (t), the principal Čech complex gives H¹_m(R) = F₂[t,t⁻¹]/F₂[t]. The Frobenius orbit of [t⁻¹] is [t⁻¹], [t⁻²], [t⁻⁴], ... . These are linearly independent. No nonzero coefficient polynomial annihilates Frobenius; in particular it has no minimal polynomial of degree one.

The regular semigroup is allowed by the original statement. No singularity or multiplicity-greater-than-one restriction is present. Coefficients are F₂, so Frobenius is linear, not merely semilinear. The same mathematical counterexample applies to the completed convention F₂[[t]] via F₂((t))/F₂[[t]], but the Lean file uses finite Laurent polynomials, not formal power series.

## Original problem and eligibility
- https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000000523.md
- Original source blob: 1350fd5092d75704112961ab5683d7b6601e5b55.
- Checked 2026-10-22 UTC. Metadata had proven=false, disproven=false. Both padded and unpadded PR searches had no matching solution; the unpadded query returned unrelated PR number 523 for problem 8776. The upstream solutions/00000000523 directory was absent (404).
- Submission-time eligibility must be rechecked independently of this initial record.

## Formalization scope
Main.lean constructs finitely supported integer-indexed Boolean coefficients (Laurent polynomials), the nonnegative polynomial subspace, and an actual Quotient by agreement of negative coefficients. It proves that this relation is exactly difference belonging to the polynomial subspace. Denominator clearing is proved explicitly. It verifies the Boolean field identities, descends the exponent-doubling map to the quotient, proves F₂-linearity, and checks failure of every degree-one monic annihilator. A stronger theorem proves failure of every nonzero finite coefficient polynomial, using coefficient extraction from its genuine Horner operator evaluation.

Square.lean defines ordinary finite double-list convolution and proves cancellation of cross terms in characteristic two. Bridge.lean identifies this square with Main.frobenius, including a surjective sparse representation theorem for every bounded Laurent polynomial. These are algebraic identities, not bounded experiments.

The general comparison between derived-functor local cohomology and the Čech complex is a cited mathematical theorem, not rebuilt as a Lean theorem here. The quotient implementation is the concrete degree-one Čech model for the principal ideal. See the paper's coverage section. No claim is made to formalize the full general local-cohomology machinery or formal power series.

## Sources
Read on 2026-10-22 UTC:
- Stacks Project, Lemma 47.9.1, https://stacks.math.columbia.edu/tag/0952 : extended Čech complex for local cohomology.
- Stacks Project, Lemma 51.2.1, https://stacks.math.columbia.edu/tag/0A6T : comparison with supported cohomology.

## Reproduction
Existing Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783. No external Lean dependencies.
Run ./VERIFY.sh /absolute/path/to/lean-4.31.0/bin . This performs a clean lake build, an axiom audit, and independent leanchecker kernel replay. Run ./build_pdf.sh with pdflatex available to reproduce paper.pdf. Verification logs record actual results rather than assumed success.
