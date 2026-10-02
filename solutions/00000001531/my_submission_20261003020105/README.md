# Disproof of conjecture `00000001531`

**Verdict: FALSE — for the torsion-free hyperbolic genus-2 surface
group Γ = ⟨a,b,c,d | [a,b][c,d]⟩, HH₂(ZΓ) ⊇ H₂(Γ;Z) = Z ≠ 0 by
Burghelea's decomposition: the minimal nonzero Hochschild degree is at
most 2, not infinite.**

## The conjecture (verbatim from `conjectures/00000001531.md`)

> Definition: HH_n(Z) is the Hochschild homology of the integers (known
> to vanish for n ≥ 2). Conjecture: For group rings ZΓ with Γ a
> torsion-free hyperbolic group, the minimal nonzero n of HH_n(ZΓ) is
> infinite — higher Hochschild homology always vanishes; with torsion,
> the minimal nonzero n is given by the smallest prime factor of the
> orders of torsion elements.

## The counterexample: the genus-2 surface group

Γ = ⟨a,b,c,d | r⟩ with r = a b a⁻¹ b⁻¹ c d c⁻¹ d⁻¹ (the relation
[a,b][c,d]) is torsion-free and hyperbolic (classical). Burghelea's
theorem (Invent. Math. 90: the Hochschild homology of group rings)
decomposes HHₙ(ZΓ) over conjugacy classes of Γ, with the identity
conjugacy class contributing the group homology Hₙ(Γ; Z). The genus-2
surface is orientable, so **H₂(Γ; Z) = Z ≠ 0**, hence
**HH₂(ZΓ) ≠ 0**: the minimal nonzero n is ≤ 2, and "higher Hochschild
homology always vanishes" is false for this torsion-free hyperbolic
group.

**Chain-level input, kernel-certified:** the Fox derivatives of the
relator r evaluated at the trivial representation (the augmentation)
are all exactly zero — each equals the exponent sum of its generator in
r (+1 −1 = 0 for each of a, b, c, d). This is the standard computation
underlying the homology of the surface group; the conjecture's premise
(Γ torsion-free hyperbolic) is satisfied, only its conclusion fails.

## Verification

* `reproduce.py` — computes all four Fox derivatives of r symbolically
  as elements of the group ring Z[Γ] (free module on Γ), evaluates them
  at the augmentation (every group element ↦ 1), confirms they all
  vanish, and confirms the abelianization H₁ = Z⁴ (exponent-sum matrix
  of rank 4).
* Lean 4 (core, v4.33.1) — `lean4/`: the word encoding of r, the
  structural exponent-sum (Fox-at-augmentation) computation for all
  four generators, and the refutation of the "vanishes identically"
  claim. All 7 audited theorems report `does not depend on any axioms`.
  The presentation, hyperbolicity/torsion-freeness, H₂ = Z, and
  Burghelea's theorem are classical and cited.

## Boundary

Only the torsion-free case ("minimal nonzero n is infinite") is
refuted; the torsion case (smallest-prime-factor clause) is not
addressed.
