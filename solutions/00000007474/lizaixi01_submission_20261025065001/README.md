# Problem00000007474: affine parameter spectrum of a genuine quadratic family

This submission refutes only the printed real-algebraic-curve clause under the standard affine parameter-spectrum convention, with arbitrary finite real parameter tuples as permitted by the source. It does not compute genus or rank and does not refute a projectivized or otherwise restricted statement.

The actual bounded selfadjoint operators on R are T(s,t,u)=(s+t+u)^2 id. The actual noninvertibility/zero-spectrum set is the proper nonempty plane s+t+u=0. Restriction of all real polynomials to every point defines its actual vanishing ideal. Native evaluation and infinite-field polynomial extensionality identify that ideal with the kernel of the surjective substitution to R[Y0,Y1]. The native quotient algebra is therefore genuinely isomorphic to R[Y0,Y1], whose actual Krull dimension is2, not1. No expected dimension or genus is assigned as a definition.

The source is pinned at b355e42906e6eaf52bc7e9d005e0ef02d8aa7400, Git blob b8a693ede3d5168a584df7af0b442a14f77c23c6, exact source SHA256 ae13713358b23a4d5e30022bacb9be4ef365b090975d1043557111b46c2ea50a. SOURCE.md preserves the complete original bilingual statement. Grigorchuk–Yang/Yang define the noninvertibility convention and distinguish affine and projective parameter spectra; the report explicitly states that their background is linear complex pencils while this example is a quadratic real family. Stacks33.43.1 supplies the standard dimension-one terminology for curves. The actual algebraic/operator/dimension chain is proved in Lean; these definition boundaries are not extra axioms.

Reproduce from lean/ using Lean4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:

1. `lean --version`
2. `lake build +Main`
3. `lake env lean -DwarningAsError=true Check.lean`
4. `lake env leanchecker --fresh Main`

After the separate version check, `bash verify.sh` runs the remaining three commands. Check.lean enumerates every owned declaration, including generated/private names, and applies ordinary `#print axioms` to each. Only propext, Classical.choice and Quot.sound are allowed. The full project, exact commands, logs, original execution evidence, complete SOURCE.md and SHA256SUMS.json accompany the proof. This assigned v3 trial case retains all attempts and costs; its isolated timing establishes no efficiency result.
