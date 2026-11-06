# Parent adversarial review: conjecture 00000004003

Verdict: PASS

Scope of this verdict: the original, unaugmented process-law reading explicitly stated in the submission title, abstract, first paragraph, README and PR description. It is not a verdict against uniqueness of laws on signatures, tree-like equivalence classes, or time-augmented paths.

I reviewed the frozen bilingual source, every definition and proof in the final Lean file, the full paper, and all three final rendered PDF pages. Another delegated agent also supplied a read-only conceptual review and identified the interpretation and moment-object issues; the final paper addresses them openly. All of this is AI-assisted author and coordinating review, not external independent review.

The source says the expected signature determines the process distribution and does not define a reduced-path quotient, augmentation, or an injective class of signatures. In that literal reading, two distinct smooth closed paths based at zero already refute sufficiency. I checked the cited primary abstracts directly: Hambly-Lyons identifies equal signatures with tree-like equivalence, while Chevyrev-Lyons studies probability measures on signatures. These reinforce the essential distinction rather than turn the example into a contradiction of those theorems. If the source were amended to refer to signature laws or a suitable quotient, this submission would not resolve that amended conjecture; the paper makes exactly this limitation explicit.

The paths are the actual continuous functions x_a(t)=4*a*t*(1-t), with amplitudes 1 and 2. The scalar signature is defined recursively by actual interval integrals of the previous level times the actual derivative. The code derives that derivative and uses induction and the fundamental theorem of calculus to establish signature_n=x_a(t)^n/n! for every degree and endpoint. This is the full one-dimensional tensor signature, not a truncated summary. At endpoint one the degree-zero value is one and every positive degree is zero, so integrating against the two actual Dirac probability measures gives identical expectations at every level.

The distinction between laws is made after measurable restriction to C([0,1],R), using midpoint evaluation, where the two values are 1 and 2. Merely differing outside the observation interval would have been insufficient, and the final theorem avoids that error. The smoothness, shared initial point, probability hypotheses, and integrability of every signature coordinate are all established for the witnesses.

The moment condition is explicitly defined as the radial supremum-norm Carleman condition. The source leaves the moment object unspecified, so the submission does not claim there is one canonical path-space definition. Crucially, the code proves the exact supremum norm of x_a equals a for nonnegative a and also proves midpoint recovery and injectivity of the amplitude family. Thus these are genuine moments of the ordinary compactly supported amplitude moment problem. For each Dirac law all even moments are positive and all moments are integrable. The inverse-even-root sequence is proved equal to the nonzero constant reciprocal radius and hence nonsummable. Coordinate and total-variation readings are separately explained on paper, rather than assumed to be formalized.

The universal proposition negated by the final theorem retains all these admissibility assumptions and concludes equality of observed process laws. Refuting its sufficient implication refutes the stated iff under the disclosed reading; the submission does not claim a separate truncation theorem or solve an alternative signature-law interpretation.

The fresh copied-project lake build and separate warnings-as-errors Lean check returned zero with clean pinned dependency sources. The four printed audits contain only propext, Classical.choice and Quot.sound. The native document compiler succeeded on the exact final source. Tectonic generated three pages with no warnings. I inspected the definitions, moment series, all-level induction, stated interpretation boundary, references, and reproduction command across all three pages; everything is readable and unclipped.


Reviewed artifact hashes:

- Main.lean: `18c529df1739c6f562b159dc921b90bbde2d677f782ce0e1c40128c6c6d360fb`
- main.tex: `15543caaa8dd2c39ef596dbf68201a4ec8569b2890a8805848e3162e788871dd`
- main.pdf: `e7dda3fa9759db777813d4c9e0f8ed2ff3968620c148460b7c1e2e52a866514f`
- SOURCE.md: `4d027a4c26830074fa83b5ccc1eede505774456d8ef0ceebfd138c42165f5eb4`
