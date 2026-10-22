# Disproof of Conjecture 00000000947

Already on the fixed real plane, the actual lower envelope of the modulus of convexity over all genuine norms is zero. The sup norm attains zero at every separation in [0,2]. Every genuine finite l_q^2 norm with 1<q<infinity has strictly positive actual modulus at every positive separation up to two, so a minimizing exponent selector cannot tend to two as separation tends to zero.

## Scope

Refutes the small-separation minimizing-exponent conjunct in dimension two, hence the full statement. The obstruction does not depend on excluding uniformly convex spaces: for every fixed 0<epsilon<2 and every eta>0, the proof supplies an actual uniformly convex l_q^2 norm, q>=2, with actual modulus strictly between zero and eta. Thus even the uniformly convex lower envelope is zero there, with no finite exponent q>1 attaining it. No assertion about large-separation asymptotics, endpoint slopes, or uniformly convex approximation at epsilon=2 is needed.

## Formalization

Lean defines genuine real norm axioms on Fin 2 -> R, actual sInf over all admissible unit pairs, and actual outer sInf over all such norms. Admissible sets are proved nonempty for every norm throughout the geometric domain. Mathlib PiLp provides the actual l_q norms; real-power strict convexity and an attained minimum on the compact full admissible-pair set prove strict positivity, without assuming a missing library uniform-convexity instance. The proof then constructs an actual Mathlib UniformConvexSpace certificate, directly rules out arbitrary minimizing selectors tending to two, and proves arbitrarily small positive actual moduli in the uniformly convex class by a carefully labeled trial-pair upper bound and a proved real-power limit. No numerical oracle or auxiliary verifier is required.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile the document with `tectonic main.tex`. No auxiliary program is needed.
The exact bilingual source, provenance, actual fresh-build logs, axiom audit,
artifact hashes and PDF review are included. An author agent supplied a
self-review; the parent separately reviewed the complete proof and final
artifacts. No external independent review or novelty of these elementary
convexity facts is claimed. The standard modulus conventions appear in
E. Llorens Fuster, Moduli and Constants (2006), section 1, cited in the paper.
