# Disproof of conjecture 00000001015

## Standard projective-plane interpretation
An arc in PG(2, q) is a set of points with no three collinear. In a projective plane of order q, exactly q+1 lines pass through each point. Fix one point P in an arc of k points. Each of the other k−1 points lies on a line through P, and these lines must be distinct: two other points on the same line would make three arc points collinear. Therefore k−1 ≤ q+1, or k ≤ q+2.

For q=8, this gives k ≤ 10. There are no arcs of length 11 in PG(2,8), so the number of their isomorphism classes is zero, not one. The conjecture does not name an ambient projective space; this disproof uses the standard projective-plane meaning of “MDS arc,” consistent with the surrounding arc conjectures in the repository.

## Formalization scope
Lean checks the decisive cardinality contradiction: an 11-arc would require ten distinct lines through a fixed point, while an order-8 plane has only nine. The projective-plane incidence facts and the no-three-collinear injection are proved in the text and are not formalized in Lean.

## Contents
- main.tex, main.pdf: written disproof and interpretation notes.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
