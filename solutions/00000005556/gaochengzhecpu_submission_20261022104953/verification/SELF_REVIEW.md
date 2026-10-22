# Self-review: conjecture 00000005556

Verdict: PASS (development self-review; coordinating adversarial review pending).

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. Both source languages were read. The unambiguous first clause requires the Newton polygon to determine the characteristic polynomial; equal polygon and different polynomial is enough to refute it. The last clause's subject might instead be the polygon itself, which is already horizontal for unit-root objects. The paper clearly exempts that weaker reading and does not claim all weight-zero Newton polygons differ.
2. The objects are genuine rank-one F-crystals over the point Spec F_3, using W(F_3)=Z_3 and identity base Witt Frobenius. These standard identifications are openly paper background. The specialized Lean structure contains the entire linear-algebra data: integral Z_3 linear equivalence, rational Q_3 linear equivalence, and scalar extension compatibility.
3. This does not replace an F-crystal by a pair of rational numbers. Both Frobenius maps are actual automorphisms with inverse and module axioms. Matrix representation is connected by a theorem on every vector, and the characteristic polynomial is actual Matrix.charpoly.
4. Unit-root status is both integral and numerical: integral Frobenius is an automorphism of the Z_3 lattice, and actual Q_3 norm and Padic.valuation of its rational eigenvalue are checked to be one and zero. The valuation is not defined as a table or an arbitrary rational label.
5. The Newton polygon is a real standard segment between actual coefficient-valuation points of the characteristic polynomial. For a monic linear polynomial with nonzero constant coefficient there are exactly those two relevant points, so its lower Newton polygon is exactly that segment. Both examples have nonzero unit coefficients and rank one; no higher-dimensional polygon convention affects the comparison.
6. PureWeightZero is deliberately specialized to rational algebraic eigenvalues. It requires existence of a rational eigenvalue matching the actual Q_3 coefficient and modulus one under every complex embedding of Q. For +1 and -1 this is exactly Weil purity of weight zero. No claim that all pure eigenvalues must be rational is made.
7. Distinctness uses the characteristic-zero Q_3 field: the constant coefficients are -1 and +1, whose equality would imply 2=0. No reduction mod 2 or base change is involved. Frobenius non-conjugacy is independently verified for every Q_3 linear equivalence, avoiding a weak test of only selected candidate maps.
8. The universal propositions quantify over actual RankOneCrystal objects and require true unit-root conditions. The main one requires equal actual Newton polygons and concludes equal actual characteristic polynomials. Both values come from the same objects, not unrelated invariants.
9. The standard Witt identification is not proved inside Lean and no crystalline-site formalization is claimed. The paper explicitly explains this bridge and the parent approved the faithful specialized data rather than requiring the general WittVector.Isocrystal class.
10. Actual warning-as-error Lean checks pass with only propext, Classical.choice, Quot.sound. No new axioms, placeholders, native_decide, or numeric surrogate tests occur. The concrete identity x^3=x in ZMod 3 uses kernel decide, which is legitimate for that finite-field background identity.
11. The parent checked current source and complete PR history before locking this ID. The draft directory did not previously exist. Official cached dependencies were acquired by the parent; no private cache download, installation or shared source modification was performed by this agent.


Reviewed artifact hashes:

- Main.lean: `0501e96670bb92f38ae2ed1cfcc523fcc3f9542d79badc43303b4b76344f07ca`
- main.tex: `f31ac1cf53c0ab4820c41f552bde4ef6b575fe4c67a1b10cd9851e7219e0e10d`
- main.pdf: `13520551a7dc9c2ea63ea1b15f1ea8d32c615d5faa6cfd8866b1a56b5d7eafa8`
- SOURCE.md: `804447248b1636fecdcd361db2150fe1cc37122c52424152e1523ca09c004194`
