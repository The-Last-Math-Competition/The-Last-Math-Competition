# Conjecture 00000005556 — Disproof

Over F_3, the actual free Z_3 lines with Frobenius +identity and -identity are unit-root crystals. Their rationalizations have characteristic polynomials X-1 and X+1, but the same horizontal Newton polygon and pure weight zero.

Lean constructs actual integral and rational linear automorphisms with scalar extension compatibility; proves their actual matrix representation, p-adic unit norms and valuations, geometric Newton segments, pure-weight-zero complex embedding conditions, distinct Matrix.charpoly values and actual Frobenius non-conjugacy. It negates a universally quantified Newton-polygon determination proposition. The pure-weight determination negation is additional, conditional on reading the last source clause as about characteristic polynomials.

The paper explicitly explains W(F_3)=Z_3, identity base Witt Frobenius, and the usual equivalence between crystals on the point and this specialized linear-algebra description. These standard bridges are paper background, not a claimed formal construction of a crystalline site or general WittVector.Isocrystal instance. The weaker reading that pure weight determines only the unit-root Newton polygon is not refuted.

From lean/ run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. The pinned versions are recorded in the project metadata. Principal axiom reports contain only propext, Classical.choice, Quot.sound.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed. Fresh build, PDF checking and publication are performed by the coordinating agent.
