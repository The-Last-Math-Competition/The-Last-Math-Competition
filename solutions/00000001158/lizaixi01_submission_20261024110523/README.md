# Problem 00000001158: a rank-one lattice with unbounded scl

Under the standard ambient real-rank convention, the usual nonuniform congruence lattice Γ(2)/{±I} in PSL₂(ℝ) has real rank one and is a free group of rank two. For its genuine commutator c=[a,b], the complete Lean proof gives N/12 ≤ scl(cᴺ) ≤ N for every natural N, and actual finite values exceeding every real bound. Its native abelianization has a genuine noncyclic quotient ℤ², excluding all usual single-knot groups in S³, whose abelianization is cyclic. This refutes the printed rank-one boundedness implication, including its stated knot exception; no infinite scl outside the commutator subgroup is used.

The exact published congruence-lattice/free-group identification, finite Haar covolume, ambient Lie rank and classical knot-group abelianization theorem are explicitly external geometric/topological boundaries, documented in the report. They are not re-proved or inserted as axioms in Lean. Γ(2) in SL₂(ℤ) contains −I and is not itself the free group; the projective quotient is essential. The source adds no cocompactness restriction. No claim is made for a differently defined rank, arbitrary link complements, knots in other ambient manifolds, or a general lattice/knot classification.

The algebraic proof constructs the native FreeGroup, its true reduced words and actual adjacent List.zip/countP occurrences. It proves the signed Brooks inverse rule, full cancellation decomposition and defect3, exact count H(cⁿ)=n, all-product minimal commutator lengths by existence plus Nat.find, actual native Fekete stable limits and their unbounded finite bounds. Both cl and scl are transported through every group isomorphism. The full native Abelianization surjects onto actual ℤ², proved noncyclic. No desired norm, count or limit is assigned.

`lean/Main.lean` contains the whole algebraic proof in namespace `TLMC1158`, ending in `complete_counterexample`; `SOURCE.md` contains the complete original bilingual statement. `report.tex` and `report.pdf` explain the proof, precise interpretation and external recognition boundary. `SHA256SUMS.json` binds all other files.

Reproduce from the `lean` directory with the pinned Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

`verify.sh` runs the last three commands. The exhaustive Check calls ordinary `#print axioms` on every imported TLMC1158 environment declaration, including generated names, and checks exact enumeration coverage. The permitted foundational axioms are only propext, Classical.choice and Quot.sound. All original command logs, complete source-bound job/result/mask samples and eligibility receipts accompany the verified package. Resource timings are production observations, not controlled causal efficiency evidence. Organizer review remains pending.
