# Source correspondence: 00000003825

Exact source copy: `sources/00000003825.md`. SHA256: `d42e78b95fd7fee5cac646669c1f43db9fbca852843f58f65b9c46dd52953bdb`.

The source defines an arrow structure on an alphabet monoid satisfying crystal axioms. English calls it a **monomial** crystal; Chinese calls it a **monoid** crystal. This package follows the explicit shared definition: the alphabet is always the same two letters `{1,2}`, represented by `Bool` (`false=1`, `true=2`); its free monoid is `List Bool` with concatenation and the empty word. It does not replace the object with Laurent Nakajima monomials. If an unstated Laurent-monomial interpretation is preferred, the present result must be evaluated under that changed definition separately.

## The precise false conjunct

The conjecture joins (i) a dominant-weight classification, (ii) the Weyl vertex-count formula and (iii) finiteness of irreducibles over a fixed alphabet. This package disproves (iii). It does not assume or prove the broad classification (i). Its A1 family agrees with (ii): highest weight `k` and `k+1` vertices, the rank-one Weyl dimension `(k+1)/1`. One false necessary conjunct refutes the stated conjunction.

## Complete actual crystal data

`Tensor.lean` defines `A1Crystal V` for the Cartan datum `[2]`: weight lattice `Z`, fundamental weight `1`, simple root `2`. Its fields include partial maps `e,f : V -> Option V`, nonnegative epsilon and phi, the pairing identity `phi=epsilon+weight`, e/f partial inverses, both normal endpoints, and every lowering change. Raising changes are derived from the inverse relation. `Classes.lean` proves the full string characterization for any such object:

```lean
iterate A.e n x ≠ none ↔ n ≤ A.eps x
iterate A.f n x ≠ none ↔ n ≤ A.phi x
```

Thus normal string length is proved, rather than stored as an assumed hypothesis. Rank one has no two-colour switching axioms to discharge. Every member is nonempty, including `k=0`.

## The whole fixed alphabet monoid and the tensor bridge

`Words.lean` constructs the actual two-letter crystal and the unit crystal. The type `Word n` is an n-letter product of this same alphabet. `wordCrystal n` is built recursively using the general tensor constructor, whose crystal axioms are all proved in `Tensor.lean`.

The chosen conventional reading writes `uv` as the tensor `v ⊗ u` (reverse factor reading). Its functions are

```
epsilon(u,v) = epsilon(v) + max(epsilon(u)-phi(v),0)
phi(u,v)     = phi(u) + max(phi(v)-epsilon(u),0)
weight(u,v)  = weight(u)+weight(v).
```

The raising operator acts on `u` exactly when `epsilon(u)>phi(v)`; lowering acts on `u` exactly when `epsilon(u)>=phi(v)`. Otherwise the respective operator acts on `v`. These are the usual strict/non-strict tensor rules with the factors reversed. In this convention a `2` to the left of a `1` cancels in the signature. Reversing the word gives the other common factor-reading convention.

The package proves `Sigma Word ≃ List Bool` via encode/decode inverses, constructs a sigma crystal on all lengths, and transports **all crystal data and both operators** through that equivalence. The result is `monoidCrystal : A1Crystal (List Bool)`. This is the whole monoid, including nonsorted words; it is not just labels attached to an abstract path. `monoid_cons_e` and `monoid_cons_f` prove its actual word-recursion/tensor arrows. Concatenation remains the ordinary free-monoid multiplication; no homomorphism assumption about e/f is imposed, since crystal operators are partial tensor operators rather than monoid homomorphisms.

`Main.lean` also declares `fixedMonoidCrystal : A1Crystal (FreeMonoid Bool)` using Mathlib's actual free-monoid type and its concatenation monoid instance. `FreeMonoid Bool` is definitionally `List Bool`; `fixed_monoid_multiply` verifies multiplication is concatenation. `all_k_in_one_free_monoid` gives both-arrow preservation for all k in this one explicitly structured monoid.

`Family.lean` proves the closed forms for every `a,b`:

```
row(a,b) = 1^a 2^b,
epsilon(row(a,b))=b, phi(row(a,b))=a, weight(row(a,b))=a-b,
f(row(a+1,b))=row(a,b+1), e(row(a,b+1))=row(a+1,b).
```

These formulae are consequences of the actual ambient tensor recursion, not defining assumptions about the ambient arrows.

## Family admissibility and irreducibility

For each unrestricted `k : Nat`, `family k` is a complete actual A1 crystal on `Fin(k+1)`. Its embedding is `i -> 1^(k-i)2^i`. Every image word has length `k`; the alphabet and monoid are independent of k. Distinct letters or alphabets are never introduced for different k.

`embedding_e`, `embedding_f` and `embedding_stats` prove preservation of both partial arrows, including their undefined endpoints, and preservation of all weights and string functions. The maps are injective, so their images are genuine closed subcrystals of the one ambient monoid crystal.

`from_highest` proves actual edge paths from vertex 0 to every vertex; `family_connected` proves connectedness without assuming it. `Main.lean` strengthens this to `family_irreducible`: any nonempty subset closed under both e and f equals the entire vertex set. This proves irreducibility in the crystal-component sense and prevents manufacturing irreducibility by storing an assumption.

`highest_iterate` shows that exactly i lowerings from the highest element give vertex i. `family_full_strings` states for every k, every vertex i and every number n of iterations that e survives exactly when n<=i and f survives exactly when n<=k-i. The package therefore handles an actual infinite k-indexed family and complete strings, not finite samples.

## Actual isomorphism classes and the conclusion

`Classes.lean` defines `CrystalIso` as a vertex equivalence preserving e, f, weight, epsilon and phi, with proven reflexivity, symmetry and transitivity. `IrreducibleWordCrystal` stores an actual finite nonempty connected crystal and an injective, two-arrow-and-data-preserving embedding into the fixed ambient monoid. Its isomorphism quotient is `IrreducibleWordCrystalClass`.

`familyClass : Nat -> IrreducibleWordCrystalClass` inserts the admissible family objects into this actual quotient. `familyClass_injective` takes equality of quotient classes, obtains an actual crystal isomorphism, and only then applies preservation of the vertex cardinality. The equation `k+1=l+1` forces k=l. Cardinality is the obstruction between admissible objects, not a substitute for constructing them.

Final theorem:

```lean
FixedAlphabetA1.fixed_alphabet_finiteness_false :
  ¬ Finite FixedAlphabetA1.IrreducibleWordCrystalClass
```

This implies that the fixed two-letter A1 alphabet has infinitely many irreducible finite word/monoid crystal isomorphism classes, contradicting the source's final conjunct. A1 is finite type, and all dominant k are admissible.

## Reproducibility and review boundaries

`Lean/lean-toolchain` pins Lean 4.33.0; `Lean/lakefile.toml` pins Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d` and records `autoImplicit=false,maxSynthPendingDepth=3`. The worker uses only existing pinned package caches and writes private module outputs. `compile.py` records each local invocation, including failures, with its source hash. The final printed theorem axioms should contain only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx` or assumed bridge.

These are worker evidence and a source correspondence claim. Independent original-first semantic review, manager mechanical checks, PDF checks and a fresh official replay remain separate acceptance steps. No worker self-acceptance or upstream submission occurs.
