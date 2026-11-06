# Disproof of 00000004279: an infinite rank-three Butler family

For every prime p, the actual additive group G_p = (Z[1/p])^3 is a rank-three torsion-free Butler group. It is p-divisible and is not q-divisible for any other prime q. This invariant of actual additive-group isomorphisms gives infinitely many isomorphism classes, contradicting the source's unconditional finite-quotient necessary clause. It does not contradict infinite-parameter classifications or a modified problem with fixed rank-one types.

Lean uses the actual Away localization, proves its rank over Z is one, constructs an injective localization homomorphism into Q, and bounds the genuine rank of G_p above and below using Z^3 and Q^3. Its equivalence to the actual finite DirectSum and the pure full-submodule witness are supplied, including torsion freeness of both the summands and the group. No freeness over Z is assumed. Genuine residue homomorphisms into ZMod q prove failure of q-divisibility. The isomorphism quotient relation is Nonempty (G_p equivalent-additively G_q), and is proved infinite; it is not defined as equality of prime labels.

The source's English pure-subgroup/direct-sum definition and the standard torsion-free convention agree with [Fuchs and Rangaswamy, Valuated Butler groups of finite rank (2006), Introduction p.336 item (1)](https://doi.org/10.1017/S144678870001404X).

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, transitive axiom audits for every theorem and the infinite-primes instance, and full official leanchecker --fresh Main replay are required. Full LaTeX/PDF and source-bound logs/receipts accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review the source/report/PDF; organizer acceptance is pending.
