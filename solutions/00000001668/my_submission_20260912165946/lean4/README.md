# Lean 4 formalisation — status: COMPLETE

This directory contains a complete, compiling Lean 4 formalisation of the
**refutation** of conjecture `00000001668`. It builds with **core Lean 4 only**
— no Mathlib, no `sorry`, no extra axioms.

```
$ lake build
Build completed successfully (3 jobs).
```

## Contents

| file | purpose |
|---|---|
| `Main.lean` | the formalisation (namespace `Tlmc1668`) |
| `Check.lean` | `#print axioms` audit for every headline theorem |
| `lakefile.toml` | Lake configuration, library name `tlmc1668` |
| `lean-toolchain` | `leanprover/lean4:v4.33.1` |

## Build

```bash
lake build                # compiles Main.lean
lake env lean Check.lean  # prints the axiom profile of each theorem
```

`lake env` (rather than a bare `lean`) is required so that `Check.lean` can find
the local module `Main`. No network access is needed and nothing is downloaded.

## What is formalised

The refutation of the conjecture rests on two explicit finite certificates. Both
are formalised, and both are verified edge by edge by `decide` — the kernel
evaluates every edge of every graph, so there is no unverified case analysis.

| theorem | statement |
|---|---|
| `circDist_lt` | `circDist p a b < p` |
| `circDist_pos` | `a ≠ b → 1 ≤ circDist p a b` |
| `circDist_self` | `circDist p a a = 0` |
| `isPQ_iff` | the computable `List.all` form of `isPQ` equals the paper's `∀ e ∈ E` form |
| `proper_is_pq` | a proper `k`-colouring is a `(k,1)`-colouring — i.e. `χ_c ≤ χ` at `q = 1` |
| `gp51_has_5_2_colouring` | `isPQ G51 5 2 c51 = true` — all 15 edges checked |
| `gp61_has_2_1_colouring` | `isPQ G61 2 1 c61 = true` — all 18 edges checked |
| `gp61_proper` | `c61` is a proper 2-colouring of `G(6,1)` |
| `gp61_bipartite` | `G(6,1)` admits a proper 2-colouring |
| `gp61_below_3` | `χ_c(G(6,1)) < 3`, witnessed by the `(2,1)`-colouring |
| `gp51_below_4` | `χ_c(G(5,1)) < 4`, witnessed by the `(5,2)`-colouring |
| `branch_S3_refuted` | `(6,1) ∈ S₃` **and** `χ_c(G(6,1)) < 3` |
| `branch_otherwise_refuted` | `(5,1) ∉ S₃` **and** `χ_c(G(5,1)) < 4` |
| `conjecture_00000001668_false` | the conjunction of the two branch refutations |

## Proof structure

1. **`circDist`.** `absDiff a b := if a ≤ b then b - a else a - b`, and
   `circDist p a b := min (absDiff a.val b.val) (p - absDiff a.val b.val)`.
   This is the paper's `min(d mod p, p − (d mod p))` with `d = a − b`; taking
   the absolute value before reducing is immaterial because `min` follows.
   Only the inequalities actually needed by `proper_is_pq` are proved —
   positivity and the strict upper bound — plus reflexivity, which
   `gp61_proper` uses. Symmetry of the circular distance is not needed anywhere
   and is therefore not proved.
2. **Graphs.** A graph on `Fin m` is a `structure Graph (m : Nat)` carrying an
   edge list. Each edge is recorded once as an ordered pair; the `(p,q)`
   constraint is symmetric in the endpoints, so the orientation is immaterial.
3. **`isPQ`.** Stated with `List.all`, not as a `∀` over edges, because
   `∀ e : Fin m × Fin m` has **no `Decidable` instance in core Lean** (there is
   no `Fintype` instance for product types), so `decide` cannot evaluate it.
   `isPQ_iff` bridges back to the readable propositional form via
   `List.all_eq_true`, and `proper_is_pq` is proved in the propositional form.
4. **The graphs.** `gp n k hn` builds `G(n,k)`'s edge list from `List.finRange n`
   with `(i.val + 1) % n` and `(i.val + k) % n`, so the formal definition is
   literally Definition 2.1 of the paper rather than a hand-written edge list.
   `G51 := gp 5 1 _` and `G61 := gp 6 1 _`.
5. **The certificates.** `c51` and `c61` transcribe the colourings exhibited in
   §4 of the paper. `gp51_has_5_2_colouring` and `gp61_has_2_1_colouring` are
   each a single `decide`: the kernel reduces the whole edge list.
6. **The refutation.** `HasColouringBelow G a b` says `G` admits a `(p,q)`-
   colouring with `p/q < a/b` (cross-multiplied as `p * b < a * q`). Since
   `χ_c` is the *infimum* of the realised ratios, a realised ratio below `a/b`
   gives `χ_c(G) < a/b`. This is the only property of the infimum used, so
   `χ_c` itself is deliberately not formalised — the constructive statement is
   used instead, which keeps the whole development in core Lean.

## Axiom profile

`Check.lean` prints, for every theorem in the table above:

```
'Tlmc1668.<theorem>' depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are the standard core axioms of Lean 4. There is no
`Classical.choice`, no `sorryAx`, and no user-declared `axiom`.

```
$ grep -n "sorry\|admit\|axiom " Main.lean Check.lean
(no output)
```

## Scope: what is *not* formalised

This is the one point a reviewer should check explicitly, so it is stated
plainly.

**Not formalised: Brooks' theorem, and therefore the paper's stronger
structural claim.** §3 of `main.tex` argues that `χ_c(G(n,k)) ≤ 3` for
*every* admissible `(n,k)`, so that the "4 otherwise" branch is not merely
wrong at `(5,1)` but unattainable anywhere. That argument rests on Brooks'
theorem, which is a research theorem. It is **neither formalised here nor
assumed as a hypothesis** — it does not appear in `Main.lean` in any form.

**This is a deliberate scope decision, and it does not weaken the disproof.**
§4 of `main.tex` gives the same conclusion by a second, independent route: two
explicit finite certificates. Refuting a two-valued classification table
requires contradicting one of its two values, and the certificates do exactly
that, unconditionally. So `conjecture_00000001668_false` is a complete
refutation of the conjecture, with no unproved input.

Two further consequences worth recording:

- `gp61_proper` is derived *from* `gp61_has_2_1_colouring` through `isPQ_iff`,
  not asserted; this is what shows that `(p,q) = (2,1)` really does mean
  "proper". `gp61_has_2_1_colouring'` then feeds the proper colouring back into
  the general lemma `proper_is_pq` and recovers the same `isPQ` statement. The
  two directions of the bridge are therefore both exercised by the build.
- `proper_is_pq` is proved for **arbitrary** `G` and `k`. It is the formal
  content of `χ_c ≤ χ` at `q = 1` and is stated generally rather than being
  inlined into the `G(6,1)` case.

The structural Brooks argument remains in LaTeX only. If the maintainers want it
formalised as well, that is a substantially larger piece of work and should be
agreed before submission; it is flagged rather than silently omitted.

## Notes for a reviewer

Five traps specific to core Lean 4 were hit while writing this file. They are
recorded because each one produces an error message that does not point at the
real cause.

1. **`∀ e : Fin m × Fin m` is not decidable.** There is no `Fintype` instance for
   product types in core Lean, so `Decidable (∀ e : α × β, P e)` cannot be
   synthesised and `decide` fails with
   `failed to synthesize Decidable (…)`. Hence `isPQ` is stated with `List.all`.
2. **Order-theoretic lemmas are not all in the prelude.** `le_refl`,
   `le_max_left`, `le_max_right`, `max_lt` and `lt_of_le_of_lt` are *not*
   available without further imports, while `Nat.sub_self`, `Nat.min_zero`,
   `Nat.mod_lt`, `Nat.sub_le` and `Nat.succ_le_of_lt` are. The development was
   therefore written against `omega` plus the `Nat.*` lemmas, which removed the
   dependency on the generic order hierarchy entirely.
3. **`omega` handles `Nat.min` and `Nat.max`.** This is what makes
   `circDist_lt` and `circDist_pos` one-liners after unfolding, rather than a
   case analysis over which of the two arguments of `min` is smaller.
4. **A `def` returning a `Prop` is not unfolded by `decide`'s instance search.**
   `inS3` was originally a `def`, and `by decide` on `inS3 6 1` failed with
   `failed to synthesize Decidable (inS3 6 1)`. Making it an `abbrev` fixed it.
   The same applies to `RatioLt`.
5. **`Fin n` numeral patterns in a `def` body need a catch-all.** `c51` and
   `c61` match on `i.val` with an explicit branch per residue and a final
   `| _ => 0`. The catch-all is unreachable (`i.val < 10`, resp. `< 12`) but is
   required for the match to elaborate.

The file has been compiled from a clean directory (no `.lake`, no manifest) as a
reviewer would, and the axiom output above was produced from that clean build.
