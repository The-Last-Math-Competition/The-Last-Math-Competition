# TLMC-00000004396 — Refutation submission

**Conjecture.** "All Möbius ladders are Sidorenko, and every odd
subdivision of a tree is Sidorenko, and the union of the two families
gives infinitely many new nontrivial members."

**Verdict: REFUTED.** The first conjunct is false: not all Möbius
ladders are Sidorenko.

## The refutation

A finite graph `G` is *Sidorenko* iff for every finite host `H`,

    hom(G,H) · |V(H)|^{|E(G)|} ≥ hom(K₂,H)^{|E(G)|} · |V(H)|^{|V(G)|}.

Taking `H = K₂`: if `G` is non-bipartite then `hom(G,K₂) = 0` while the
right-hand side is `≥ 1` (the identity map `K₂ → K₂`), so the inequality
fails. Hence **every Sidorenko graph is bipartite**.

The Möbius ladder `M_k` on `2k` vertices is bipartite iff `k` is odd.
`M₂` has rim `i ~ i±1` and spokes `i ~ i+2` on `Z₄` — every pair of
distinct vertices is adjacent, so `M₂ ≅ K₄`, which is non-bipartite and
therefore not Sidorenko. The same holds for all even `k` (`M₄, M₆, …`).

## Layout

- `main.tex` / `build/main.pdf` — write-up of the refutation.
- `reproduce.py` — brute-force verification: computes bipartiteness of
  `M_n` for `n = 2..8` and checks `hom(M_n,K₂)·2^{e} vs
  hom(K₂,K₂)^{e}·2^{2n}` for the non-bipartite ones (all fail).
  Run: `python3 reproduce.py`.
- `lean4/` — Lean 4 + Mathlib (`v4.33.1`) formalization.
  - `Main.lean` defines `mobiusLadder n : SimpleGraph (ZMod (2*n+2))`
    (classical `M_{n+1}`; shift keeps the modulus ≥ 2 so the graph is
    simple for all `n`), `homCount` (via `Nat.card`), `IsSidorenko`,
    and proves:
    - `mobiusLadder_one_eq_top` — `mobiusLadder 1 = ⊤` on `ZMod 4`
      (i.e. `M₂ = K₄`), by `fin_cases` + `rfl` on each disjunct;
    - `isEmpty_hom_K4_K2` — pigeonhole: three pairwise-distinct values
      in `Fin 2` (`omega`);
    - `isEmpty_hom_top_zmod4_K2` — transport along `Fin 4 ≃ ZMod 4`
      (`ZMod.finEquiv`);
    - `homCount_mobiusLadder_one_K2` — `hom(M₂,K₂) = 0`;
    - **`not_sidorenko_mobiusLadder_one`** — `¬ IsSidorenko (mobiusLadder 1)`.
  - `Check.lean` audits axioms; output:
    `[propext, Classical.choice, Quot.sound]` for every theorem —
    no `sorryAx`, no `native_decide`, no `ofReduceBool`.

## Reproduce the Lean check

```bash
export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd lean4 && lake build          # builds Main (mathlib is pinned v4.33.1)
lake env lean Check.lean        # prints the axiom audit
```

Build confirmed: `lake build` exit 0 (8707 jobs, warnings only —
style lints, no errors, no `sorry`).
