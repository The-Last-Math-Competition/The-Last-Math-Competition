# Disproof of 00000001216: a legal devil schedule defeats every angel strategy

The actual infinite three-row board is Z × Fin 3, starting at (0,0). A fixed legal schedule first blocks the four columns -31,-30,30,31 in twelve turns. The angel's first twelve moves cannot pass them. The finished two-thick walls trap it in -29 through 29; 177 further turns eat every interior square. No 190th legal angel move is possible after 189 devil burns.

The proof lets the angel move first, change rows arbitrarily and even stay put. It therefore covers both the literal three-row lattice strip and a periodic identification of the three rows, as well as all standard king-distance-two moves. The finite interval is derived from the infinite-board rules. The devil's entire infinite schedule is injective and does not depend on angel responses. Turn indexing explicitly permits burning the currently occupied square without incorrectly banning that landing in advance, as in [Conway's original rules, Introduction, p.3](https://library.slmath.org/books/Book29/files/conway.pdf).

Lean proves the finite 190-move obstruction, the absence of any infinite legal response path, and defeat of every arbitrary full-history response strategy. This disproves the cylinder winning necessary clause, including its proposed local strategy. No independent half-plane conclusion is claimed.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, fourteen transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF and source-bound receipts accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review the source/report/PDF; organizer acceptance is pending.
