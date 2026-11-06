# Disproof of conjecture 00000000479

The conjecture asserts that the number `N_k` of matchings of the order-`n`
Aztec diamond containing exactly `k` main-diagonal lozenges satisfies

- `v_2(N_k) = 0` when `k ≡ 0 (mod 4)`,
- `v_2(N_k) = 1` otherwise,

with period 4.

This is false. The smallest counterexample is at order `n = 2`:

| `k` | `N_k` | `v_2(N_k)` | conjectured |
|-----|-------|------------|-------------|
| 0   | 1     | 0          | 0           |
| 2   | 3     | 0          | **1**       |
| 4   | 3     | 0          | 0           |
| 6   | 1     | 0          | **1**       |

Both strata with `k ≢ 0 (mod 4)` have odd cardinality, so their 2-adic
valuation is `0`, not `1`. The failure is not an edge phenomenon: at order 3
the stratum `k = 6` has `N_6 = 20` with `v_2 = 2 ≠ 1`, and at order 4 the
stratum `k = 8` has `N_8 = 210`, which is even although `8 ≡ 0 (mod 4)` — so
even the "vanishing" half fails.

The count is orientation-independent: reflection in `x = y` swaps horizontal
and vertical dominoes, so the horizontal and vertical stratum sizes coincide.

## The Lean project

`Main.lean` encodes the order-1 and order-2 Aztec diamonds as explicit lists of
cells, enumerates their matchings with the total recursive function `search`,
and kernel-checks the stratum sizes. The two counting theorems needed are
`stratum2_order2` (`N_2 = 3`) and `three_is_odd` (`¬ 2 ∣ 3`). The file has no
imports at all: it depends only on Lean's `Init` core, not on `Std` or
Mathlib, so `lake build` is fast and has no external dependency.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

`Check.lean` prints the axioms of every theorem; none should report `sorryAx`
or any extra axiom. No `sorry`, no `native_decide`, and no additional axiom is
used. The search is not left unformalised — it is a definition, and the counts
are decided in the kernel.

## Compilation evidence

`Main.lean` (94 lines, md5 `e2e6e2394efeca3faa44636c250bfa29`) was compiled in
full and reports **0 errors, 0 warnings**:

```text
Compiled without errors.   3.2 s · Lean 4.30.0
Problems: No problems. Lean reported nothing to fix.
```

The axiom audit returns

```text
'Tlmc479.refutation_order2' depends on axioms: [propext]
'Tlmc479.refutation_order1' depends on axioms: [propext]
'Tlmc479.strata_partition' does not depend on any axioms
'Tlmc479.matchings2_card' does not depend on any axioms
```

so the reachable axiom set is contained in `{propext}` — well inside the
`{propext, Classical.choice, Quot.sound}` envelope that accepted reviews in
this repository allow, and with no `sorryAx`.

The run above used a Lean 4.30.0 build. The file was additionally checked
against the pinned toolchain itself — `leanprover/lean4:v4.33.1` — through the
LSP endpoint of the official Lean web editor
(`wss://live.lean-lang.org/websocket/lean-v4.33.1`): the session initialises,
`didOpen` is sent, and the server publishes **zero diagnostics** for the file,
i.e. no errors and no warnings on v4.33.1.

That channel was validated against two controls before being trusted:

- a file with three deliberate mistakes produced three errors with correct line
  numbers, and
- appending `theorem bogus : (… filter …).length = 4` to this very file was
  rejected at line 97 with `Tactic decide proved that the proposition
  (List.filter (fun L => hcount L == 2) matchings2).length = 4 is false`,

which also confirms that the kernel really evaluates the enumeration (the count
is 3, not 4) rather than accepting it unexamined.

## Layout

```text
jiakeboge_submission_20261030002730/
├── main.tex     the report
├── main.pdf     the compiled report
├── README.md    this file
└── lean4/       the Lean 4 project
    ├── Main.lean
    ├── Check.lean
    ├── lakefile.toml
    └── lean-toolchain
```
