# Lean 4 formalisation — status: COMPLETE

This project formalises the **finite residue shadow** of the disproof of
conjecture `00000000747`. It targets **core Lean 4 only** (`import Std`, no
Mathlib), with no `sorry`, no `axiom`, and no `native_decide`.

```bash
lake build                  # Build completed successfully
lake env lean Check.lean    # prints the axiom dependencies of every theorem
```

The build was verified with the pinned toolchain `leanprover/lean4:v4.33.1`.

## Scope — what is and is not formalised

**Not formalised: the $p$-adic integers $\mathbb{Z}_p$.** Core Lean 4 has no
$p$-adic numbers, and this project deliberately has no dependencies, so the
statement "the fixed points of $x \mapsto x^p$ on $\mathbb{Z}_p$ are exactly the
$p$ Teichmüller roots" is **not** a Lean theorem here.

What the Lean file does formalise is the **finite residue shadow**: the
decidable arithmetic facts about $x^5 = x$ modulo powers of $5$. The step that
upgrades these finite facts to $\mathbb{Z}_p$ is **Hensel's lemma**, which is
proved in `main.tex` (Lemma "Hensel, simple-root form") and verified numerically
by `reproduce.py`. In particular:

- `fermat_five` / `roots_mod_5` are the $p = 5$ instance of Fermat's little
  theorem, i.e. the statement that all five residues are roots modulo $5$.
- `nontrivial_root_mod_5_pow_8` exhibits the concrete non-trivial root
  $110443$ of $x^5 = x$ modulo $5^8$.
- `hensel_step_k1` is one concrete Hensel lifting step ($k = 1 \to k = 2$ at
  $p = 5$), the finite instance of the general Hensel lemma.
- The general Hensel step, the count $p$, and the passage to $\mathbb{Z}_p$ are
  argued in `main.tex` and checked in `reproduce.py`; they are **outside** the
  Lean development.

## Contents

| file | purpose |
|---|---|
| `Main.lean` | the finite-residue formalisation |
| `Check.lean` | `#print axioms` for each theorem — the machine-checkable evidence |
| `lakefile.toml` | Lake configuration, no dependencies |
| `lean-toolchain` | pins `leanprover/lean4:v4.33.1` |

## Theorems

| theorem | statement |
|---|---|
| `fermat_five` | `∀ x : Fin 5, x.val ^ 5 % 5 = x.val % 5` |
| `roots_mod_5` | `∀ x : Fin 5, x.val ^ 5 % 5 = x.val` |
| `nontrivial_root_mod_5_pow_8` | `110443 ^ 5 % 5^8 = 110443 % 5^8 ∧ 110443 % 5^8 ≠ 0 ∧ 110443 % 5^8 ≠ 1` |
| `hensel_step_k1` | every root mod `5` lifts to a root mod `25` congruent to it mod `5` |
| `conjecture_00000000747_false` | three pairwise distinct roots mod `5^8` (`0`, `1`, `110443`) and all five residues roots mod `5` |

The main theorem `conjecture_00000000747_false` contradicts the claim that the
only fixed points are `0` and `1`: modulo `5^8` there are at least the three
pairwise distinct roots `0`, `1`, `110443`, and over `F_5` all five residues are
roots. These finite facts are the decidable shadow of the $p$-adic statement
"there are exactly $p$ fixed points".

## Proof structure

1. `fermat_five`, `roots_mod_5`, `nontrivial_root_mod_5_pow_8` and
   `conjecture_00000000747_false` are closed statements over `Fin 5`, `Fin 25`
   and `Nat`; they are discharged by kernel-checked `decide`.

2. `hensel_step_k1` is a `∀ x : Fin 5, … → ∃ y : Fin 25, …`. The existential
   quantifies over the finite type `Fin 25`, so `decide` enumerates the
   candidates and checks the unique lift for each of the five roots modulo `5`.
   `set_option maxRecDepth 100000` gives the elaborator enough fuel for the
   `Fin 25` search and the large power `110443 ^ 5`.

3. No arithmetic tactic beyond `decide` is used. There is no `Rat`, so the
   `decide`-cannot-reduce-`Rat` pitfall is avoided by construction.

The mathematical content of the paper — Fermat mod $p$, the derivative
$f'(x) \equiv -1 \pmod p$, Hensel's lemma, the count $p$, and the explicit
$p = 5$ example — is in `main.tex`; the finite instances are in Lean.

## Axiom dependencies

`lake env lean Check.lean` prints exactly:

```
'Tlmc747.fermat_five' does not depend on any axioms
'Tlmc747.roots_mod_5' does not depend on any axioms
'Tlmc747.nontrivial_root_mod_5_pow_8' does not depend on any axioms
'Tlmc747.hensel_step_k1' depends on axioms: [propext, Quot.sound]
'Tlmc747.conjecture_00000000747_false' does not depend on any axioms
```

There is **no `sorryAx`** and **no `Lean.ofReduceBool`**. The only nonempty
dependency list is the standard core pair `[propext, Quot.sound]`, pulled in by
the `Fintype`/`Decidable` machinery used in the `∃`-statement; it introduces no
mathematical assumption.

## Environment

Lean 4 `v4.33.1` (pinned by `lean-toolchain`), core only, no Mathlib.
