/-
  Disproof of conjecture 00000000747.

  The conjecture: for p >= 5 the iterative fixed points of x |-> x^p in the
  p-adic integers Z_p are only 0 and 1 ("rigidity of superattracting orbits").

  Refutation.  The fixed points of x |-> x^p on Z_p are the roots of
  f(x) = x^p - x.  Modulo p every residue is a root by Fermat's little theorem
  (x^p = x in F_p), and f'(x) = p*x^(p-1) - 1 = -1 (mod p) is a unit, so each
  residue class contains exactly one root in Z_p by Hensel's lemma.  Hence there
  are exactly p roots, namely {0} together with the Teichmuller roots mu_{p-1}.
  For p >= 5 that is at least 5 roots, not 2.

  What this file formalises.  Core Lean 4 has no p-adic integers, and this
  project deliberately uses core Lean only (`import Std`, no Mathlib).  So the
  Lean development formalises the *finite residue shadow* of the argument:

    * Fermat's little theorem modulo 5 (`fermat_five`, `roots_mod_5`),
    * the explicit non-trivial root 110443 of x^5 = x modulo 5^8
      (`nontrivial_root_mod_5_pow_8`),
    * one concrete Hensel lifting step, k = 1 -> k = 2 at p = 5
      (`hensel_step_k1`),
    * the packaged disproof `conjecture_00000000747_false`.

  The full statement that the p-adic fixed-point set has exactly p elements ---
  including the derivative computation and Hensel's lemma that upgrade this
  finite shadow to Z_p --- is proved in `main.tex` and checked numerically in
  `reproduce.py`.  The Lean file does NOT formalise Z_p.

  Everything here is discharged by kernel-checked `decide`; there is no
  `sorry`, no `axiom`, and no `native_decide`.
-/

import Std

namespace Tlmc747

set_option maxRecDepth 100000

/-- Fermat's little theorem at `p = 5`, stated over the five residues:
every `x : Fin 5` satisfies `x^5 = x (mod 5)`. -/
theorem fermat_five : ∀ x : Fin 5, x.val ^ 5 % 5 = x.val % 5 := by
  decide

/-- All five residues modulo 5 are roots of `x^5 = x`. -/
theorem roots_mod_5 : ∀ x : Fin 5, x.val ^ 5 % 5 = x.val := by
  decide

/-- The explicit non-trivial root `110443` of `x^5 = x` modulo `5^8`.
It satisfies `110443^5 = 110443 (mod 5^8)`, and `110443 mod 5^8 = 110443`
is neither `0` nor `1`.  (Its residue modulo `5` is `3`; `reproduce.py` also
exhibits the Hensel lift of the class `2 mod 5`, which is `280182 mod 5^8`.) -/
theorem nontrivial_root_mod_5_pow_8 :
    (110443 : Nat) ^ 5 % (5 ^ 8) = 110443 % (5 ^ 8) ∧
    110443 % (5 ^ 8) ≠ 0 ∧
    110443 % (5 ^ 8) ≠ 1 := by
  decide

/-- One concrete Hensel lifting step at `p = 5`: every root `x` of `x^5 = x`
modulo `5` lifts to a root `y` of `x^5 = x` modulo `25` with `y = x (mod 5)`.
This is the finite (`k = 1` to `k = 2`) instance of Hensel's lemma; the general
statement is proved in `main.tex`. -/
theorem hensel_step_k1 :
    ∀ x : Fin 5, x.val ^ 5 % 5 = x.val % 5 →
      ∃ y : Fin 25, y.val % 5 = x.val ∧ y.val ^ 5 % 25 = y.val % 25 := by
  decide

/-- **Conjecture 00000000747 is false (finite residue shadow).**

Modulo `5^8 = 390625` there are at least three pairwise distinct roots of
`x^5 = x`: `0`, `1`, and `110443`.  This contradicts the claim that the fixed
points are only `0` and `1`.  Moreover, over `F_5` all five residues are roots,
so the modulo-`5` reading of the claim is false as well.

The upgrade of this finite residue statement to `Z_p` is Hensel's lemma, proved
in `main.tex`; the Lean statement here is intentionally the decidable shadow. -/
theorem conjecture_00000000747_false :
    (0 % (5 ^ 8) ≠ 1 % (5 ^ 8) ∧
     0 % (5 ^ 8) ≠ 110443 % (5 ^ 8) ∧
     1 % (5 ^ 8) ≠ 110443 % (5 ^ 8)) ∧
    (0 ^ 5 % (5 ^ 8) = 0 % (5 ^ 8) ∧
     1 ^ 5 % (5 ^ 8) = 1 % (5 ^ 8) ∧
     110443 ^ 5 % (5 ^ 8) = 110443 % (5 ^ 8)) ∧
    (∀ x : Fin 5, x.val ^ 5 % 5 = x.val) := by
  decide

end Tlmc747
