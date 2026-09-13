# Submission: disproof of conjecture 00000001323

- Conjecture file: `conjectures/00000001323.md`
- Verdict: **FALSE** (disproved)
- Submitter: earthking11
- Date: 2026-09-13

## The conjecture, verbatim

From `conjectures/00000001323.md`:

> **Definition.** The Jacobian-conjecture class in the automorphism group
> Aut(Cⁿ). **Conjecture.** In Aut(C²), the set of possible periods of elements
> with Jacobian constant 1 is {1, 2, 3, 4, 6} (a conformal-symmetry restriction).

(The Chinese text says the same: the possible lengths of periods of elements of
Aut(ℂ²) with Jacobian constant 1 form the set {1, 2, 3, 4, 6}, a
"conformal-symmetry restriction".)

## The counterexample

For every $m \ge 1$ let $\zeta_m$ be a primitive $m$-th root of unity (over
$\mathbb{C}$) and set

$$A_m = \operatorname{diag}(\zeta_m, \zeta_m^{-1})
      = \begin{pmatrix} \zeta_m & 0 \\ 0 & \zeta_m^{-1} \end{pmatrix}.$$

Then:

1. **It is an automorphism.** $A_m \in \operatorname{GL}_2(\mathbb{C}) \subseteq
   \operatorname{Aut}(\mathbb{C}^2)$; it is linear, hence polynomial, with
   inverse $\operatorname{diag}(\zeta_m^{-1}, \zeta_m)$.
2. **Its Jacobian is identically the constant-1 determinant.** For a linear map
   the Jacobian is the (constant) matrix of the map, so $\operatorname{Jac} A_m
   = A_m$ and $\det \operatorname{Jac} A_m = \det A_m = \zeta_m \cdot
   \zeta_m^{-1} = 1$ identically.
3. **Its order is exactly $m$.** Since $A_m^k =
   \operatorname{diag}(\zeta_m^k, \zeta_m^{-k})$, this equals $I$ iff
   $\zeta_m^k = 1$ iff $m \mid k$; the least positive such $k$ is $m$.

Hence **every** positive integer $m$ is a period of an element with Jacobian
determinant identically 1. In particular $m = 5$ occurs, and
$5 \notin \{1,2,3,4,6\}$ (indeed $5 \ne 1,2,3,4,6$). The conjectured period set
is therefore not $\{1,2,3,4,6\}$; in fact the true period set is all of
$\mathbb{N}_{>0}$.

The concrete witness for the conjunctive claim is
$A_5 = \operatorname{diag}(e^{2\pi i/5}, e^{-2\pi i/5})$, with
$\det A_5 = 1$ and order $5$.

## Honest treatment of the reading issue

The claim **would be true** if it were restricted to automorphisms with
**integer** (or rational) coefficients. Indeed, the finite-order elements of
$\operatorname{SL}_2(\mathbb{Z})$ have orders exactly
$$\{1,2,3,4,6\},$$
realised by the rotations of orders 1, 2, 3, 4, 6 (equivalently: the $n$ with
$\varphi(n) \le 2$ are $n = 1,2,3,4,6$). The conjecture as written, however,
says $\operatorname{Aut}(\mathbb{C}^2)$ **over $\mathbb{C}$**, with no
integrality hypothesis, and the witness above is a perfectly valid
$\mathbb{C}$-coefficient element. So the restriction to integer coefficients is
a genuinely different (and true) statement, not the one in the file.

Related readings that also do not save the conjecture:

- **Requiring non-linearity does not help.** Conjugating $A_m$ by any non-linear
  polynomial automorphism $H$ gives $F = H \circ A_m \circ H^{-1}$, a non-linear
  finite-order automorphism with $\det \operatorname{Jac} F \equiv 1$ and the
  same order $m$, for every $m$ (chain rule and multiplicativity of the
  determinant). See `main.tex`, Proposition 2.2.
- **Reading "Jacobian constant 1" as "the Jacobian is literally the identity
  matrix"** would give the period set $\{1\}$: $\operatorname{Jac} F = I$ forces
  $F$ to be a translation, and a non-trivial translation has infinite order.
  This is even further from $\{1,2,3,4,6\}$.

## Files

| Path | Purpose |
| --- | --- |
| `main.tex` | Standalone article with the full proof, the non-linearity remark, and the integer-coefficient discussion. |
| `build/main.pdf` | Compiled article (produced by `tectonic --outdir build main.tex`). |
| `reproduce.py` | Stdlib + sympy script; symbolically builds $\operatorname{diag}(\zeta_m, \zeta_m^{-1})$ for $m = 5..12$ and verifies $\det = 1$ and order exactly $m$. |
| `lean4/` | Lean 4 formalisation of the algebraically identical finite-field witness over $\mathbb{F}_{11}$. |
| `lean4/Main.lean` | The formalised theorem. |
| `lean4/Check.lean` | Axiom audit. |
| `lean4/README.md` | Details of what the Lean file formalises and the transfer to $\mathbb{C}$. |

## Reproduction

### Python

```
python3 reproduce.py
```

Prints PASS/FAIL per $m \in \{5,\dots,12\}$ and exits 0 on success.

### LaTeX

```
tectonic --outdir build main.tex
```

### Lean

```
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean
```

## Note on what the Lean development proves

Core Lean (no Mathlib) has no field $\mathbb{C}$, so `lean4/Main.lean`
formalises the *algebraically identical finite-field model*: over
$\mathbb{F}_{11}$ the element $3$ has multiplicative order exactly $5$
(because $5 \mid 10 = |\mathbb{F}_{11}^\times|$), and the diagonal map
$\operatorname{diag}(3, 3^{-1}) = \operatorname{diag}(3, 3^4)$ has determinant
$1$ and order exactly $5$. The determinant/order computation is coefficient-free
and transfers verbatim to $\mathbb{C}$ with $\zeta_5 = e^{2\pi i/5}$. See
`lean4/README.md` for the precise scope. The file contains no `sorry`, no
`axiom`, and no `native_decide`; the only axioms reported for the main theorem
are the standard `propext` and `Quot.sound` (used by `decide`), with no
`sorryAx`.
