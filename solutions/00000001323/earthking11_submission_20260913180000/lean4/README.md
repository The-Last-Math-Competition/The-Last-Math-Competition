# Lean 4 formalisation (conjecture 00000001323)

This directory contains a Lean 4 formalisation of the algebraically identical
**finite-field model** of the counterexample that disproves conjecture
00000001323.

- Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
- Dependencies: none beyond core Lean + `Std` (`import Std`). **No Mathlib.**
- No `sorry`, no `axiom`, no `native_decide`.

## Build

```
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean
```

`lake build` should end with:

```
Build completed successfully (3 jobs).
```

`Check.lean` prints the axioms each theorem depends on. The expected output is

```
'TLMC1323.zeta_order_five' depends on axioms: [propext]
'TLMC1323.det_is_one' depends on axioms: [propext]
'TLMC1323.order_is_five' depends on axioms: [propext, Quot.sound]
'TLMC1323.conjecture_00000001323_false' depends on axioms: [propext, Quot.sound]
```

Only the standard Lean axioms `propext` and `Quot.sound` appear (they are used
internally by `decide`). There is no `sorryAx` and no `ofReduceBool`.

## Why a finite field, and what exactly is formalised

Core Lean has **no** `ℂ` (no complex numbers, no `Field`/`Matrix` typeclasses,
and no `ZMod`). The complex-analytic statement itself is therefore not
expressible in this dependency-free setting. What *is* expressible is the exact
algebraic computation on which the refutation rests, over a finite field.

The refutation's witness over $\mathbb{C}$ is
$A_m = \operatorname{diag}(\zeta_m, \zeta_m^{-1})$ with $\zeta_m$ a primitive
$m$-th root of unity. Its two defining properties are purely equational:

1. $\det A_m = \zeta_m \cdot \zeta_m^{-1} = 1$;
2. $A_m^k = I \iff \zeta_m^k = 1$, so the order of $A_m$ equals the
   multiplicative order of $\zeta_m$.

Both are instances of identities in a commutative monoid and hold over **any**
commutative ring containing a primitive $m$-th root of unity together with its
inverse. There is no use of characteristic $0$, of a topology, or of any
field-specific property beyond commutativity of multiplication. Consequently the
finite-field proof transfers verbatim to $\mathbb{C}$ by taking
$\zeta = \exp(2\pi i/m)$ and $3 \rightsquigarrow \zeta$, $4 \rightsquigarrow -1$
(exponent notation), $11 \rightsquigarrow$ the characteristic-$0$ ground field.

For the formal witness we take $m = 5$ over $\mathbb{F}_{11} = \mathtt{Fin\ 11}$.
The choice is forced by $5 \mid 10 = |\mathbb{F}_{11}^{\times}|$: the element
$3$ is a primitive $5$-th root of unity, with $3^{-1} \equiv 3^4 \pmod{11}$.

### Contents of `Main.lean`

- `TLMC1323.iterate` and the notation `f^[n]`: core `Std`, unlike Mathlib, has
  no `Function.iterate` and no `f^[n]` notation, so they are defined locally
  (plain `Nat` recursion).
- `TLMC1323.zeta_order_five`:
  $(3 : \mathbb{F}_{11})^5 = 1$ while
  $(3)^1, (3)^2, (3)^3, (3)^4 \ne 1$; i.e. $3$ has multiplicative order
  exactly $5$. Proved by `decide`.
- `TLMC1323.three_inv`: $3 \cdot 3^4 = 1$ in $\mathbb{F}_{11}$.
- `TLMC1323.A`: the diagonal linear map
  $A(v_1, v_2) = (3 v_1,\; 3^4 v_2)$ on $\mathbb{F}_{11}^2$, i.e. the matrix
  $\operatorname{diag}(3, 3^{-1}) = \operatorname{diag}(3, 3^4)$.
- `TLMC1323.detA` and `TLMC1323.det_is_one`: the determinant
  $\det A = 3 \cdot 3^4 = 1$.
- `TLMC1323.A_five_eq_id`: $A^5 = \mathrm{id}$ (verified coordinatewise; the
  type $\mathbb{F}_{11}^2$ is finite, so `decide` works after splitting the
  argument).
- `TLMC1323.order_is_five`: $A^5 = \mathrm{id}$ and $A^k \ne \mathrm{id}$ for
  $k = 1,2,3,4$; i.e. $A$ has order exactly $5$. The non-identity of the
  smaller powers is witnessed at the point $(1,0)$, where $A^k(1,0)=(3^k,0)$
  and $3^k \neq 1$.
- `TLMC1323.conjecture_00000001323_false`: the collected statement — there is a
  linear map $T$ on $\mathbb{F}_{11}^2$ of order exactly $5$ whose determinant
  is $1$, together with $5 \ne 1,2,3,4,6$.

The last theorem is the formal content of "the period set is not
$\{1,2,3,4,6\}$": the specific value $5$ occurs, and it is not one of the six
claimed values.

## Honest scope statement

The Lean development does **not** formalise $\operatorname{Aut}(\mathbb{C}^2)$
or the notion of a polynomial automorphism, because core Lean (with `import Std`
only, no Mathlib) cannot express the complex field. It formalises the
det/order computation for the diagonal witness over the finite field
$\mathbb{F}_{11}$, which is the algebraically identical instance of the general
argument. The transfer to $\mathbb{C}$ is by the coefficient-free nature of the
computation described above: replace the root of unity and keep the same proof.
