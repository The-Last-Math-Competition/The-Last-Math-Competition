# Disproof of conjecture `00000003844`

**Verdict: FALSE.**

This submission disproves conjecture `00000003844` as stated. The refutation is
unconditional and completely elementary. The finite-type $0$-Hecke monoid
$H(S_3)$ (the $0$-Hecke monoid of type $A_2$, with $6$ elements) has covering
number **exactly $2$**, so it is a counterexample to the conjecture's first
clause. The same construction shows that every finite-type $0$-Hecke monoid of
rank $\ge 2$ has covering number exactly $2$ (in particular $H(S_4)$, with $24$
elements). The direct-product clause fails as well, since
$\operatorname{cov}(M_1\times M_2)\le \operatorname{cov}(M_1)\operatorname{cov}(M_2)$,
so $H(S_3)\times H(S_3)$ has covering number at most $4$, not $\infty$.

## The conjecture

Quoted verbatim from `conjectures/00000003844.md`:

> **English.** Definition: The covering number of a monoid is the least number
> of proper submonoids needed to cover it, infinity if impossible. Conjecture:
> Every finite-type 0-Hecke monoid and every plactic monoid has infinite
> covering number, and arbitrary direct products of these two classes still
> have infinite covering number. (uncoverable direct product closure)
>
> **中文。** 定义：幺半群的覆盖数指把它写成真子幺半群之并所需的最少个数,不可写则记为无穷。猜想：每个有限型 0-Hecke 幺半群与每个 plactic 幺半群的覆盖数均为无穷,且这两类幺半群的任意直积的覆盖数仍为无穷。（不可覆盖的直积封闭）

The statement has three components:

1. every finite-type $0$-Hecke monoid has infinite covering number;
2. every plactic monoid has infinite covering number;
3. arbitrary direct products of these two classes still have infinite covering
   number.

Component 1 is a universal statement over the finite-type $0$-Hecke monoids; a
**single** counterexample refutes it. Component 3 is refuted by the product
bound below. Since the conjecture is a conjunction, components 1 and 3 being
false is enough; we make no claim about plactic monoids (component 2), which is
not needed.

## The covering-number definition

A **submonoid** of a monoid $M$ is a subset containing the identity $e$ and
closed under the product.

**Definition.** The **covering number** $\operatorname{cov}(M)$ is the least
$k\ge 1$ such that $M=S_1\cup\cdots\cup S_k$ for **proper** submonoids
$S_i\subsetneq M$; if no finite such cover exists, $\operatorname{cov}(M)=\infty$.

Note that a single proper submonoid can never cover $M$ (a proper subset is not
all of $M$); hence a finite covering number is always at least $2$.

## The Demazure product and the explicit $H(S_3)$ table

For a finite Coxeter system $(W,S)$, the **$0$-Hecke monoid** $H(W)$ has
generators $\pi_s$ ($s\in S$) with relations $\pi_s^2=\pi_s$ and the braid
relations of $(W,S)$. Its elements are indexed by $W$, and the product is the
**Demazure product**
$$\pi_u\,\pi_v=\pi_{u\star v},\qquad
u\star s=\begin{cases}us,&\ell(us)>\ell(u),\\ u,&\ell(us)<\ell(u),\end{cases}$$
extended over a reduced word of $v$; here $\ell$ is the Coxeter length. The
product $\star$ is associative, the generators are idempotent, and $\pi_e$ is
the identity.

The smallest counterexample is $H(S_3)$ for the rank-$2$ system
$(S_3,\{s_1,s_2\})$ of type $A_2$. Its six elements and the Demazure product
are ($\star$ read as "row $\star$ column"; indices as in `lean4/Main.lean`):

Index labelling: `0 = e`, `1 = s2`, `2 = s1`, `3 = s1s2`, `4 = s2s1`, `5 = w0`.

| $\star$ | $e$ | $s_2$ | $s_1$ | $s_1s_2$ | $s_2s_1$ | $w_0$ |
|:--------|:----|:------|:------|:---------|:---------|:------|
| $e$      | $e$      | $s_2$    | $s_1$    | $s_1s_2$ | $s_2s_1$ | $w_0$ |
| $s_2$    | $s_2$    | $s_2$    | $s_2s_1$ | $w_0$    | $s_2s_1$ | $w_0$ |
| $s_1$    | $s_1$    | $s_1s_2$ | $s_1$    | $s_1s_2$ | $w_0$    | $w_0$ |
| $s_1s_2$ | $s_1s_2$ | $s_1s_2$ | $w_0$    | $w_0$    | $w_0$    | $w_0$ |
| $s_2s_1$ | $s_2s_1$ | $w_0$    | $s_2s_1$ | $w_0$    | $w_0$    | $w_0$ |
| $w_0$    | $w_0$    | $w_0$    | $w_0$    | $w_0$    | $w_0$    | $w_0$ |

Direct checks (all reproduced by `reproduce.py` and, for this table, by
`lean4/Main.lean`):

- **associativity**: all $6^3=216$ triples;
- **identity**: $e\star x=x\star e=x$;
- **idempotent generators**: $s_1\star s_1=s_1$, $s_2\star s_2=s_2$;
- **braid relation**: $s_1\star s_2\star s_1=w_0=s_2\star s_1\star s_2$, with
  $s_1\star s_2=s_1s_2$ and $s_2\star s_1=s_2s_1$.

## The $A/B$ covering, and why $1$ does not suffice

Take
$$A=\{e,s_2\},\qquad B=H(S_3)\setminus\{s_2\}=\{e,s_1,s_1s_2,s_2s_1,w_0\}.$$

- $A$ is a submonoid: it contains $e$, and $s_2\star s_2=s_2$.
- $B$ is a submonoid: it contains $e$; for closure, if $x,y\in B$ and
  $x\star y=s_2$, then by the length identity (below)
  $1=\ell(s_2)=\ell(x\star y)\ge\max(\ell(x),\ell(y))$, so
  $x,y\in\{e,s_1,s_2\}$; since $x,y\ne s_2$, the table gives
  $x\star y\in\{e,s_1\}$, contradiction.
- Both are proper: $|A|=2<6$ and $|B|=5<6$.
- $A\cup B=H(S_3)$: every element is either $s_2$ (in $A$) or one of the other
  five (in $B$).

So $\operatorname{cov}(H(S_3))\le 2$.

**No $1$-cover.** A single proper submonoid cannot cover, since it is a proper
subset. Exhaustively, `reproduce.py` enumerates all submonoids of $H(S_3)$
(there are $16$, including $H(S_3)$ itself) and confirms that the only
submonoid with all $6$ elements is $H(S_3)$ itself; `lean4/Main.lean` checks
all $64$ subsets by bitmask and proves that none is a proper covering
submonoid. Hence
$$\boxed{\ \operatorname{cov}(H(S_3))=2\ }.$$

This finite-type $0$-Hecke monoid therefore has finite covering number, and the
conjecture's first clause is false.

## $H(S_4)$ and the general rank-$\ge 2$ theorem

`reproduce.py` builds $H(S_4)$ ($24$ elements), verifies the monoid axioms over
all $24^3=13824$ triples, enumerates **all** submonoids ($10577$, including the
full monoid), and computes the covering number: it is exactly $2$. For every
generator $s_i$ ($i=1,2,3$) the pair $A=\{e,s_i\}$, $B=H(S_4)\setminus\{s_i\}$
is a valid $2$-cover.

**Theorem.** Let $(W,S)$ be a finite Coxeter system of rank $|S|\ge 2$. Then
$\operatorname{cov}(H(W))=2$.

*Proof sketch.* Fix $s\in S$ and set $A=\{e,s\}$, $B=H(W)\setminus\{s\}$.

- $A$ is a submonoid because $s\star s=s$.
- $B$ is a submonoid. Suppose $x,y\in B$ and $x\star y=s$. The **length
  identity**
  $$\ell(x\star y)\ge\max(\ell(x),\ell(y))\qquad\text{for all }x,y\in W$$
  gives $1=\ell(s)\ge\max(\ell(x),\ell(y))$, so $\ell(x),\ell(y)\le 1$, i.e.
  $x,y\in\{e\}\cup S$; since $x,y\ne s$ we get
  $x,y\in\{e\}\cup(S\setminus\{s\})$. If $x=e$ then $x\star y=y\ne s$, and if
  $y=e$ then $x\star y=x\ne s$. Otherwise $x,y\in S\setminus\{s\}$: if $x=y$
  then $x\star y=x\ne s$, and if $x\ne y$ then $x\star y$ is a product of two
  distinct simple reflections, of length $2>1=\ell(s)$. So $x\star y\ne s$,
  hence $x\star y\in B$.
- Both are proper: $A$ is proper because $|S|\ge 2$ gives some
  $t\in S\setminus\{s\}$; $B$ is proper because $s\notin B$.
- $A\cup B=H(W)$ since $s\in A$ and all other elements lie in $B$.

So $\operatorname{cov}(H(W))\le 2$, and $\ge 2$ because a proper submonoid
never covers. Hence $\operatorname{cov}(H(W))=2$. $\square$

The length identity follows from the subword description of the Demazure
product ($x\star y$ is the longest element that is a subword of both a reduced
word of $x$ and one of $y$, hence dominates both $x$ and $y$ in Bruhat order,
so its length is at least the larger length). It is verified exhaustively for
$S_3,S_4,S_5$ --- all $6^2,24^2,120^2$ pairs, $0$ violations --- by
`reproduce.py`.

**Only ranks $\le 1$ differ.** For the trivial $W=\{e\}$ (rank $0$),
$H(W)=\{e\}$ has no proper submonoid, so its covering number is $\infty$. For
$W=S_2$ (rank $1$), $H(W)=\{e,s\}$ has the single proper submonoid $\{e\}$,
which does not cover, so again the covering number is $\infty$ (verified by the
script). Thus the conjecture's first clause fails for essentially the entire
class, not merely in one spot.

## The direct-product clause also fails

**Proposition.** For monoids $M_1,M_2$,
$\operatorname{cov}(M_1\times M_2)\le \operatorname{cov}(M_1)\operatorname{cov}(M_2)$.

*Proof.* If $M_1=A_1\cup\cdots\cup A_p$ and $M_2=B_1\cup\cdots\cup B_q$ with
proper submonoids, then
$M_1\times M_2=\bigcup_{i,j}A_i\times B_j$. Each $A_i\times B_j$ is a
submonoid (closed componentwise, contains the identity) and is proper (pick
$a\in M_1\setminus A_i$, $b\in B_j$; then $(a,b)\notin A_i\times B_j$). Hence
the $pq$ products cover. $\square$

Consequently
$$\operatorname{cov}(H(S_3)\times H(S_3))\le 2\cdot 2=4<\infty,$$
so the conjecture's third clause is false. `reproduce.py` constructs the four
proper submonoids $A\times A$, $A\times B$, $B\times A$, $B\times B$ of the
$36$-element product explicitly, verifies closure and properness of each, and
verifies that their union is the whole product.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definition, table, cover, general theorem, product clause, files, repro, rule status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): builds $H(S_n)$ for $n=2,3,4$, checks the monoid axioms, enumerates all submonoids, computes the exact covering number, checks the length identity for $S_3,S_4,S_5$, checks the product bound on $H(S_3)\times H(S_3)$; `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only with **no imports at all**, no `sorry`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in a few seconds):

```sh
python3 reproduce.py
```

It prints `PASS: conjecture 00000003844 is FALSE.` and exits `0` on success; it
exits non-zero if any check fails. It recomputes, from scratch, the Demazure
product on permutations of $S_n$, the monoid axioms, all submonoids, the exact
covering numbers, the length identity, and the direct-product bound.

LaTeX document:

```sh
tectonic --outdir build main.tex
```

produces `build/main.pdf` (non-empty).

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem
and reports only `propext` (with `A_proper`, `B_proper`, `cover` depending on no
axioms at all); no `sorryAx` appears.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** --- present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** --- present at `build/main.pdf`.
- **Lean 4 project** --- present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (library `Main`), `Main.lean`,
  `Check.lean`, and a `README.md`. It formalises the counterexample
  $\operatorname{cov}(H(S_3))=2$ (`covering_number_is_two`) and hence
  `conjecture_00000003844_false`, using **no imports**, no Mathlib, and no
  `sorry`; the audit reports no `sorryAx` and only `propext`.
