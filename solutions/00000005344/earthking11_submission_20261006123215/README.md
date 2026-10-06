# Disproof of conjecture `00000005344`

**Verdict: false.** Ordinary categories embed as strict bicategories having
only identity 2-morphisms, and horizontal composition of 1-morphisms is then
ordinary morphism composition.  That composition need not commute.

In the category of sets, consider the Boolean endomorphisms

```text
f(x) = false
g(x) = not x.
```

Then

```text
(f ∘ g)(false) = false,
(g ∘ f)(false) = true.
```

So `f ∘ g != g ∘ f`.  Viewing this category as a locally discrete strict
bicategory gives a direct bicategorical counterexample to strict
commutativity.  Normalizing a scalar conversion constant cannot change this
inequality of composites.

## Formal verification

The Lean project defines composition of Boolean endomorphisms, evaluates both
orders on `false`, proves the functions unequal, and negates the universal
strict-commutativity proposition.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
