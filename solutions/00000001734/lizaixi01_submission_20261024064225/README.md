# TLMC 00000001734: infinitely many integral figure-eight characters

The source asserts finiteness for the full SL2 character variety of a fibered hyperbolic 3-manifold group, with no irreducibility, canonical-component or fixed-boundary restriction. The example uses the published figure-eight exterior and its precise presentation t*a*t^-1=a*b, t*b*t^-1=b*a*b.

Lean constructs the native PresentedGroup, actual SL2(Z) homomorphisms with a=b=I and t=[[n+3,-1],[1,0]], and their complex scalar extensions. It proves integer trace for every group element, distinct full character functions, conjugation invariance, and infinitely many such integral characters. The actual coordinates (trace(a),trace(b),trace(t))=(2,2,n+3) are also realized in the published three-variable polynomial model, whose integer zero locus is explicitly defined and proved to equal the stated union of components.

The report cites Heusener-Munoz-Porti and Porti for the standard geometric/group/character-variety identifications. Lean does not reprove 3-manifold topology, hyperbolicity or general GIT. The abelian-component family only refutes the unrestricted full-variety finiteness clause. It does not refute irreducible/canonical or fixed-boundary variants and does not define the source's Hitchin trace-field phrase.

The complete project pins Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Run lean/verify.sh. Included evidence covers actual build, complete-namespace ordinary axiom inspection and official fresh-kernel replay. No sorry, additional axiom or native_decide. Production timings are not controlled efficiency samples. Organizer acceptance is pending.
