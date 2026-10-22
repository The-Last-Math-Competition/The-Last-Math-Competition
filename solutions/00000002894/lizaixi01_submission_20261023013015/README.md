# Counterexample for 00000002894

In the genuine projective plane PG(2,9), take the three coordinate sides with their three vertices removed. There are 24 points. Every nonzero homogeneous linear form meets the set; each point has an explicit tangent meeting it alone, proving inclusion-minimality. Every line also has a point outside the set. A line has at most 10 points, so at least 14 of these 24 points lie outside it, whereas a Redei line would leave exactly 9. This is therefore a nontrivial minimal non-Redei blocking set with plane order 9=3^2 and non-square parameter 3.

Minimal means inclusion-minimal, not minimum-cardinality. No smallness hypothesis appears in the original English conjecture. The standard definitions and Redei necessary condition are given in [Gacs--Lovasz--Szonyi, Directions in AG(2,p^2), printed page 191](https://msp.org/iig/2008/6-1/iig-v6-n1-p12-p.pdf). The further classification clause cannot repair the false necessary assertions.

Lean uses Mathlib Projectivization of F9^3 and kernels of all nonzero coordinate linear forms, proves their dimension is 2, and bounds their actual projective point counts. The set is an injective image of three explicit unit-parameter families; no abstract incidence answer or computed threshold is assumed. Complete source/report/PDF and source-bound verification receipts are included.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new Main build, sixteen transitive axiom audits, and full official leanchecker --fresh Main replay are required. No sorry, native_decide, or added axiom is used. OpenAI Codex assisted; a separate supervising Codex agent reviewed the source, report and PDF. This is AI review, not human certification. Organizer acceptance is pending.
