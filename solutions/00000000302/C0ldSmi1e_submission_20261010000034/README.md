# Proof of conjecture 00000000302

Both Hausdorff dimensions in the conjecture equal **1**. More generally, for each real α > 0 the set II_α has full Lebesgue measure, and the intersection II_α ∩ II_β has Hausdorff dimension one whenever α, β > 0.

The original English and Chinese text leaves the domains and quantifiers on p and q implicit. The formalization states the conventional meaning explicitly: x is real, p ranges over every integer, q ranges over every positive natural number, and one positive real constant works uniformly for all p and q. The inequality is strict; real powers, all unreduced fractions, the full real line, and Mathlib's actual metric Hausdorff dimension are used.

`ORIGINAL.md` is the byte-exact bilingual statement. `proof.tex` and the matching two-page `proof.pdf` give the complete argument. The complete Lean project is in `lean/`. Independent semantic review and compiler/audit evidence are in `verification/`; the verification summary distinguishes local checks from maintainer acceptance. No auxiliary numerical calculation is required.

## Reproduce the complete verification

Run `python3 lean/verify.py` with Python 3.9 or later, Git, and the pinned Lean/Lake toolchain available on PATH. This creates a fresh temporary project, fetches/builds the pinned stock dependencies, rebuilds the submitted proof, replays all five Lean sources with warnings as errors, exports and checks the complete dependency graph, and runs six rejection controls. It writes `verification.json` and full command receipts in the printed work directory. Building all stock dependencies can take substantial time.

To reuse a local stock Mathlib checkout/cache, pass `--stock-mathlib /path/to/mathlib`; it must include the pinned transitive package checkouts under `.lake/packages`. The verifier copies and validates the stock sources and reuses their compiled cache, while always rebuilding the submitted project. An explicit toolchain directory can be passed with `--lean-bin /path/to/lean/bin`, and `--work-dir /new/empty/path` chooses an output directory that must not exist.

The successful final packaged run and complete raw evidence are described in `VERIFICATION.md`. Invalid control examples are generated only in temporary scratch directories; they are never imported by the proof.

## Reproduce the proof alone

Use the checked-in Lean toolchain and Lake manifest without updating their versions. They pin Lean 4.19.0, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and all eight transitive dependencies.

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture302.lean
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true lakefile.lean
```

The cache command is optional; building the pinned stock dependencies from source is also valid. The project itself must be rebuilt, rather than reusing someone else's project build products. The default build target includes both the proof and its theorem-type/axiom audit. The final theorem is `Conjecture302.conjecture`; its type is the original equality, without extra hypotheses. Its seven audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

The LaTeX report uses standard `article`, `geometry`, AMS mathematics, `mathtools`, `fontenc`, `lmodern`, and `hyperref` packages. It can be compiled with Tectonic or a standard LaTeX installation. The provided PDF was also compiled in the desktop editor and every page was visually inspected.

Prepared by C0ldSmi1e with Codex assistance. The mathematical author, semantic reviewer, and engineering reviewer used separate agent contexts. These are internal model checks, not an external human review or maintainer acceptance.
