# Verification evidence

The independent review and its final Lean and LaTeX build logs are in `independent/`. `Audit.lean` imports the root RankGap module and audits every authored theorem. Run from the root after `lake build` with `lake env lean verification/independent/Audit.lean`.

The optional independent arithmetic script requires Python 3 and SymPy. It was run using existing installed software. It is supplementary cross-checking, not a dependency of the Lean proof. Run `python3 verification/independent/independent_check.py`.

The rank proof and its ordinary Lean-kernel replay require only the pinned Lean 4.31.0 standard library. No custom axioms or native decision shortcuts are used.
