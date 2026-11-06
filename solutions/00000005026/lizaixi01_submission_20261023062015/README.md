# Conjecture 00000005026: actual two-variable singleton characterization

The source custom definition of a universal sentence means a sentence characterizing one structure up to isomorphism, with no target, signature or model-class restriction. In the actual empty first-order language, exists x forall y (y=x) uses two bound variables and characterizes exactly the singleton structure, even if empty structures are permitted. A separate forall x forall y (y=x) witness covers the syntactically universal reading under explicitly nonempty models.

Mathlib's actual terms, BoundedFormula AST, Sentence.Realize and Language.Equiv are used. Semantic and model-isomorphism theorems quantify arbitrary actual empty-language interpretations; uniqueness of such interpretation data is separately proved. Unit is a genuine witness model, every satisfying model is truly isomorphic to it, and the converse is proved.

The explicit equality body uses Fin2 variable indices 1 and 0. Recursive binderCount and maximum allocated bound-context contextWidth both equal2 on the actual syntax. This sufficient certificate is not a general identity with minimal reusable variable width, and it does not use zero free-variable count for a closed sentence. The final theorem refutes the unrestricted four-variable lower-bound clause only, not some different unspecified rich target or restricted encoding problem.

The complete bilingual SOURCE.md, LaTeX/PDF, pinned Lean 4.33.0 / Mathlib, new build, all 13 theorem audits plus canonical interpretation and proof-bearing model-equivalence audits (15 targets), full official fresh-kernel replay, source-bound evidence and SHA256 manifest are included. OpenAI Codex assisted, with separate supervising AI review. Organizer acceptance is pending.
