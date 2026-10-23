# Sources actually inspected

Checked 2026-10-23 UTC.

- Original problem: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/b355e42906e6eaf52bc7e9d005e0ef02d8aa7400/conjectures/00000007978.md . The source specifies server count t but no K=2 restriction. Verbatim original retained in source-conjecture.md.
- Hua Sun and Syed Ali Jafar, The Capacity of Private Information Retrieval. Author-hosted manuscript https://newport.eecs.uci.edu/~syed/papers/j75.pdf ; arXiv https://arxiv.org/abs/1602.09134 ; IEEE Transactions on Information Theory 63(7),4075–4088, July2017, DOI10.1109/TIT.2017.2689028. Actually read Section II equations(3)–(9), Section III Theorem1 and its discussion, and Section V converse. Section II defines expected download and vanishing-error capacity; Theorem1 identifies both zero-error and vanishing-error capacities. The proof paper cites this known theorem rather than claiming a new capacity discovery.
- Lean source library used locally: Lean4.31.0 standard library; no Mathlib or external package dependency. List.perm_iff_count is used in the finite coupling proof; all instantiated declarations were kernel-checked by Lean.

Publication qualification, all-state duplicate search, and score/acceptance status are checked separately by the submitting coordinator. A compiled Lean file or a draft PR is not an accepted or scored solution.
