ARCHIVAL ONLY: none of these files is a Lean build root or imported.
Definitions.attempt01.txt preserves the first source rejected for an unused binder.
Challenges.attempt01.txt preserves elaboration/linter errors before correction.
Definitions.freeze01.txt and Challenges.freeze01.txt preserve the first mathematical freeze.
Definitions.noncomputable-section.txt and Challenges.noncomputable-section.txt preserve the unsuccessful section-only code-generation suppression attempt.
Audit.attempt01.txt preserves a Name-quotation error.
Audit.attempt02.txt is the full auditor that detected generated compiler intermediates using lcProof; its code remains the final auditor after the Name correction.
MATH_FROZEN.first.json.txt binds the original freeze, superseded only by explicit noncomputability annotations.
Corresponding logs are retained under evidence/. The first warning appeared in the tool transcript; its exact diagnostic was: Definitions.lean:19:16 unused variable G, treated as an error by warningAsError.
