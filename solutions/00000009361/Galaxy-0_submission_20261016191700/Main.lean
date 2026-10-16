import RecordsCount

/-!
TLMC 00000009361: exact record-pattern counts for actual permutations.

The principal entry points, all in namespace Records9361, are:
* chronologicalPerms_complete, chronologicalPerms_nodup;
* chronologicalRecords (an independent left-to-right comparison scan);
* chronologicalPatternCount_exact;
* independent_bernoulli_joint_law.

The probability theorem uses the exact uniform measure on the duplicate-free
finite permutation enumeration. Positional exchangeability implies this
uniform measure by transitivity; that elementary probability argument is in
main.pdf, and is not claimed as a Lean theorem about a probability library.
-/
