# Engineering evidence

RESULT.json is the concise result. final-run/verification.json is the complete successful machine-readable result. The two bootstrap folders preserve original failed command logs and their exact source snapshots. No failure log was overwritten or relabeled as success.

Every command has a timestamped JSON receipt plus original stdout and stderr. The receipt records the arguments, working directory, selected environment, exit status, and SHA-256 of each stream. Recorded absolute paths identify the original scratch run; locate the corresponding file here by its same basename. JSON files ending in .gz are lossless gzip copies of complete audit/dependency graphs and can be inspected with gzip -cd. Source snapshots and generated control sources are tar.gz archives; they contain source only, no compiled artifacts.

All mathematical declarations were selected by originating module, including private and generated proof declarations. The successful mathematical audit covers 47 safe roots and 15,665 reachable declarations. The full 53-root inventory also explicitly records six compiler-generated unsafe runtime entries; none is reachable from a mathematical root. Infrastructure has its own separate inventory.

The first bootstrap failed because its newly added verification library root import was missing. The second bootstrap deliberately enforced the all-roots audit on compiler-generated runtime entries and rejected them; every mathematical root already passed. The final run uses the reviewed exact six-entry runtime list and the source guard against authored unsafe definitions.

The original verify.sh and the independent verify.py both executed successfully. Negative controls intentionally produce rejection exits for admission, custom axiom, native decision, unsafe root, unsafe proof use, frozen mutation, and unlisted module. No mathematical computation scripts are required.

The report has two parent-approved layout-only changes after the author freeze; all mathematical Lean source bytes remain identical. input-and-source-integrity.json records the exact input and source changes. The original author report hash and provenance remain under provenance/.
