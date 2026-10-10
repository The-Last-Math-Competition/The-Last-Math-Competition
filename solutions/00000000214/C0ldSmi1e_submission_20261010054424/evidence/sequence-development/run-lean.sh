#!/bin/zsh
set -u
cd /private/tmp/tlmc214-sequence
seq_source="$1"
seq_run="$2"
seq_mathlib=/private/tmp/tlmc-standard-library-419/mathlib
export LEAN_PATH="$seq_mathlib/.lake/build/lib/lean:$seq_mathlib/.lake/packages/Cli/.lake/build/lib/lean:$seq_mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$seq_mathlib/.lake/packages/Qq/.lake/build/lib/lean:$seq_mathlib/.lake/packages/aesop/.lake/build/lib/lean:$seq_mathlib/.lake/packages/batteries/.lake/build/lib/lean:$seq_mathlib/.lake/packages/importGraph/.lake/build/lib/lean:$seq_mathlib/.lake/packages/plausible/.lake/build/lib/lean:$seq_mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean"
seq_stdout="compile-${seq_run}.stdout"
seq_stderr="compile-${seq_run}.stderr"
seq_exit="compile-${seq_run}.exit"
if [[ -e "$seq_stdout" || -e "$seq_stderr" || -e "$seq_exit" ]]; then
  print -u2 'Refusing to overwrite earlier logs.'
  exit 99
fi
/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lean "$seq_source" > "$seq_stdout" 2> "$seq_stderr"
seq_code=$?
print -r -- "$seq_code" > "$seq_exit"
cat "$seq_stdout" "$seq_stderr"
exit "$seq_code"
