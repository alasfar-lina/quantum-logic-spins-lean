#!/usr/bin/env bash
# Each mutant is a deliberately FALSE claim. The check passes only if Lean
# reports an error located inside the mutant file itself (not a build failure).
set -u
cd "$(dirname "$0")/.."
status=0
for f in mutants/Mutant*.lean; do
  out=$(lake env lean "$f" 2>&1)
  if echo "$out" | grep -qE "$(basename "$f"):[0-9]+:[0-9]+: error"; then
    echo "rejected as expected: $f"
  else
    echo "NOT rejected: $f"; echo "$out" | head -20; status=1
  fi
done
exit $status
