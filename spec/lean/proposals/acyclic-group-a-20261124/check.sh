#!/usr/bin/env bash
# Check the two models with Lean 4.36.0 (core only) and audit the axioms.
# Pass: no error, no `sorry`, every `#print axioms` line lists only propext and Quot.sound.
set -euo pipefail
cd "$(dirname "$0")"
status=0
for f in G6DropForm.lean MustExactCleaner.lean; do
  if ! out=$(elan run leanprover/lean4:v4.36.0 lean "$f" 2>&1); then
    echo "$out"; echo "FAIL $f: lean error"; status=1; continue
  fi
  if echo "$out" | grep -qE "error|sorry"; then echo "$out"; echo "FAIL $f: error or sorry"; status=1; continue; fi
  claims=0; bad=0
  while IFS= read -r line; do
    case "$line" in
      *"does not depend on any axioms"*) claims=$((claims+1)) ;;
      *"depends on axioms: ["*)
        claims=$((claims+1))
        list=${line#*depends on axioms: [}; list=${list%]*}
        IFS=',' read -ra names <<< "$list"
        for n in "${names[@]}"; do
          n=$(echo "$n" | tr -d ' ')
          if [[ "$n" != "propext" && "$n" != "Quot.sound" ]]; then echo "BAD AXIOM $n: $line"; bad=1; fi
        done ;;
    esac
  done <<< "$out"
  if [[ $bad -ne 0 ]]; then echo "FAIL $f: axiom outside {propext, Quot.sound}"; status=1; continue; fi
  echo "OK   $f: $claims audited claims, axioms within {propext, Quot.sound}"
done
exit $status
