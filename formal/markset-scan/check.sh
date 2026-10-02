#!/usr/bin/env bash
# Builds the model and fails if any theorem depends on an axiom other than
# propext / Quot.sound (no Classical.choice, no sorryAx, no native_decide).
set -euo pipefail
cd "$(dirname "$0")"
lake build
if grep -rn --include=*.lean -E '\bsorry\b|\badmit\b|native_decide|^axiom ' MarkScan; then
  echo "forbidden construct"; exit 1
fi
./gen_audit.py
out=$(lake env lean AxiomAudit.lean)
if echo "$out" | grep -E 'Classical|sorryAx|ofReduceBool'; then
  echo "non-constructive axiom found"; exit 1
fi
echo "$out" | sed -E 's/.*depends on axioms: (.*)/\1/; s/.*does not depend.*/none/' | sort | uniq -c
