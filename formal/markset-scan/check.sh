#!/usr/bin/env bash
# Builds the model and fails if any declaration depends on an axiom other than
# propext / Quot.sound (no Classical.choice, no sorryAx).
set -euo pipefail
cd "$(dirname "$0")"
lake build
grep -rn --include=*.lean -E '\bsorry\b|\badmit\b|native_decide|^axiom ' MarkScan && { echo "forbidden construct"; exit 1; } || true
out=$(lake env lean AxiomAudit.lean)
echo "$out" | grep -E 'Classical|sorryAx|Lean.ofReduceBool' && { echo "non-constructive axiom found"; exit 1; } || true
echo "$out" | grep -c "depends on axioms\|does not depend" | xargs echo "audited declarations:"
