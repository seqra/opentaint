#!/usr/bin/env bash
# Enforces the mapping law of formal/README.md.
#
#   Lean  formal/Opentaint/<Seg>/X.lean   <->   the source file X in package <seg>
#
# Four checks, all of them ratchets rather than style preferences:
#
#   1. every Lean file is either a mirror of a source file, a Support/ file, or listed in
#      LEGACY.txt (files not yet re-homed).  LEGACY.txt must shrink to empty.
#   2. LEGACY.txt names no file that has already moved -- so the ratchet cannot rust.
#   3. MAP.md is what gen-map.sh produces -- the index cannot drift from the tree.
#   4. no `sorry` / bare `admit` in tactic position; every proof is complete.  (`lake build`'s
#      "declaration uses 'sorry'" warning is the authoritative check -- this one catches a hole
#      before a full build.)
#
# The reverse direction (a source file with no model) is deliberately NOT an error: demanding a
# model for every file would make the gate unusable.  What this enforces is that nothing in
# formal/ is unattached.

set -uo pipefail

cd "$(dirname "$0")" || exit 2
repo_root="$(cd .. && pwd)"
# shellcheck source=counterpart.sh
. ./counterpart.sh
status=0

legacy_file="LEGACY.txt"
legacy="$(grep -vE '^\s*(#|$)' "$legacy_file" 2>/dev/null || true)"

# --- 1/2. mirror law, with the legacy ratchet -----------------------------------------------
seen_legacy=""
while IFS= read -r lean; do
  rel="${lean#Opentaint/}"

  if [[ "$rel" == Support/* ]]; then
    continue
  fi

  if grep -qxF "$lean" <<<"$legacy"; then
    seen_legacy+="$lean"$'\n'
    continue
  fi

  if [[ -z "$(counterpart_for "$rel" "$repo_root")" ]]; then
    echo "FAIL $lean: no source counterpart (and not in $legacy_file)"
    status=1
  fi
done < <(find Opentaint -name '*.lean' | sort)

while IFS= read -r stale; do
  [[ -z "$stale" ]] && continue
  if [[ ! -f "$stale" ]]; then
    echo "FAIL $legacy_file lists $stale, which no longer exists -- drop the line"
    status=1
  elif ! grep -qxF "$stale" <<<"$seen_legacy"; then
    echo "FAIL $legacy_file lists $stale, which is already mirrored -- drop the line"
    status=1
  fi
done <<<"$legacy"

# --- 3. the generated index is current ------------------------------------------------------
if ! ./gen-map.sh | diff -q - MAP.md > /dev/null; then
  echo "FAIL MAP.md is stale -- run ./gen-map.sh > MAP.md"
  status=1
fi

# --- 4. no holes ----------------------------------------------------------------------------
if grep -rn --include='*.lean' -E '(\bsorry\b|^[[:space:]]*admit\b)' Opentaint > /tmp/formal-sorry.$$ 2>/dev/null; then
  echo "FAIL incomplete proofs:"
  cat /tmp/formal-sorry.$$
  status=1
fi
rm -f /tmp/formal-sorry.$$

remaining="$(grep -vE '^[[:space:]]*(#|$)' "$legacy_file" 2>/dev/null | wc -l | tr -d ' ')"
if [[ $status -eq 0 ]]; then
  if [[ "$remaining" -eq 0 ]]; then
    echo "OK mapping law holds; every Lean file is mirrored"
  else
    echo "OK mapping law holds; $remaining file(s) still awaiting a home"
  fi
fi
exit $status
