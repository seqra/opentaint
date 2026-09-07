#!/usr/bin/env bash
# Resolves the source file a Lean file mirrors, per the mapping law in README.md.
#
#   Lean  formal/Opentaint/<Seg>/<Base>.lean
#     Go      <seg>/<base_in_snake_case>.go        (paths are lowercase, files snake_case)
#     Kotlin  core/**/org/opentaint/<seg>/<Base>.kt
#
# Prints the repo-relative path of the counterpart, or nothing.  Sourced by check-map.sh
# and gen-map.sh so the two cannot disagree about what the law says.

counterpart_for() {
  local rel="$1" repo_root="$2"
  local dir base lower_dir snake hit

  dir="$(dirname "$rel")"
  base="$(basename "$rel" .lean)"
  [[ "$dir" == "." ]] && dir=""

  lower_dir="$(tr '[:upper:]' '[:lower:]' <<<"$dir")"
  snake="$(sed 's/\([a-z0-9]\)\([A-Z]\)/\1_\2/g' <<<"$base" | tr '[:upper:]' '[:lower:]')"

  if [[ -n "$lower_dir" && -f "$repo_root/$lower_dir/$snake.go" ]]; then
    echo "$lower_dir/$snake.go"
    return
  fi

  local pkg="org/opentaint${lower_dir:+/$lower_dir}"
  hit="$(find "$repo_root/core" -path "*/$pkg/$base.kt" -not -path '*/bin/*' -print -quit 2>/dev/null)"
  [[ -n "$hit" ]] && echo "${hit#"$repo_root"/}"
}
