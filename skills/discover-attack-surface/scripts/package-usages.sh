#!/usr/bin/env bash
# package-usages.sh <model-dir> <package>
#
# Print the distinct methods of dependency <package> that the project's OWN
# compiled classes call. Scans every moduleClasses entry in <model-dir>/project.yaml
# (class dirs or jars) and keeps only call sites whose owner is in <package>,
# deduped. A model's moduleClasses can mix project + dependency jars, so when the
# modules carry a `packages:` list, only classes under those roots are scanned;
# when there's no `packages:` list, moduleClasses is already project-only. The
# separate `dependencies:` list is never touched.
MODEL=$1; PKG=$2
[ -n "$MODEL" ] && [ -n "$PKG" ] || { echo "usage: package-usages.sh <model-dir> <package>" >&2; exit 2; }
pp=${PKG//.//}

# read a YAML block list — the "- item" lines under <key>:
ylist(){ awk -v k="$1" '$0~"^[[:space:]]*"k":[[:space:]]*$"{f=1;next} f&&/^[[:space:]]*-[[:space:]]/&&$0!~/:/{sub(/^[^-]*-[[:space:]]*/,"");print;next} f&&/:/{f=0}' "$MODEL/project.yaml"; }

roots=$(ylist packages | tr . / | paste -sd'|' -)   # project roots; empty ⇒ scan all moduleClasses
ylist moduleClasses | while IFS= read -r e; do
  p="$MODEL/$e"
  { if [ -d "$p" ]; then (cd "$p" && find . -name '*.class' | sed 's#^\./##'); else jar tf "$p" | grep '\.class$'; fi; } \
    | { [ -n "$roots" ] && grep -E "^($roots)/" || cat; } \
    | sed 's#\.class$##; s#/#.#g' | xargs -r javap -c -p -classpath "$p" 2>/dev/null
done | grep -oE '// (Interface)?Method '"$pp"'/[^ ]+' | sort -u
