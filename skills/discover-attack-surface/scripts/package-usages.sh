#!/usr/bin/env bash
MODEL=$1; PKG=$2
[ -n "$MODEL" ] && [ -n "$PKG" ] || { echo "usage: package-usages.sh <model-dir> <package>" >&2; exit 2; }
pp=${PKG//.//}

ylist(){ awk -v k="$1" '$0~"^[[:space:]]*"k":[[:space:]]*$"{f=1;next} f&&/^[[:space:]]*-[[:space:]]/&&$0!~/:/{sub(/^[^-]*-[[:space:]]*/,"");print;next} f&&/:/{f=0}' "$MODEL/project.yaml"; }

roots=$(ylist packages | tr . / | paste -sd'|' -)
ylist moduleClasses | while IFS= read -r e; do
  p="$MODEL/$e"
  { if [ -d "$p" ]; then (cd "$p" && find . -name '*.class' | sed 's#^\./##'); else jar tf "$p" | grep '\.class$'; fi; } \
    | { [ -n "$roots" ] && grep -E "^($roots)/" || cat; } \
    | sed 's#\.class$##; s#/#.#g' | xargs -r javap -c -p -classpath "$p" 2>/dev/null
done | grep -oE '// (Interface)?Method '"$pp"'/[^ ]+' | sort -u
