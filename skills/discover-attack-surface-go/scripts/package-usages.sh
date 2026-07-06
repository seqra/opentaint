#!/usr/bin/env sh
MODEL=$1; MOD=$2
[ -n "$MODEL" ] && [ -n "$MOD" ] || { echo "usage: package-usages.sh <model-dir> <module-path>" >&2; exit 2; }

dirs=$(awk '/^goProjects:/{g=1;next} g&&/^[^[:space:]-]/{g=0} g&&/projectDir:/{sub(/^[^:]*:[[:space:]]*/,"");print}' "$MODEL/project.yaml" 2>/dev/null)
[ -n "$dirs" ] || dirs=$MODEL
tab=$(printf '\t')
CACHE=$(mktemp) || exit 1
trap 'rm -f "$CACHE"' EXIT

printf '%s\n' "$dirs" | while IFS= read -r d; do
  [ -n "$d" ] || continue
  [ -d "$d" ] || d="$MODEL/$d"
  grep -rlF --include='*.go' "\"$MOD" "$d" 2>/dev/null | while IFS= read -r f; do
    awk -v mod="$MOD" '
      /^import[[:space:]]*\(/{blk=1;next}
      blk&&/^\)/{blk=0;next}
      (blk||/^import[[:space:]]/)&&match($0,/"[^"]+"/){
        path=substr($0,RSTART+1,RLENGTH-2)
        if(path==mod||index(path,mod"/")==1){
          name=substr($0,1,RSTART-1); gsub(/[[:space:]]/,"",name); sub(/^import/,"",name)
          print path"\t"name}}' "$f" \
    | while IFS="$tab" read -r path id; do
        case $id in .|_) continue;; esac
        if [ -z "$id" ]; then
          id=$(awk -v p="$path" '$1==p{print $2;exit}' "$CACHE")
          if [ -z "$id" ]; then
            id=$(cd "$d" 2>/dev/null && go list -f '{{.Name}}' "$path" 2>/dev/null)
            [ -n "$id" ] || id=$(basename "$path")
            printf '%s %s\n' "$path" "$id" >>"$CACHE"
          fi
        fi
        esc=$(printf '%s' "$id" | sed 's/[^A-Za-z0-9_]/\\&/g')
        grep -oE "\b$esc\.[A-Z][A-Za-z0-9_]*" "$f" | awk -v p="$path" -F. '{print p"."$NF}'
      done
  done
done | sort -u
