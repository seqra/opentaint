#!/usr/bin/env sh
MODEL=$1; MOD=$2
[ -n "$MODEL" ] && [ -n "$MOD" ] || { echo "usage: package-usages.sh <model-dir> <module-path>" >&2; exit 2; }

dirs=$(awk '/^goProjects:/{g=1;next} g&&/^[^[:space:]-]/{g=0} g&&/projectDir:/{sub(/^[^:]*:[[:space:]]*/,"");print}' "$MODEL/project.yaml" 2>/dev/null)
[ -n "$dirs" ] || dirs=$MODEL
tab=$(printf '\t')

for d in $dirs; do
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
        [ -n "$id" ] || id=$(cd "$d" 2>/dev/null && go list -f '{{.Name}}' "$path" 2>/dev/null)
        [ -n "$id" ] || id=$(basename "$path")
        grep -oE "\b$id\.[A-Z][A-Za-z0-9_]*" "$f" | awk -v p="$path" -F. '{print p"."$NF}'
      done
  done
done | sort -u
