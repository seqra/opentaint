#!/usr/bin/env bash
set -euo pipefail

# Assemble npm packages from GoReleaser "full" archives.
#
# Usage: build-npm-packages.sh <dist-dir> <version>
#
# Produces ready-to-publish package directories under cli/dist-npm/
# (override with OPENTAINT_NPM_OUT_DIR). Requires: tar, unzip, python3.

DIST_DIR="${1:?Usage: $0 <dist-dir> <version>}"
VERSION="${2:?Usage: $0 <dist-dir> <version>}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NPM_SRC="$(cd "$SCRIPT_DIR/../npm" && pwd)"
OUT_DIR="${OPENTAINT_NPM_OUT_DIR:-$(cd "$SCRIPT_DIR/.." && pwd)/dist-npm}"
SCOPE="@seqra"

# goreleaser_platform  npm_suffix  npm_os  npm_cpu  ext     binary
PLATFORMS=(
  "linux_amd64    linux-x64     linux   x64    tar.gz  opentaint"
  "linux_arm64    linux-arm64   linux   arm64  tar.gz  opentaint"
  "darwin_amd64   darwin-x64    darwin  x64    tar.gz  opentaint"
  "darwin_arm64   darwin-arm64  darwin  arm64  tar.gz  opentaint"
  "windows_amd64  win32-x64     win32   x64    zip     opentaint.exe"
  "windows_arm64  win32-arm64   win32   arm64  zip     opentaint.exe"
)

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

# Collect "name=version" pairs for the main package's optionalDependencies.
DEPS=()

for entry in "${PLATFORMS[@]}"; do
  read -r gr_plat npm_suffix npm_os npm_cpu ext _bin <<< "$entry"
  archive="$DIST_DIR/opentaint-full_${gr_plat}.${ext}"
  if [ ! -f "$archive" ]; then
    echo "WARNING: archive not found, skipping: $archive" >&2
    continue
  fi

  pkg_name="${SCOPE}/opentaint-${npm_suffix}"
  pkg_dir="$OUT_DIR/opentaint-${npm_suffix}"
  mkdir -p "$pkg_dir"

  echo "Assembling ${pkg_name} from $(basename "$archive")"
  if [ "$ext" = "zip" ]; then
    unzip -q "$archive" -d "$pkg_dir"
  else
    tar -xzf "$archive" -C "$pkg_dir"
  fi

  if [ ! -e "$pkg_dir/$_bin" ]; then
    echo "ERROR: expected binary '$_bin' not found after extracting $archive" >&2
    exit 1
  fi

  NAME="$pkg_name" VERSION="$VERSION" OS="$npm_os" CPU="$npm_cpu" \
  python3 - "$NPM_SRC/platform.tmpl.json" "$pkg_dir/package.json" <<'PY'
import json, os, sys
tmpl, out = sys.argv[1], sys.argv[2]
with open(tmpl) as f:
    pkg = json.load(f)
pkg["name"] = os.environ["NAME"]
pkg["version"] = os.environ["VERSION"]
pkg["os"] = [os.environ["OS"]]
pkg["cpu"] = [os.environ["CPU"]]
with open(out, "w") as f:
    json.dump(pkg, f, indent=2)
    f.write("\n")
PY

  DEPS+=("${pkg_name}=${VERSION}")
done

if [ "${#DEPS[@]}" -eq 0 ]; then
  echo "ERROR: no platform archives found in $DIST_DIR" >&2
  exit 1
fi

# Assemble the main package.
main_dir="$OUT_DIR/opentaint"
mkdir -p "$main_dir/bin"
cp "$NPM_SRC/bin/opentaint.js" "$main_dir/bin/opentaint.js"
chmod +x "$main_dir/bin/opentaint.js"

VERSION="$VERSION" DEPS="${DEPS[*]}" \
python3 - "$NPM_SRC/package.tmpl.json" "$main_dir/package.json" <<'PY'
import json, os, sys
tmpl, out = sys.argv[1], sys.argv[2]
with open(tmpl) as f:
    pkg = json.load(f)
pkg["version"] = os.environ["VERSION"]
deps = {}
for pair in os.environ["DEPS"].split():
    name, ver = pair.rsplit("=", 1)
    deps[name] = ver
pkg["optionalDependencies"] = deps
with open(out, "w") as f:
    json.dump(pkg, f, indent=2)
    f.write("\n")
PY

echo "npm packages assembled in $OUT_DIR"
ls -1 "$OUT_DIR"
