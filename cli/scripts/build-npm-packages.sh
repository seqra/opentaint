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

  python3 "$SCRIPT_DIR/render-package-json.py" \
    --template "$NPM_SRC/platform.tmpl.json" --out "$pkg_dir/package.json" \
    --name "$pkg_name" --version "$VERSION" --os "$npm_os" --cpu "$npm_cpu"

  DEPS+=("${pkg_name}=${VERSION}")
done

if [ "${#DEPS[@]}" -eq 0 ]; then
  echo "ERROR: no platform archives found in $DIST_DIR" >&2
  exit 1
fi

main_dir="$OUT_DIR/opentaint"
mkdir -p "$main_dir/bin"
cp "$NPM_SRC/bin/opentaint.js" "$main_dir/bin/opentaint.js"
chmod +x "$main_dir/bin/opentaint.js"
cp "$NPM_SRC/README.md" "$main_dir/README.md"

dep_args=()
for dep in "${DEPS[@]}"; do
  dep_args+=(--optional-dep "$dep")
done

python3 "$SCRIPT_DIR/render-package-json.py" \
  --template "$NPM_SRC/package.tmpl.json" --out "$main_dir/package.json" \
  --version "$VERSION" "${dep_args[@]}"

echo "npm packages assembled in $OUT_DIR"
ls -1 "$OUT_DIR"
