#!/usr/bin/env bash
set -euo pipefail

# Smoke test for build-npm-packages.sh: assemble packages from fake "full"
# archives and assert the generated package.json metadata and file layout.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

DIST="$WORK/dist"
mkdir -p "$DIST"

# Fake linux + windows "full" archives containing a stub binary.
printf '#!/bin/sh\necho stub\n' > "$WORK/opentaint"
chmod +x "$WORK/opentaint"
tar -czf "$DIST/opentaint-full_linux_amd64.tar.gz" -C "$WORK" opentaint

printf 'MZstub\n' > "$WORK/opentaint.exe"
( cd "$WORK" && zip -q "$DIST/opentaint-full_windows_amd64.zip" opentaint.exe )

VERSION="1.2.3-test"
OUT="$WORK/dist-npm"
OPENTAINT_NPM_OUT_DIR="$OUT" bash "$SCRIPT_DIR/build-npm-packages.sh" "$DIST" "$VERSION"

fail() { echo "FAIL: $1" >&2; exit 1; }

# Linux platform package
LP="$OUT/opentaint-linux-x64"
[ -x "$LP/opentaint" ] || fail "linux binary missing or not executable"
node -e "const p=require('$LP/package.json');
  if(p.name!=='@seqra/opentaint-linux-x64')process.exit(11);
  if(p.version!=='$VERSION')process.exit(12);
  if(JSON.stringify(p.os)!=='[\"linux\"]')process.exit(13);
  if(JSON.stringify(p.cpu)!=='[\"x64\"]')process.exit(14);" \
  || fail "linux package.json metadata wrong"

# Windows platform package
WP="$OUT/opentaint-win32-x64"
[ -f "$WP/opentaint.exe" ] || fail "windows binary missing"
node -e "const p=require('$WP/package.json');
  if(JSON.stringify(p.os)!=='[\"win32\"]')process.exit(21);
  if(JSON.stringify(p.cpu)!=='[\"x64\"]')process.exit(22);" \
  || fail "windows package.json metadata wrong"

# Main package
MP="$OUT/opentaint"
[ -f "$MP/bin/opentaint.js" ] || fail "launcher missing from main package"
node -e "const p=require('$MP/package.json');
  if(p.name!=='@seqra/opentaint')process.exit(31);
  if(p.version!=='$VERSION')process.exit(32);
  const d=p.optionalDependencies||{};
  if(d['@seqra/opentaint-linux-x64']!=='$VERSION')process.exit(33);
  if(d['@seqra/opentaint-win32-x64']!=='$VERSION')process.exit(34);
  if(p.bin.opentaint!=='bin/opentaint.js')process.exit(35);" \
  || fail "main package.json metadata wrong"

echo "PASS: build-npm-packages smoke test"
