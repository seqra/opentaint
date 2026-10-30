#!/usr/bin/env bash
set -euo pipefail

# Bundle the platform-specific go-ssa-server binary into the release archives.
# The script runs after GoReleaser. It puts the binary into the lib/ directory
# of the "opentaint" and "opentaint-full" archives, next to the analyzer, the
# autobuilder, and the rules. This is the analogue of bundle-jre.sh, which
# injects the platform-specific JREs.
#
# Usage: ./scripts/bundle-go-server.sh <dist-dir> [github-repo]
#
# Prerequisites: gh (authenticated), tar, unzip, zip

DIST_DIR="${1:?Usage: $0 <dist-dir> [github-repo]}"
REPO="${2:-seqra/opentaint}"
VERSIONS_FILE="internal/globals/versions.yaml"

GO_SERVER_TAG=$(grep '^go-server:' "$VERSIONS_FILE" | awk '{print $2}' | tr -d '"')
echo "go-ssa-server version: $GO_SERVER_TAG"

# The release assets are named "go-ssa-server_<goos>_<goarch>", with ".exe" on
# windows. The platform list matches the GoReleaser build matrix.
PLATFORMS=(linux_amd64 linux_arm64 darwin_amd64 darwin_arm64 windows_amd64 windows_arm64)

inject_tar_gz() {
    local archive="$1"
    local binary="$2"
    local tmp_dir

    tmp_dir=$(mktemp -d)
    trap 'rm -rf "$tmp_dir"' RETURN

    echo "  Extracting archive..."
    tar -xzf "$archive" -C "$tmp_dir"

    mkdir -p "$tmp_dir/lib"
    cp "$binary" "$tmp_dir/lib/$(basename "$binary")"
    # The binary must be executable when the archive is unpacked on unix.
    chmod 0755 "$tmp_dir/lib/$(basename "$binary")"

    echo "  Recompressing archive..."
    tar -czf "$archive" -C "$tmp_dir" .
}

inject_zip() {
    local archive
    archive="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
    local binary="$2"
    local tmp_dir

    tmp_dir=$(mktemp -d)
    trap 'rm -rf "$tmp_dir"' RETURN

    echo "  Extracting archive..."
    unzip -q "$archive" -d "$tmp_dir"

    mkdir -p "$tmp_dir/lib"
    cp "$binary" "$tmp_dir/lib/$(basename "$binary")"

    echo "  Recompressing archive..."
    (cd "$tmp_dir" && zip -qr "$archive" .)
}

for platform in "${PLATFORMS[@]}"; do
    asset="go-ssa-server_${platform}"
    if [[ "$platform" == windows_* ]]; then
        asset="${asset}.exe"
        archive_ext="zip"
    else
        archive_ext="tar.gz"
    fi

    echo "Processing platform: $platform"

    asset_dir=$(mktemp -d)
    echo "  Downloading $asset..."
    gh release download "$GO_SERVER_TAG" \
        --repo "$REPO" \
        --pattern "$asset" \
        --dir "$asset_dir"

    for variant in opentaint opentaint-full; do
        archive_file="$DIST_DIR/${variant}_${platform}.${archive_ext}"
        if [ ! -f "$archive_file" ]; then
            echo "  Archive not found: $archive_file, skipping"
            continue
        fi
        if [ "$archive_ext" = "zip" ]; then
            inject_zip "$archive_file" "$asset_dir/$asset"
        else
            inject_tar_gz "$archive_file" "$asset_dir/$asset"
        fi
        echo "  Done: $archive_file"
    done

    rm -rf "$asset_dir"
done

echo "go-ssa-server bundling complete."
