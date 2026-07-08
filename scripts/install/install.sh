#!/usr/bin/env bash
set -euo pipefail

# OpenTaint installer for Linux and macOS
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/seqra/opentaint/main/scripts/install/install.sh | bash
#   curl -fsSL .../install.sh | bash -s -- v1.2.3  # exact version ('v' optional)
#   curl -fsSL .../install.sh | bash -s -- v0       # newest v0.x.y
#   curl -fsSL .../install.sh | bash -s -- v0.2     # newest v0.2.x

REPO="${OPENTAINT_REPOSITORY:-seqra/opentaint}"
INSTALL_DIR="${OPENTAINT_INSTALL_DIR:-}"

DOWNLOADER=""
# Populated by validate_version(): one of latest|exact|major|minor.
VERSION_SELECTOR_KIND=""
# Floating selector (e.g. v0 or v0.1) when kind is major|minor; resolved later.
VERSION_SELECTOR=""

# Populates VERSION_SELECTOR_KIND, VERSION_SELECTOR, VERSION_PATH_SEGMENT and
# VERSION_TAG from the raw version argument.
# Accepts:
#   (empty)  -> latest
#   latest
#   X / vX             (floating major, resolved to newest vX.Y.Z)
#   X.Y / vX.Y         (floating minor, resolved to newest vX.Y.Z)
#   X.Y.Z / vX.Y.Z     (exact, optionally with -suffix)
# For floating selectors VERSION_PATH_SEGMENT is left empty and filled in later
# by resolve_floating_selector() once a downloader is available.
# Exits 2 on invalid input.
validate_version() {
    local raw="${1:-latest}"

    if [ "$raw" = "latest" ] || [ -z "$raw" ]; then
        VERSION_SELECTOR_KIND="latest"
        VERSION_PATH_SEGMENT="latest/download"
        VERSION_TAG="latest"
        return
    fi

    if [[ "$raw" =~ ^v?[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9._-]+)?$ ]]; then
        local normalized="${raw#v}"
        VERSION_SELECTOR_KIND="exact"
        VERSION_PATH_SEGMENT="download/v${normalized}"
        VERSION_TAG="v${normalized}"
        return
    fi

    if [[ "$raw" =~ ^v?[0-9]+\.[0-9]+$ ]]; then
        VERSION_SELECTOR_KIND="minor"
        VERSION_SELECTOR="v${raw#v}"
        VERSION_TAG="$VERSION_SELECTOR"
        return
    fi

    if [[ "$raw" =~ ^v?[0-9]+$ ]]; then
        VERSION_SELECTOR_KIND="major"
        VERSION_SELECTOR="v${raw#v}"
        VERSION_TAG="$VERSION_SELECTOR"
        return
    fi

    echo "Error: invalid version '$raw'." >&2
    echo "Expected 'latest', 'X', 'X.Y', or 'X.Y.Z' (optionally prefixed with 'v')." >&2
    exit 2
}

# Fetches a URL to stdout using the selected downloader. Adds a GitHub token
# header when OPENTAINT_GITHUB_TOKEN or GITHUB_TOKEN is set (avoids API rate
# limits). Returns non-zero on failure.
fetch_stdout() {
    local url="$1"
    local token="${OPENTAINT_GITHUB_TOKEN:-${GITHUB_TOKEN:-}}"

    case "$DOWNLOADER" in
        curl)
            if [ -n "$token" ]; then
                curl -fsSL -H "Authorization: Bearer $token" "$url"
            else
                curl -fsSL "$url"
            fi
            ;;
        wget)
            if [ -n "$token" ]; then
                wget -qO- --header="Authorization: Bearer $token" "$url"
            else
                wget -qO- "$url"
            fi
            ;;
        *)
            return 1
            ;;
    esac
}

# Resolves a floating major/minor selector (e.g. v0 or v0.1) to the newest
# matching exact vX.Y.Z release tag by querying the GitHub releases API. Only
# exact vX.Y.Z tags are considered (floating and prefixed tags are ignored),
# mirroring scripts/resolve_opentaint_version.py. Prints the resolved tag.
resolve_floating_selector() {
    local selector="$1"
    local api_url="https://api.github.com/repos/${REPO}/releases?per_page=100"

    local body
    if ! body="$(fetch_stdout "$api_url")"; then
        echo "Error: failed to query the GitHub releases API to resolve '$selector'." >&2
        exit 2
    fi

    # Match e.g. ^v0\.  (major) or ^v0\.1\.  (minor) against vX.Y.Z tags.
    local pattern
    if [ "$VERSION_SELECTOR_KIND" = "minor" ]; then
        pattern="^${selector//./\\.}\\."
    else
        pattern="^${selector}\\."
    fi

    local best
    best="$(printf '%s' "$body" \
        | grep -oE '"tag_name"[[:space:]]*:[[:space:]]*"v[0-9]+\.[0-9]+\.[0-9]+"' \
        | sed -E 's/.*"(v[0-9]+\.[0-9]+\.[0-9]+)"$/\1/' \
        | grep -E "$pattern" \
        | sed 's/^v//' \
        | sort -t. -k1,1n -k2,2n -k3,3n \
        | tail -1)"

    if [ -z "$best" ]; then
        echo "Error: no release found matching selector '$selector'." >&2
        exit 2
    fi

    echo "v${best}"
}

# Prints the resolved path of an existing opentaint binary if it appears to
# belong to a Homebrew installation (mirrors cli/internal/utils/updater.go
# classification). Prints nothing otherwise.
detect_homebrew_install() {
    if ! command -v opentaint >/dev/null 2>&1; then
        return 0
    fi
    local path resolved
    path="$(command -v opentaint)"
    # Resolve symlinks so we can compare against the real location.
    # readlink -f is GNU-only; fall back to realpath on macOS/BSD.
    if resolved="$(readlink -f "$path" 2>/dev/null)" && [ -n "$resolved" ]; then
        path="$resolved"
    elif resolved="$(realpath "$path" 2>/dev/null)" && [ -n "$resolved" ]; then
        path="$resolved"
    fi
    case "$(printf '%s' "$path" | tr '[:upper:]' '[:lower:]')" in
        */cellar/*|*/caskroom/*|*/homebrew/*)
            echo "$path"
            ;;
    esac
}

pick_downloader() {
    if command -v curl >/dev/null 2>&1; then
        DOWNLOADER="curl"
        return
    fi
    if command -v wget >/dev/null 2>&1; then
        DOWNLOADER="wget"
        return
    fi
    echo "Error: curl or wget is required but neither is installed." >&2
    echo "Install curl or wget and re-run the installer." >&2
    exit 1
}

download() {
    local url="$1"
    local output="$2"
    local progress="${3:-0}"

    case "$DOWNLOADER" in
        curl)
            if [ "$progress" = "1" ]; then
                curl -fSL --progress-bar -o "$output" "$url"
            else
                curl -fsSL -o "$output" "$url"
            fi
            ;;
        wget)
            if [ "$progress" = "1" ]; then
                wget --show-progress --progress=bar:force:noscroll -q -O "$output" "$url"
            else
                wget -q -O "$output" "$url"
            fi
            ;;
        *)
            echo "Error: no downloader configured." >&2
            exit 1
            ;;
    esac
}

detect_platform() {
    local os arch

    os="$(uname -s)"
    case "$os" in
        Linux)  os="linux" ;;
        Darwin) os="darwin" ;;
        *)
            echo "Error: Unsupported operating system: $os" >&2
            echo "See https://github.com/seqra/opentaint/blob/main/docs/installation.md for alternatives." >&2
            exit 1
            ;;
    esac

    arch="$(uname -m)"
    case "$arch" in
        x86_64|amd64)  arch="amd64" ;;
        arm64|aarch64) arch="arm64" ;;
        *)
            echo "Error: Unsupported architecture: $arch" >&2
            echo "See https://github.com/seqra/opentaint/blob/main/docs/installation.md for alternatives." >&2
            exit 1
            ;;
    esac

    # Rosetta-2: a shell running as amd64 under Rosetta on Apple Silicon
    # should download the native arm64 archive instead.
    if [ "$os" = "darwin" ] && [ "$arch" = "amd64" ]; then
        if [ "$(sysctl -n sysctl.proc_translated 2>/dev/null)" = "1" ]; then
            arch="arm64"
        fi
    fi

    echo "${os}_${arch}"
}

verify_checksum() {
    local archive_path="$1"
    local archive_name="$2"
    local checksums_url="${DOWNLOAD_BASE_URL}/checksums.txt"

    echo "Verifying checksum..."
    if ! download "$checksums_url" "$tmp_dir/checksums.txt" 2>/dev/null; then
        echo "Warning: Could not download checksums.txt, skipping verification." >&2
        return 0
    fi

    local expected
    expected="$(grep "  ${archive_name}$" "$tmp_dir/checksums.txt" | awk '{print $1}')"
    if [ -z "$expected" ]; then
        echo "Warning: No checksum found for ${archive_name}, skipping verification." >&2
        return 0
    fi

    local actual
    if command -v sha256sum >/dev/null 2>&1; then
        actual="$(sha256sum "$archive_path" | awk '{print $1}')"
    elif command -v shasum >/dev/null 2>&1; then
        actual="$(shasum -a 256 "$archive_path" | awk '{print $1}')"
    else
        echo "Warning: No SHA256 tool found, skipping verification." >&2
        return 0
    fi

    if [ "$expected" != "$actual" ]; then
        echo "Error: Checksum verification failed!" >&2
        echo "  Expected: $expected" >&2
        echo "  Actual:   $actual" >&2
        exit 1
    fi
    echo "Checksum verified."
}

get_install_dir() {
    if [ -n "$INSTALL_DIR" ]; then
        echo "$INSTALL_DIR"
        return
    fi

    if [ "$(id -u)" = "0" ]; then
        echo "/usr/local/lib/opentaint"
    else
        echo "$HOME/.opentaint/install"
    fi
}

main() {
    local platform archive_name url install_dir bin_dir

    validate_version "${1:-}"
    pick_downloader

    local existing_brew
    existing_brew="$(detect_homebrew_install)"
    if [ -n "$existing_brew" ] && [ "${OPENTAINT_FORCE:-0}" != "1" ]; then
        echo "Error: opentaint is already installed via Homebrew at $existing_brew" >&2
        echo "Run 'brew upgrade --cask opentaint' to update, or set" >&2
        echo "OPENTAINT_FORCE=1 to install side-by-side anyway." >&2
        exit 3
    fi

    # Floating major/minor selectors are resolved to an exact tag, unless the
    # caller already pinned a fully-resolved download base URL (e.g. CI).
    if [ -z "${OPENTAINT_DOWNLOAD_BASE_URL:-}" ] && \
       { [ "$VERSION_SELECTOR_KIND" = "major" ] || [ "$VERSION_SELECTOR_KIND" = "minor" ]; }; then
        echo "Resolving ${VERSION_SELECTOR} to an exact release..."
        local resolved_tag
        resolved_tag="$(resolve_floating_selector "$VERSION_SELECTOR")"
        VERSION_PATH_SEGMENT="download/${resolved_tag}"
        VERSION_TAG="$resolved_tag"
    fi

    DOWNLOAD_BASE_URL="${OPENTAINT_DOWNLOAD_BASE_URL:-https://github.com/${REPO}/releases/${VERSION_PATH_SEGMENT}}"

    echo "Version: $VERSION_TAG"
    echo "Detecting platform..."
    platform="$(detect_platform)"
    echo "Platform: $platform"

    archive_name="opentaint-full_${platform}.tar.gz"
    url="${DOWNLOAD_BASE_URL}/${archive_name}"

    install_dir="$(get_install_dir)"
    echo "Install directory: $install_dir"

    tmp_dir="$(mktemp -d)"
    trap 'rm -rf "$tmp_dir"' EXIT

    echo "Downloading ${archive_name}..."
    download "$url" "$tmp_dir/$archive_name" 1

    verify_checksum "$tmp_dir/$archive_name" "$archive_name"

    echo "Extracting..."
    tar -xzf "$tmp_dir/$archive_name" -C "$tmp_dir"

    echo "Installing to $install_dir..."
    mkdir -p "$install_dir"
    cp "$tmp_dir/opentaint" "$install_dir/opentaint"
    chmod +x "$install_dir/opentaint"

    # Install bundled lib and jre if present (next to the binary)
    if [ -d "$tmp_dir/lib" ]; then
        mkdir -p "$install_dir/lib"
        cp -r "$tmp_dir/lib/"* "$install_dir/lib/"
    fi

    if [ -d "$tmp_dir/jre" ]; then
        mkdir -p "$install_dir/jre"
        cp -r "$tmp_dir/jre/"* "$install_dir/jre/"
    fi

    # For root installs, symlink into /usr/local/bin so the binary is in PATH
    # while keeping lib/jre next to the actual binary for bundled path resolution
    bin_dir="$install_dir"
    if [ "$(id -u)" = "0" ] && [ -z "$INSTALL_DIR" ]; then
        ln -sf "$install_dir/opentaint" /usr/local/bin/opentaint
        bin_dir="/usr/local/bin"
    fi

    echo ""
    echo "opentaint installed successfully!"
    echo ""
    echo "OPENTAINT_BINARY_PATH=$bin_dir/opentaint"
    echo ""

    # Check if bin_dir is in PATH
    case ":$PATH:" in
        *":$bin_dir:"*)
            echo "Run 'opentaint --version' to verify the installation."
            ;;
        *)
            echo "Add the following to your shell profile to use opentaint:"
            echo ""
            echo "  export PATH=\"$bin_dir:\$PATH\""
            echo ""
            echo "Then restart your shell or run the export command above."
            ;;
    esac
}

main "$@"
