#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Load the installer functions without executing main.
# shellcheck disable=SC1090
source <(sed '$d' "$SCRIPT_DIR/install.sh")

assert_eq() {
    local expected="$1"
    local actual="$2"
    if [ "$expected" != "$actual" ]; then
        echo "Expected '$expected', got '$actual'" >&2
        exit 1
    fi
}

fetch_stdout() {
    case "$1" in
        *"&page=1") printf '%s' '[{"tag_name":"analyzer/2026.01.01.abcdef0"}]' ;;
        *"&page=2") printf '%s' '[{"tag_name":"v0.4.5"},{"tag_name":"v0.5.1"}]' ;;
        *"&page=3") printf '%s' '[]' ;;
        *) return 1 ;;
    esac
}

VERSION_SELECTOR_KIND="major"
assert_eq "v0.5.1" "$(resolve_floating_selector v0)"

VERSION_SELECTOR_KIND="minor"
assert_eq "v0.4.5" "$(resolve_floating_selector v0.4)"

VERSION_SELECTOR_KIND="major"
if (resolve_floating_selector v9) >/dev/null 2>&1; then
    echo "Expected an unknown selector to fail" >&2
    exit 1
elif [ "$?" -ne 2 ]; then
    echo "Expected an unknown selector to exit 2" >&2
    exit 1
fi

validate_version v0.4.5-rc.1
assert_eq "exact" "$VERSION_SELECTOR_KIND"
assert_eq "v0.4.5-rc.1" "$VERSION_TAG"

echo "install.sh version resolution tests passed"
