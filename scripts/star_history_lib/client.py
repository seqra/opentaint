import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

from . import ChartError


CHART_ENDPOINT = "https://api.star-history.com/chart"
USER_AGENT = "opentaint-star-history"
REQUEST_TIMEOUT = 60
RETRIES = 3
RETRY_BACKOFF_SECONDS = 5
MIN_CHART_BYTES = 2048
ERROR_BODY_LIMIT = 200

TERMINAL_STATUS_HINTS = {
    400: (
        "the sealed token was rejected before it was decrypted; star-history.com "
        "may have rotated the key in star_history_lib.seal.SEALING_PUBLIC_KEY"
    ),
    401: (
        "the GitHub token was decrypted but refused; refresh the "
        "STAR_HISTORY_TOKEN secret with a valid personal access token"
    ),
}


def chart_url(
    repository: str, theme: str, token: str, chart_type: str, legend: str
) -> str:
    query = [("repos", repository), ("type", chart_type), ("legend", legend)]
    if theme != "light":
        query.append(("theme", theme))
    if token:
        query.append(("sealed_token", token))
    return f"{CHART_ENDPOINT}?{urllib.parse.urlencode(query)}"


def redact(url: str) -> str:
    return re.sub(r"(sealed_token=)[^&]*", r"\1***", url)


def describe_http_error(error: urllib.error.HTTPError) -> str:
    try:
        body = error.read().decode("utf-8", "replace").strip()
    except OSError:
        body = ""
    if not body:
        return f"HTTP {error.code}"
    return f"HTTP {error.code}: {redact(body[:ERROR_BODY_LIMIT])}"


def fetch_svg(url: str) -> str:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    last_error = ""

    for attempt in range(1, RETRIES + 1):
        try:
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
                content_type = response.headers.get("Content-Type", "")
                body = response.read().decode("utf-8")
        except urllib.error.HTTPError as error:
            last_error = describe_http_error(error)
            hint = TERMINAL_STATUS_HINTS.get(error.code)
            if hint:
                raise ChartError(f"{redact(url)} failed: {last_error} — {hint}")
        except (urllib.error.URLError, TimeoutError) as error:
            last_error = str(error)
        except UnicodeDecodeError as error:
            raise ChartError(
                f"{redact(url)} returned non-text data: {error}"
            ) from error
        else:
            if "svg" not in content_type:
                last_error = f"unexpected Content-Type '{content_type}'"
            elif len(body) < MIN_CHART_BYTES:
                last_error = f"chart is suspiciously small ({len(body)} bytes)"
            else:
                return body

        if attempt < RETRIES:
            print(
                f"::warning::Attempt {attempt}/{RETRIES} for {redact(url)} failed: "
                f"{last_error}; retrying",
                file=sys.stderr,
            )
            time.sleep(RETRY_BACKOFF_SECONDS * attempt)

    raise ChartError(f"{redact(url)} failed after {RETRIES} attempts: {last_error}")
