import base64
import json
import math
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone

from . import ChartError


API_ROOT = "https://api.github.com"
USER_AGENT = "opentaint-star-history"
API_VERSION = "2022-11-28"
STAR_MEDIA_TYPE = "application/vnd.github.star+json"
JSON_MEDIA_TYPE = "application/vnd.github+json"

AVATAR_PIXELS = 128
PER_PAGE = 100
# GitHub refuses to paginate past 400 pages of stargazers.
MAX_PAGE = 400
# Beyond this many pages we sample the curve instead of reading every star.
MAX_PAGE_REQUESTS = 30

REQUEST_TIMEOUT = 30
RETRIES = 4
RETRY_BACKOFF_SECONDS = 3
ERROR_BODY_LIMIT = 200

TERMINAL_STATUS_HINTS = {
    401: (
        "the GitHub token was refused; refresh the token the workflow passes as "
        "GITHUB_TOKEN"
    ),
    404: (
        "the repository was not found; check the name and that the token can see it"
    ),
}


def headers(token: str, accept: str) -> dict[str, str]:
    sent = {
        "Accept": accept,
        "User-Agent": USER_AGENT,
        "X-GitHub-Api-Version": API_VERSION,
    }
    if token:
        sent["Authorization"] = f"Bearer {token}"
    return sent


def describe_http_error(error: urllib.error.HTTPError) -> str:
    try:
        body = error.read().decode("utf-8", "replace").strip()
    except OSError:
        body = ""
    if not body:
        return f"HTTP {error.code}"
    return f"HTTP {error.code}: {body[:ERROR_BODY_LIMIT]}"


def rate_limited(error: urllib.error.HTTPError) -> bool:
    if error.code not in (403, 429):
        return False
    return error.headers.get("X-RateLimit-Remaining") == "0"


def fetch(url: str, request_headers: dict[str, str]) -> tuple[str, bytes]:
    request = urllib.request.Request(url, headers=request_headers)
    last_error = ""

    for attempt in range(1, RETRIES + 1):
        try:
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
                return response.headers.get("Content-Type", ""), response.read()
        except urllib.error.HTTPError as error:
            last_error = describe_http_error(error)
            if rate_limited(error):
                raise ChartError(
                    f"{url} failed: {last_error} — the GitHub API rate limit is "
                    "exhausted for this token"
                )
            hint = TERMINAL_STATUS_HINTS.get(error.code)
            if hint:
                raise ChartError(f"{url} failed: {last_error} — {hint}")
        except (urllib.error.URLError, TimeoutError) as error:
            last_error = str(error)

        if attempt < RETRIES:
            print(
                f"::warning::Attempt {attempt}/{RETRIES} for {url} failed: "
                f"{last_error}; retrying",
                file=sys.stderr,
            )
            time.sleep(RETRY_BACKOFF_SECONDS * attempt)

    raise ChartError(f"{url} failed after {RETRIES} attempts: {last_error}")


def fetch_json(url: str, token: str, accept: str = JSON_MEDIA_TYPE):
    _, payload = fetch(url, headers(token, accept))
    try:
        return json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ChartError(f"{url} returned invalid JSON: {error}") from error


def avatar_data_uri(url: str) -> str:
    """The owner's avatar, inlined so the chart stays a single self-contained file."""
    if not url:
        return ""

    separator = "&" if "?" in url else "?"
    sized = f"{url}{separator}s={AVATAR_PIXELS}"
    try:
        # A different host, so the GitHub token deliberately does not travel here.
        content_type, payload = fetch(sized, {"User-Agent": USER_AGENT})
    except ChartError as error:
        print(f"::warning::{error}; the chart will omit the logo", file=sys.stderr)
        return ""

    media_type = content_type.split(";")[0].strip()
    if not media_type.startswith("image/"):
        print(
            f"::warning::the avatar came back as '{media_type}' rather than an "
            "image; the chart will omit the logo",
            file=sys.stderr,
        )
        return ""

    encoded = base64.b64encode(payload).decode("ascii")
    return f"data:{media_type};base64,{encoded}"


def parse_timestamp(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(
            timezone.utc
        )
    except (AttributeError, ValueError) as error:
        raise ChartError(f"unparseable starred_at timestamp {value!r}") from error


def repository_facts(repository: str, token: str) -> tuple[int, datetime, str]:
    """The star total, the creation date the curve starts from, and the logo."""
    payload = fetch_json(f"{API_ROOT}/repos/{repository}", token)
    count = payload.get("stargazers_count")
    if not isinstance(count, int):
        raise ChartError(f"{repository} returned no stargazers_count")
    created = payload.get("created_at")
    if not created:
        raise ChartError(f"{repository} returned no created_at")
    owner = payload.get("owner") or {}
    return count, parse_timestamp(created), owner.get("avatar_url", "")


def stargazer_page(repository: str, page: int, token: str) -> list[dict]:
    url = (
        f"{API_ROOT}/repos/{repository}/stargazers"
        f"?per_page={PER_PAGE}&page={page}"
    )
    payload = fetch_json(url, token, accept=STAR_MEDIA_TYPE)
    if not isinstance(payload, list):
        raise ChartError(f"{url} returned {type(payload).__name__}, expected a list")
    return payload


def sampled_pages(page_count: int, budget: int = MAX_PAGE_REQUESTS) -> list[int]:
    """Evenly spaced page numbers, always including the first and the last."""
    if page_count <= budget or budget < 2:
        return list(range(1, min(page_count, max(budget, 1)) + 1))
    step = (page_count - 1) / (budget - 1)
    pages = {1 + round(index * step) for index in range(budget)}
    return sorted(pages)


def exact_timeline(repository: str, page_count: int, token: str) -> list[tuple]:
    timeline = []
    for page in range(1, page_count + 1):
        for entry in stargazer_page(repository, page, token):
            timeline.append(parse_timestamp(entry["starred_at"]))
    timeline.sort()
    return [(moment, index) for index, moment in enumerate(timeline, start=1)]


def sampled_timeline(repository: str, page_count: int, token: str) -> list[tuple]:
    timeline = []
    for page in sampled_pages(page_count):
        entries = stargazer_page(repository, page, token)
        if not entries:
            continue
        moment = parse_timestamp(entries[0]["starred_at"])
        timeline.append((moment, (page - 1) * PER_PAGE + 1))
    return timeline


def star_timeline(repository: str, token: str, now: datetime) -> dict:
    """Cumulative star counts over time, plus the metadata the manifest reports."""
    if repository.count("/") != 1:
        raise ChartError(f"repository must be owner/name, got '{repository}'")

    total, created, avatar_url = repository_facts(repository, token)
    if total < 1:
        raise ChartError(f"{repository} has no stargazers yet, so there is no chart")

    page_count = min(math.ceil(total / PER_PAGE), MAX_PAGE)
    sampled = page_count > MAX_PAGE_REQUESTS
    if sampled:
        points = sampled_timeline(repository, page_count, token)
        print(
            f"::notice::{repository} has {total} stars; sampling "
            f"{MAX_PAGE_REQUESTS} of {page_count} stargazer pages",
            file=sys.stderr,
        )
    else:
        points = exact_timeline(repository, page_count, token)

    if not points:
        raise ChartError(f"{repository} returned no stargazer timestamps")

    # Anchor the curve where the repository started, at zero stars.
    if created < points[0][0]:
        points = [(created, 0), *points]
    if now > points[-1][0]:
        points = [*points, (now, total)]

    return {
        "total": total,
        "sampled": sampled,
        "points": points,
        "avatar": avatar_data_uri(avatar_url),
    }
