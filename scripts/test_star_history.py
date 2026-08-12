import argparse
import base64
import json
import re
import os
import sys
import tempfile
import unittest
import urllib.error
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.message import Message
from io import BytesIO
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from star_history_lib import ChartError, chart, cli, raster, stars


UTC = timezone.utc


def moment(day: int, month: int = 1, year: int = 2025) -> datetime:
    return datetime(year, month, day, tzinfo=UTC)


AVATAR = "data:image/png;base64,aGVsbG8="


def timeline(points, total=None, sampled=False, avatar=AVATAR) -> dict:
    return {
        "points": points,
        "total": total if total is not None else points[-1][1],
        "sampled": sampled,
        "avatar": avatar,
    }


def http_error(code: int, body: bytes = b"", headers: dict | None = None):
    message = Message()
    for key, value in (headers or {}).items():
        message[key] = value
    return urllib.error.HTTPError("https://api.github.com", code, "", message, None)


AVATAR_URL = "https://avatars.githubusercontent.com/u/1?v=4"
AVATAR_BYTES = b"\x89PNG\r\n\x1a\nfake-avatar"


class FakeResponse:
    def __init__(self, payload=None, *, body=None, content_type="application/json"):
        if body is None:
            body = json.dumps(payload).encode("utf-8")
        self.stream = BytesIO(body)
        self.headers = {"Content-Type": content_type}

    def read(self):
        return self.stream.read()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        return False


class FakeGitHub:
    """Serves repository metadata and stargazer pages from an in-memory clock."""

    def __init__(self, count: int, first: datetime = moment(1), spacing_hours=6):
        self.count = count
        self.first = first
        self.created = first - timedelta(days=1)
        self.spacing = timedelta(hours=spacing_hours)
        self.requests = []

    def starred_at(self, index: int) -> str:
        return (self.first + self.spacing * index).strftime("%Y-%m-%dT%H:%M:%SZ")

    def __call__(self, request, timeout=None):
        url = request.full_url
        self.requests.append(url)
        if "avatars.githubusercontent.com" in url:
            self.avatar_headers = dict(request.headers)
            return FakeResponse(body=AVATAR_BYTES, content_type="image/png")
        if "/stargazers" not in url:
            return FakeResponse(
                {
                    "stargazers_count": self.count,
                    "created_at": self.created.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "owner": {"avatar_url": AVATAR_URL},
                }
            )

        page = int(url.split("page=")[-1])
        start = (page - 1) * stars.PER_PAGE
        end = min(start + stars.PER_PAGE, self.count)
        return FakeResponse(
            [{"starred_at": self.starred_at(index)} for index in range(start, end)]
        )


class TestFetchJson(unittest.TestCase):
    def test_returns_decoded_payload(self):
        with mock.patch("urllib.request.urlopen", FakeGitHub(7)):
            payload = stars.fetch_json("https://api.github.com/repos/a/b", "t")
        self.assertEqual(payload["stargazers_count"], 7)

    def test_sends_bearer_token_and_media_type(self):
        sent = stars.headers("secret", stars.STAR_MEDIA_TYPE)
        self.assertEqual(sent["Authorization"], "Bearer secret")
        self.assertEqual(sent["Accept"], stars.STAR_MEDIA_TYPE)

    def test_omits_authorization_without_a_token(self):
        self.assertNotIn("Authorization", stars.headers("", stars.JSON_MEDIA_TYPE))

    def test_retries_transient_failures_then_succeeds(self):
        attempts = []

        def flaky(request, timeout=None):
            attempts.append(request.full_url)
            if len(attempts) < 3:
                raise urllib.error.URLError("connection reset")
            return FakeResponse({"stargazers_count": 3})

        with mock.patch("urllib.request.urlopen", flaky), mock.patch("time.sleep"):
            payload = stars.fetch_json("https://api.github.com/repos/a/b", "t")

        self.assertEqual(payload, {"stargazers_count": 3})
        self.assertEqual(len(attempts), 3)

    def test_gives_up_after_the_retry_budget(self):
        def always_failing(request, timeout=None):
            raise TimeoutError("timed out")

        with mock.patch("urllib.request.urlopen", always_failing), mock.patch(
            "time.sleep"
        ):
            with self.assertRaises(ChartError) as caught:
                stars.fetch_json("https://api.github.com/repos/a/b", "t")

        self.assertIn(f"after {stars.RETRIES} attempts", str(caught.exception))

    def test_does_not_retry_a_missing_repository(self):
        attempts = []

        def missing(request, timeout=None):
            attempts.append(request.full_url)
            raise http_error(404, b'{"message":"Not Found"}')

        with mock.patch("urllib.request.urlopen", missing), mock.patch("time.sleep"):
            with self.assertRaises(ChartError) as caught:
                stars.fetch_json("https://api.github.com/repos/a/b", "t")

        self.assertEqual(len(attempts), 1)
        self.assertIn("repository was not found", str(caught.exception))

    def test_reports_an_exhausted_rate_limit(self):
        def limited(request, timeout=None):
            raise http_error(403, b"rate limited", {"X-RateLimit-Remaining": "0"})

        with mock.patch("urllib.request.urlopen", limited), mock.patch("time.sleep"):
            with self.assertRaises(ChartError) as caught:
                stars.fetch_json("https://api.github.com/repos/a/b", "t")

        self.assertIn("rate limit is exhausted", str(caught.exception))

    def test_retries_a_server_error(self):
        attempts = []

        def unstable(request, timeout=None):
            attempts.append(request.full_url)
            if len(attempts) < 2:
                raise http_error(500, b"upstream boom")
            return FakeResponse({"stargazers_count": 1})

        with mock.patch("urllib.request.urlopen", unstable), mock.patch("time.sleep"):
            stars.fetch_json("https://api.github.com/repos/a/b", "t")

        self.assertEqual(len(attempts), 2)


class TestSampling(unittest.TestCase):
    def test_returns_every_page_within_budget(self):
        self.assertEqual(stars.sampled_pages(4, budget=10), [1, 2, 3, 4])

    def test_samples_endpoints_inclusively(self):
        pages = stars.sampled_pages(400, budget=30)
        self.assertEqual(pages[0], 1)
        self.assertEqual(pages[-1], 400)
        self.assertLessEqual(len(pages), 30)
        self.assertEqual(pages, sorted(set(pages)))


class TestStarTimeline(unittest.TestCase):
    def test_rejects_a_malformed_repository(self):
        with self.assertRaises(ChartError):
            stars.star_timeline("opentaint", "t", moment(2))

    def test_rejects_a_repository_with_no_stars(self):
        with mock.patch("urllib.request.urlopen", FakeGitHub(0)):
            with self.assertRaises(ChartError):
                stars.star_timeline("seqra/opentaint", "t", moment(2))

    def test_counts_every_star_when_pages_fit_the_budget(self):
        github = FakeGitHub(127)
        now = moment(1, month=6)
        with mock.patch("urllib.request.urlopen", github):
            result = stars.star_timeline("seqra/opentaint", "t", now)

        self.assertFalse(result["sampled"])
        self.assertEqual(result["total"], 127)
        # A zero-star anchor, 127 stars, then a point carrying the curve to `now`.
        self.assertEqual(len(result["points"]), 129)
        self.assertEqual(result["points"][0], (github.created, 0))
        self.assertEqual(result["points"][1][1], 1)
        self.assertEqual(result["points"][-1], (now, 127))

    def test_counts_rise_monotonically(self):
        with mock.patch("urllib.request.urlopen", FakeGitHub(150)):
            points = stars.star_timeline("seqra/opentaint", "t", moment(1, 6))["points"]

        counts = [count for _, count in points]
        dates = [when for when, _ in points]
        self.assertEqual(counts, sorted(counts))
        self.assertEqual(dates, sorted(dates))

    def test_samples_pages_for_a_large_repository(self):
        github = FakeGitHub(50_000, spacing_hours=1)
        with mock.patch("urllib.request.urlopen", github):
            result = stars.star_timeline("seqra/opentaint", "t", moment(1, 6, 2030))

        self.assertTrue(result["sampled"])
        stargazer_calls = [url for url in github.requests if "/stargazers" in url]
        self.assertLessEqual(len(stargazer_calls), stars.MAX_PAGE_REQUESTS)
        self.assertEqual(result["points"][-1][1], 50_000)

    def test_skips_the_trailing_point_when_now_is_not_newer(self):
        github = FakeGitHub(3)
        last = github.first + github.spacing * 2
        with mock.patch("urllib.request.urlopen", github):
            result = stars.star_timeline("seqra/opentaint", "t", last)

        self.assertEqual(len(result["points"]), 4)
        self.assertEqual(result["points"][-1][1], 3)

    def test_rejects_an_unparseable_timestamp(self):
        def broken(request, timeout=None):
            if "/stargazers" in request.full_url:
                return FakeResponse([{"starred_at": "not-a-date"}])
            return FakeResponse(
                {"stargazers_count": 1, "created_at": "2025-01-01T00:00:00Z"}
            )

        with mock.patch("urllib.request.urlopen", broken):
            with self.assertRaises(ChartError):
                stars.star_timeline("seqra/opentaint", "t", moment(2))


class TestAvatar(unittest.TestCase):
    def test_the_timeline_carries_the_owner_avatar(self):
        with mock.patch("urllib.request.urlopen", FakeGitHub(5)):
            result = stars.star_timeline("seqra/opentaint", "t", moment(1, 6))

        expected = base64.b64encode(AVATAR_BYTES).decode("ascii")
        self.assertEqual(result["avatar"], f"data:image/png;base64,{expected}")

    def test_the_avatar_is_requested_at_a_usable_size(self):
        github = FakeGitHub(5)
        with mock.patch("urllib.request.urlopen", github):
            stars.star_timeline("seqra/opentaint", "t", moment(1, 6))

        avatar_calls = [url for url in github.requests if "avatars." in url]
        self.assertEqual(len(avatar_calls), 1)
        self.assertIn(f"s={stars.AVATAR_PIXELS}", avatar_calls[0])

    def test_the_github_token_is_not_sent_to_the_avatar_host(self):
        github = FakeGitHub(5)
        with mock.patch("urllib.request.urlopen", github):
            stars.star_timeline("seqra/opentaint", "t", moment(1, 6))

        sent = {key.lower() for key in github.avatar_headers}
        self.assertNotIn("authorization", sent)

    def test_a_failing_avatar_does_not_fail_the_chart(self):
        def flaky(request, timeout=None):
            if "avatars." in request.full_url:
                raise urllib.error.URLError("avatar host down")
            return FakeGitHub(5)(request, timeout)

        with mock.patch("urllib.request.urlopen", flaky), mock.patch(
            "time.sleep"
        ), mock.patch("sys.stderr", new_callable=lambda: open(os.devnull, "w")):
            result = stars.star_timeline("seqra/opentaint", "t", moment(1, 6))

        self.assertEqual(result["avatar"], "")
        self.assertEqual(result["total"], 5)

    def test_a_non_image_response_is_ignored(self):
        def wrong_type(request, timeout=None):
            if "avatars." in request.full_url:
                return FakeResponse(body=b"<html>", content_type="text/html")
            return FakeGitHub(5)(request, timeout)

        with mock.patch("urllib.request.urlopen", wrong_type), mock.patch(
            "sys.stderr", new_callable=lambda: open(os.devnull, "w")
        ):
            result = stars.star_timeline("seqra/opentaint", "t", moment(1, 6))

        self.assertEqual(result["avatar"], "")


class TestAxes(unittest.TestCase):
    def test_tick_step_matches_d3(self):
        # The values d3.tickIncrement produces for the same inputs.
        for maximum, expected in ((126, 20), (5, 1), (1000, 200), (4200, 500)):
            self.assertEqual(chart.tick_step(maximum, chart.Y_TICK_TARGET), expected)

    def test_value_ticks_reproduce_the_reference_axis(self):
        self.assertEqual(chart.value_ticks(126), [0, 20, 40, 60, 80, 100, 120])

    def test_value_ticks_never_exceed_the_maximum(self):
        self.assertLessEqual(chart.value_ticks(127)[-1], 127)

    def test_a_tiny_repository_still_gets_integer_ticks(self):
        self.assertEqual(chart.value_ticks(3), [0, 1, 2, 3])

    def test_a_year_of_history_steps_by_three_months(self):
        self.assertEqual(chart.month_step(timedelta(days=310)), 3)

    def test_a_long_history_steps_by_a_year(self):
        self.assertEqual(chart.month_step(timedelta(days=2000)), 12)

    def test_quarter_ticks_land_on_january_april_july_october(self):
        ticks = chart.time_ticks(moment(30, 9, 2025), moment(6, 8, 2026))
        self.assertEqual(
            [label for _, label in ticks], ["October", "2026", "April", "July"]
        )

    def test_january_is_labelled_with_the_year(self):
        ticks = chart.time_ticks(moment(30, 9, 2025), moment(6, 8, 2026))
        january = [tick for tick, label in ticks if label == "2026"][0]
        self.assertEqual((january.month, january.year), (1, 2026))

    def test_ticks_stay_inside_the_domain(self):
        start, end = moment(14, 10, 2025), moment(6, 8, 2026)
        for tick, _ in chart.time_ticks(start, end):
            self.assertGreaterEqual(tick, start)
            self.assertLessEqual(tick, end)

    def test_a_short_history_falls_back_to_day_ticks(self):
        ticks = chart.time_ticks(moment(1), moment(9))
        self.assertTrue(ticks)
        self.assertRegex(ticks[0][1], r"^[A-Z][a-z]{2} \d{2}$")


def path_numbers(path: str) -> list[float]:
    return [float(value) for value in re.findall(r"-?\d+\.?\d*", path)]


class TestCurve(unittest.TestCase):
    def test_a_single_point_is_just_a_move(self):
        self.assertEqual(chart.basis_path([(0.0, 10.0)]), "M0 10")

    def test_two_points_are_a_straight_line(self):
        self.assertEqual(chart.basis_path([(0.0, 0.0), (5.0, 5.0)]), "M0 0L5 5")

    def test_each_span_emits_one_cubic(self):
        path = chart.basis_path([(0.0, 0.0), (1.0, 1.0), (2.0, 4.0)])
        self.assertEqual(path.count("C"), 2)
        self.assertTrue(path.startswith("M0 0"))

    def test_the_curve_starts_and_ends_on_the_data(self):
        points = [(0.0, 0.0), (10.0, 5.0), (20.0, 30.0), (30.0, 31.0)]
        numbers = path_numbers(chart.basis_path(points))
        self.assertEqual((numbers[0], numbers[1]), points[0])
        self.assertEqual((numbers[-2], numbers[-1]), points[-1])

    def test_a_rising_series_never_dips(self):
        # curveBasis is variation-diminishing, so a falling y (rising count)
        # must never produce a control point above where it started.
        points = [(0.0, 100.0), (10.0, 100.0), (20.0, 40.0), (30.0, 0.0)]
        ys = path_numbers(chart.basis_path(points))[1::2]
        self.assertTrue(all(y <= 100.0001 for y in ys))
        self.assertTrue(all(y >= -0.0001 for y in ys))

    def test_the_spline_smooths_rather_than_interpolates(self):
        # A corner point is approximated, which is exactly what removes the kink.
        points = [(0.0, 0.0), (10.0, 0.0), (20.0, 100.0), (30.0, 100.0)]
        self.assertNotIn("100 100", chart.basis_path(points)[: -len("L30 100")])

    def test_downsample_keeps_the_ends(self):
        points = [(moment(1) + timedelta(days=i), i) for i in range(200)]
        reduced = chart.downsample(points, 11)
        self.assertEqual(len(reduced), 11)
        self.assertEqual(reduced[0], points[0])
        self.assertEqual(reduced[-1], points[-1])

    def test_downsample_leaves_short_series_alone(self):
        points = [(moment(1), 1), (moment(2), 2)]
        self.assertEqual(chart.downsample(points, 11), points)


class TestRender(unittest.TestCase):
    def setUp(self):
        self.timeline = timeline(
            [(moment(1, month), month * 10) for month in range(1, 13)]
        )

    def series_path(self, svg: str) -> str:
        match = re.search(
            r'stroke="#[0-9a-f]+" d="([^"]+)" class="xkcd-chart-xyline"', svg
        )
        self.assertIsNotNone(match, "the series path is missing")
        return match.group(1)

    def test_renders_well_formed_svg_for_both_themes(self):
        for theme in cli.THEMES:
            svg = chart.render("seqra/opentaint", self.timeline, theme)
            root = ET.fromstring(svg)
            self.assertEqual(root.tag, "{http://www.w3.org/2000/svg}svg")
            self.assertEqual(root.get("width"), str(chart.WIDTH))
            self.assertEqual(root.get("height"), "533.333")
            self.assertIn(
                f'background:{chart.PALETTES[theme]["background"]}', root.get("style")
            )

    def test_carries_the_xkcdify_filter(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertIn('<filter id="xkcdify"', svg)
        self.assertIn('<feTurbulence baseFrequency=".05"', svg)
        self.assertIn('<feDisplacementMap in="SourceGraphic"', svg)
        # The axes, the legend and the curve all have to wobble.
        self.assertGreaterEqual(svg.count('filter="url(#xkcdify)"'), 5)

    def test_embeds_the_handwriting_font(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertIn('@font-face{font-family:"xkcd"', svg)
        self.assertIn("data:application/font-woff;charset=utf-8;base64,", svg)

    def test_omits_star_history_branding(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertNotIn("star-history.com", svg)
        # The only embedded image is the repository owner's own avatar.
        self.assertEqual(svg.count("<image"), 1)
        self.assertIn(f'href="{AVATAR}"', svg)

    def test_themes_render_different_colours(self):
        light = chart.render("seqra/opentaint", self.timeline, "light")
        dark = chart.render("seqra/opentaint", self.timeline, "dark")
        self.assertIn(chart.PALETTES["light"]["series"], light)
        self.assertIn(chart.PALETTES["dark"]["series"], dark)
        self.assertNotIn(chart.PALETTES["dark"]["series"], light)

    def test_legend_carries_the_repository_name(self):
        svg = chart.render("seqra/opentaint", self.timeline, "light")
        labels = [element.text for element in ET.fromstring(svg).iter() if element.text]
        self.assertIn("seqra/opentaint", labels)
        self.assertIn("Star History", labels)
        self.assertIn("GitHub Stars", labels)
        self.assertIn("Date", labels)

    def test_legend_box_matches_the_reference_width(self):
        svg = chart.render("seqra/opentaint", self.timeline, "light")
        self.assertIn('<rect width="141.5" height="32" x="8" y="5"', svg)

    def test_legend_box_grows_with_a_longer_name(self):
        svg = chart.render("some-org/a-much-longer-name", self.timeline, "light")
        width = float(re.search(r'<rect width="([\d.]+)" height="32"', svg).group(1))
        self.assertGreater(width, 141.5)

    def test_the_zero_label_is_blank(self):
        svg = chart.render("a/b", self.timeline, "light")
        labels = [
            element.text
            for element in ET.fromstring(svg).iter()
            if element.get("dy") == ".32em"
        ]
        self.assertEqual(labels[0], " ")
        self.assertNotIn("0", labels[:1])

    def test_a_repository_name_is_escaped(self):
        svg = chart.render("a/<b>&", timeline([(moment(1), 5)]), "light")
        self.assertNotIn("<b>", svg)
        ET.fromstring(svg)

    def test_the_curve_stays_inside_the_plot_area(self):
        svg = chart.render("a/b", self.timeline, "light")
        numbers = path_numbers(self.series_path(svg))
        xs, ys = numbers[0::2], numbers[1::2]
        self.assertGreaterEqual(min(xs), 0)
        self.assertLessEqual(max(xs), chart.PLOT_WIDTH)
        self.assertGreaterEqual(min(ys), 0)
        self.assertLessEqual(max(ys), chart.BASELINE)

    def test_the_curve_spans_the_full_width(self):
        numbers = path_numbers(
            self.series_path(chart.render("a/b", self.timeline, "light"))
        )
        self.assertEqual(numbers[0], 0)
        self.assertEqual(numbers[-2], chart.PLOT_WIDTH)

    def test_embeds_the_owner_avatar_beside_the_title(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertIn(f'href="{AVATAR}"', svg)
        self.assertIn(
            f'<image width="22" height="22" x="{chart.LOGO_X}" y="{chart.LOGO_Y}"', svg
        )

    def test_the_avatar_is_clipped_to_a_circle(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertIn(f'clip-path="url(#{chart.LOGO_CLIP_ID})"', svg)
        circle = re.search(r'<circle cx="([\d.]+)" cy="([\d.]+)" r="([\d.]+)"', svg)
        radius = chart.LOGO_SIZE / 2
        self.assertEqual(
            [float(value) for value in circle.groups()],
            [chart.LOGO_X + radius, chart.LOGO_Y + radius, radius],
        )

    def test_renders_without_an_avatar(self):
        svg = chart.render("a/b", timeline([(moment(1), 5)], avatar=""), "light")
        self.assertNotIn("<image", svg)
        self.assertNotIn("clipPath", svg)
        self.assertIn("Star History", svg)
        ET.fromstring(svg)

    def test_the_title_stays_centred(self):
        svg = chart.render("a/b", self.timeline, "light")
        self.assertIn(f'<text x="50%" y="{chart.TITLE_BASELINE}"', svg)

    def test_a_flat_single_point_series_still_renders(self):
        svg = chart.render("a/b", timeline([(moment(1), 1)]), "light")
        ET.fromstring(svg)

    def test_rejects_an_unknown_theme(self):
        with self.assertRaises(ChartError):
            chart.render("a/b", self.timeline, "sepia")

    def test_rejects_an_empty_timeline(self):
        with self.assertRaises(ChartError):
            chart.render("a/b", timeline([], total=0), "light")


class TestManifest(unittest.TestCase):
    def build(self, directory: str, count: int = 127) -> dict:
        args = argparse.Namespace(
            repository="seqra/opentaint",
            output_dir=os.path.join(directory, "dist"),
            basename="star-history",
            token="t",
        )
        with mock.patch("urllib.request.urlopen", FakeGitHub(count)):
            return cli.build_manifest(args, moment(1, 6))

    def test_writes_an_svg_and_a_raster_page_per_theme(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = self.build(directory)

            self.assertEqual([c["theme"] for c in manifest["charts"]], ["light", "dark"])
            for entry in manifest["charts"]:
                self.assertTrue(os.path.isfile(entry["svg"]))
                self.assertTrue(os.path.isfile(entry["raster_page"]))
                self.assertEqual(entry["width"], chart.WIDTH)
                self.assertGreater(entry["bytes"], 0)

    def test_assets_list_the_svg_and_png_of_each_theme(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = self.build(directory)
            self.assertEqual(len(manifest["assets"]), 4)
            self.assertEqual(
                [os.path.basename(path) for path in manifest["assets"]],
                [
                    "star-history-light.svg",
                    "star-history-light.png",
                    "star-history-dark.svg",
                    "star-history-dark.png",
                ],
            )

    def test_records_the_star_count_and_source(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = self.build(directory)
            self.assertEqual(manifest["stars"], 127)
            self.assertFalse(manifest["sampled"])
            self.assertTrue(manifest["authenticated"])
            self.assertIn("seqra/opentaint/stargazers", manifest["source"])

    def test_the_manifest_round_trips_through_the_asset_reader(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = self.build(directory)
            path = os.path.join(directory, "manifest.json")
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(manifest, handle)

            self.assertEqual(raster.asset_paths(path), manifest["assets"])

    def test_build_refuses_to_run_without_a_token(self):
        args = argparse.Namespace(
            repository="seqra/opentaint",
            output_dir="dist",
            basename="star-history",
            token="",
        )
        with self.assertRaises(ChartError):
            cli.build(args)


class TestRasterPage(unittest.TestCase):
    def test_page_references_the_svg_and_its_background(self):
        with tempfile.TemporaryDirectory() as directory:
            svg_path = os.path.join(directory, "star-history-dark.svg")
            page = raster.write_raster_page(svg_path, "#0d1117", 800, 534)

            with open(page, encoding="utf-8") as handle:
                document = handle.read()

            self.assertIn('src="star-history-dark.svg"', document)
            self.assertIn("background:#0d1117", document)
            self.assertIn("Content-Security-Policy", document)


class TestEntryPoint(unittest.TestCase):
    def test_main_reports_chart_errors_as_workflow_errors(self):
        argv = ["star_history.py", "build", "--repository", "bad", "--output-dir", "d"]
        with mock.patch.object(sys, "argv", argv), mock.patch.dict(
            os.environ, {"GITHUB_TOKEN": "t"}
        ), mock.patch("star_history_lib.cli.build_manifest", side_effect=ChartError("x")):
            with mock.patch("sys.stderr", new_callable=lambda: open(os.devnull, "w")):
                self.assertEqual(cli.main(), 1)


if __name__ == "__main__":
    unittest.main()
