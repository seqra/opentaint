import argparse
import json
import os
import sys
from datetime import datetime, timezone

from . import ChartError
from .chart import PAGE_HEIGHT, PAGE_WIDTH, palette_of, render
from .raster import asset_paths, rasterize, write_raster_page
from .stars import API_ROOT, star_timeline


THEMES = ("light", "dark")


def add_build_parser(subparsers) -> None:
    parser = subparsers.add_parser("build")
    parser.add_argument("--repository", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--basename", default="star-history")
    parser.add_argument("--token", default=os.environ.get("GITHUB_TOKEN", ""))
    parser.set_defaults(handler=build)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Chart a repository's star history")
    subparsers = parser.add_subparsers(required=True)
    add_build_parser(subparsers)

    raster_parser = subparsers.add_parser("rasterize")
    raster_parser.add_argument("--manifest", required=True)
    raster_parser.add_argument("--chrome", required=True)
    raster_parser.add_argument("--scale", default="2")
    raster_parser.set_defaults(handler=run_rasterize)

    assets_parser = subparsers.add_parser("assets")
    assets_parser.add_argument("--manifest", required=True)
    assets_parser.set_defaults(handler=print_assets)
    return parser.parse_args()


def write_chart(args: argparse.Namespace, timeline: dict, theme: str) -> dict:
    svg = render(args.repository, timeline, theme)
    svg_path = os.path.join(args.output_dir, f"{args.basename}-{theme}.svg")
    png_path = os.path.join(args.output_dir, f"{args.basename}-{theme}.png")
    with open(svg_path, "w", encoding="utf-8") as handle:
        handle.write(svg)

    background = palette_of(theme)["background"]
    return {
        "theme": theme,
        "svg": svg_path,
        "png": png_path,
        "raster_page": write_raster_page(
            svg_path, background, PAGE_WIDTH, PAGE_HEIGHT
        ),
        "background": background,
        "width": PAGE_WIDTH,
        "height": PAGE_HEIGHT,
        "bytes": len(svg.encode("utf-8")),
    }


def build_manifest(args: argparse.Namespace, now: datetime) -> dict:
    os.makedirs(args.output_dir, exist_ok=True)
    timeline = star_timeline(args.repository, args.token, now)

    charts = [write_chart(args, timeline, theme) for theme in THEMES]
    assets = [path for chart in charts for path in (chart["svg"], chart["png"])]

    return {
        "repository": args.repository,
        "source": f"{API_ROOT}/repos/{args.repository}/stargazers",
        "authenticated": bool(args.token),
        "stars": timeline["total"],
        "sampled": timeline["sampled"],
        "points": len(timeline["points"]),
        "generated_at": now.isoformat(timespec="seconds"),
        "assets": assets,
        "charts": charts,
    }


def build(args: argparse.Namespace) -> int:
    if not args.token:
        raise ChartError(
            "no GitHub token available; the workflow must pass GITHUB_TOKEN so the "
            "stargazer pages can be read without hitting the anonymous rate limit"
        )
    print(json.dumps(build_manifest(args, datetime.now(timezone.utc))))
    return 0


def run_rasterize(args: argparse.Namespace) -> int:
    rasterize(args.manifest, args.chrome, args.scale)
    return 0


def print_assets(args: argparse.Namespace) -> int:
    print("\n".join(asset_paths(args.manifest)))
    return 0


def main() -> int:
    args = parse_args()
    try:
        return args.handler(args)
    except ChartError as error:
        print(f"::error::{error}", file=sys.stderr)
        return 1
