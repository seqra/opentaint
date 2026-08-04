import argparse
import json
import os
import sys

from . import ChartError
from .client import CHART_ENDPOINT, chart_url, fetch_svg
from .raster import asset_paths, rasterize, write_raster_page
from .seal import seal_token
from .svg import background_of, sanitize_svg, viewport_of


THEMES = ("light", "dark")


def add_mirror_parser(subparsers) -> None:
    parser = subparsers.add_parser("mirror")
    parser.add_argument("--repository", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--basename", default="star-history")
    parser.add_argument("--token", default=os.environ.get("STAR_HISTORY_TOKEN", ""))
    parser.add_argument("--chart-type", default="date")
    parser.add_argument("--legend", default="top-left")
    parser.set_defaults(handler=mirror)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Mirror star-history.com charts")
    subparsers = parser.add_subparsers(required=True)
    add_mirror_parser(subparsers)

    raster_parser = subparsers.add_parser("rasterize")
    raster_parser.add_argument("--manifest", required=True)
    raster_parser.add_argument("--chrome", required=True)
    raster_parser.add_argument("--scale", default="2")
    raster_parser.set_defaults(handler=run_rasterize)

    assets_parser = subparsers.add_parser("assets")
    assets_parser.add_argument("--manifest", required=True)
    assets_parser.set_defaults(handler=print_assets)
    return parser.parse_args()


def fetch_sanitized_svg(url: str) -> str:
    return sanitize_svg(fetch_svg(url))


def build_manifest(args: argparse.Namespace) -> dict:
    if args.repository.count("/") != 1:
        raise ChartError(f"--repository must be owner/name, got '{args.repository}'")

    os.makedirs(args.output_dir, exist_ok=True)
    charts = []
    assets = []

    sealed = seal_token(args.token) if args.token else ""
    if not sealed:
        print(
            "::warning::No STAR_HISTORY_TOKEN set; falling back to the shared "
            "star-history.com token pool, which is often rate-limited",
            file=sys.stderr,
        )

    for theme in THEMES:
        url = chart_url(
            args.repository, theme, sealed, args.chart_type, args.legend
        )
        svg = fetch_sanitized_svg(url)
        svg_path = os.path.join(args.output_dir, f"{args.basename}-{theme}.svg")
        png_path = os.path.join(args.output_dir, f"{args.basename}-{theme}.png")
        with open(svg_path, "w", encoding="utf-8") as handle:
            handle.write(svg)

        width, height = viewport_of(svg, theme)
        background = background_of(svg, theme)
        charts.append(
            {
                "theme": theme,
                "svg": svg_path,
                "png": png_path,
                "raster_page": write_raster_page(
                    svg_path, background, width, height
                ),
                "background": background,
                "width": width,
                "height": height,
                "bytes": len(svg.encode("utf-8")),
            }
        )
        assets.extend((svg_path, png_path))

    return {
        "repository": args.repository,
        "source": CHART_ENDPOINT,
        "authenticated": bool(args.token),
        "assets": assets,
        "charts": charts,
    }


def mirror(args: argparse.Namespace) -> int:
    print(json.dumps(build_manifest(args)))
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
