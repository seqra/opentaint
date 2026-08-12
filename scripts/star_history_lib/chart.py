"""Renders star history charts in star-history.com's hand-drawn style.

The layout, the xkcdify turbulence filter and the type scale are matched to the
charts this repository previously mirrored from star-history.com, so the README
keeps the look it had. Their watermark and their logo are deliberately left out:
these charts are built from the GitHub API, so crediting their service would
misstate where the data came from. The repository owner's avatar takes the place
their mark used to occupy.
"""

import base64
import functools
import math
from datetime import datetime, timedelta
from pathlib import Path
from xml.sax.saxutils import escape

from . import ChartError


WIDTH = 800
HEIGHT = 533.333
# Chrome needs whole pixels for the screenshot viewport.
PAGE_WIDTH = 800
PAGE_HEIGHT = 534

PLOT_ORIGIN = (70, 60)
PLOT_WIDTH = 700
PLOT_HEIGHT = 423.333
# Where a count of zero sits inside the translated plot group.
BASELINE = 423.833

FONT_FAMILY = "xkcd"
FONT_PATH = Path(__file__).parent / "assets" / "xkcd-script.woff"

# The owner avatar sits left of the centred title, circular-clipped, at the same
# coordinates star-history used for its own mark.
LOGO_SIZE = 22
LOGO_X = 316
LOGO_Y = 12
LOGO_CLIP_ID = "clip-circle-title"

TITLE = "Star History"
TITLE_SIZE = 20
TITLE_BASELINE = 30

PALETTES = {
    "light": {"background": "#fff", "ink": "#000", "series": "#dd4528"},
    "dark": {"background": "#0d1117", "ink": "#fff", "series": "#ff6b6b"},
}

# star-history plots a sampled curve rather than every star; sampling first is
# what lets the spline read as a trend instead of tracing every single star.
MAX_CHART_POINTS = 11
X_TICK_TARGET = 5
Y_TICK_TARGET = 6
MONTH_STEPS = (1, 3, 6, 12)
DAYS_PER_MONTH = 30.44
WEEK_SPAN_DAYS = 14
DAY_SPAN_DAYS = 60

LEGEND_TEXT_ORIGIN = 29
LEGEND_CHARACTER_WIDTH = 7.5

E10 = math.sqrt(50)
E5 = math.sqrt(10)
E2 = math.sqrt(2)


def palette_of(theme: str) -> dict:
    try:
        return PALETTES[theme]
    except KeyError:
        raise ChartError(f"unknown chart theme '{theme}'") from None


@functools.lru_cache(maxsize=1)
def font_face() -> str:
    try:
        woff = FONT_PATH.read_bytes()
    except OSError as error:
        raise ChartError(f"the embedded chart font is missing: {error}") from error
    encoded = base64.b64encode(woff).decode("ascii")
    return (
        f'@font-face{{font-family:"{FONT_FAMILY}";'
        f"src:url(data:application/font-woff;charset=utf-8;base64,{encoded})"
        'format("woff")}'
    )


def number(value: float) -> str:
    return f"{round(value, 3):g}"


def tick_step(maximum: float, count: int) -> float:
    """d3's tickIncrement, so the axis lands on the same numbers d3 would pick."""
    raw = maximum / max(1, count)
    if raw <= 0:
        return 1
    power = math.floor(math.log10(raw))
    error = raw / 10**power
    if error >= E10:
        factor = 10
    elif error >= E5:
        factor = 5
    elif error >= E2:
        factor = 2
    else:
        factor = 1
    return factor * 10**power


def value_ticks(maximum: int) -> list[int]:
    step = max(1, round(tick_step(maximum, Y_TICK_TARGET)))
    return [tick for tick in range(0, maximum + 1, step)]


def month_step(span: timedelta) -> int:
    months = span.days / DAYS_PER_MONTH
    for step in MONTH_STEPS:
        if months / step <= X_TICK_TARGET:
            return step
    return MONTH_STEPS[-1]


def month_ticks(start: datetime, end: datetime, step: int) -> list[datetime]:
    ticks = []
    cursor = start.year * 12 + start.month - 1
    while True:
        year, month = divmod(cursor, 12)
        moment = datetime(year, month + 1, 1, tzinfo=start.tzinfo)
        if moment > end:
            return ticks
        if moment >= start and month % step == 0:
            ticks.append(moment)
        cursor += 1


def spaced_ticks(start: datetime, end: datetime, stride: timedelta) -> list[datetime]:
    ticks = []
    moment = start.replace(hour=0, minute=0, second=0, microsecond=0) + stride
    while moment <= end:
        ticks.append(moment)
        moment += stride
    return ticks


def time_ticks(start: datetime, end: datetime) -> list[tuple[datetime, str]]:
    span = end - start
    if span.days <= WEEK_SPAN_DAYS:
        return [(tick, f"{tick:%b %d}") for tick in spaced_ticks(start, end, timedelta(days=2))]
    if span.days <= DAY_SPAN_DAYS:
        return [(tick, f"{tick:%b %d}") for tick in spaced_ticks(start, end, timedelta(days=7))]

    ticks = month_ticks(start, end, month_step(span))
    return [
        (tick, f"{tick:%Y}" if tick.month == 1 else f"{tick:%B}") for tick in ticks
    ]


def downsample(points: list[tuple], limit: int = MAX_CHART_POINTS) -> list[tuple]:
    if len(points) <= limit:
        return points
    stride = (len(points) - 1) / (limit - 1)
    return [points[round(index * stride)] for index in range(limit)]


def cubic(before: tuple, current: tuple, following: tuple) -> str:
    """One uniform cubic B-spline span, in d3 curveBasis' bezier form."""
    x0, y0 = before
    x1, y1 = current
    x2, y2 = following
    return (
        f"C{number((2 * x0 + x1) / 3)} {number((2 * y0 + y1) / 3)}"
        f" {number((x0 + 2 * x1) / 3)} {number((y0 + 2 * y1) / 3)}"
        f" {number((x0 + 4 * x1 + x2) / 6)} {number((y0 + 4 * y1 + y2) / 6)}"
    )


def basis_path(coordinates: list[tuple[float, float]]) -> str:
    """A B-spline through the samples, matching d3's curveBasis.

    The spline approximates rather than interpolates, which is what smooths the
    corners a plain interpolation leaves behind. Being variation-diminishing, it
    still cannot dip below a series that only ever rises.
    """
    first = coordinates[0]
    path = f"M{number(first[0])} {number(first[1])}"
    if len(coordinates) == 1:
        return path
    if len(coordinates) == 2:
        last = coordinates[1]
        return f"{path}L{number(last[0])} {number(last[1])}"

    second = coordinates[1]
    path += (
        f"L{number((5 * first[0] + second[0]) / 6)}"
        f" {number((5 * first[1] + second[1]) / 6)}"
    )
    for index in range(2, len(coordinates)):
        path += cubic(coordinates[index - 2], coordinates[index - 1], coordinates[index])

    last = coordinates[-1]
    path += cubic(coordinates[-2], last, last)
    return f"{path}L{number(last[0])} {number(last[1])}"


def projector(start: datetime, end: datetime, maximum: int):
    span = (end - start).total_seconds() or 1.0

    def project(moment: datetime, value: float) -> tuple[float, float]:
        x = (moment - start).total_seconds() / span * PLOT_WIDTH
        y = BASELINE - (value / maximum if maximum else 0) * PLOT_HEIGHT
        return x, y

    return project


def x_axis(ticks: list[tuple[datetime, str]], project, ink: str) -> str:
    labels = "".join(
        f'<text y="6" fill="currentColor" class="tick" dy=".71em" '
        f'style="font-family:{FONT_FAMILY};font-size:16px;fill:{ink}" '
        f'transform="translate({number(project(moment, 0)[0])} {number(BASELINE - 0.5)})">'
        f"{escape(label)}</text>"
        for moment, label in ticks
    )
    return (
        '<g fill="none" class="xaxis" font-family="sans-serif" font-size="10" '
        'text-anchor="middle">'
        f'<path stroke="currentColor" d="M.5.5h{PLOT_WIDTH}" class="domain" '
        f'filter="url(#xkcdify)" style="stroke:{ink}" '
        f'transform="translate(0 {number(BASELINE - 0.5)})"/>'
        f"{labels}</g>"
    )


def y_axis(ticks: list[int], maximum: int, ink: str) -> str:
    rows = ""
    for tick in ticks:
        y = BASELINE - (tick / maximum if maximum else 0) * PLOT_HEIGHT
        # star-history blanks the zero label so it does not collide with the x axis.
        label = " " if tick == 0 else str(tick)
        rows += (
            '<g class="tick">'
            f'<path stroke="currentColor" d="M0 {number(y)}h-1"/>'
            f'<text x="-7" fill="currentColor" dy=".32em" '
            f'style="font-family:{FONT_FAMILY};font-size:16px;fill:{ink}" '
            f'transform="translate(0 {number(y)})">{escape(label)}</text></g>'
        )
    return (
        '<g fill="none" class="yaxis" font-family="sans-serif" font-size="10" '
        'text-anchor="end">'
        f'<path stroke="currentColor" d="M-1 {number(BASELINE)}H.5V.5H-1" '
        f'class="domain" filter="url(#xkcdify)" style="stroke:{ink}"/>'
        f"{rows}</g>"
    )


def legend(repository: str, colors: dict) -> str:
    box = LEGEND_TEXT_ORIGIN + LEGEND_CHARACTER_WIDTH * len(repository)
    return (
        f'<rect width="{number(box)}" height="32" x="8" y="5" fill-opacity=".85" '
        f'stroke="{colors["ink"]}" stroke-width="2" filter="url(#xkcdify)" rx="5" '
        f'ry="5" style="fill:{colors["background"]}"/>'
        f'<rect width="8" height="8" x="15" y="17" filter="url(#xkcdify)" rx="2" '
        f'ry="2" style="fill:{colors["series"]}"/>'
        f'<text x="{LEGEND_TEXT_ORIGIN}" y="25" '
        f'style="font-size:15px;fill:{colors["ink"]}">{escape(repository)}</text>'
    )


def logo(avatar: str) -> str:
    if not avatar:
        return ""
    radius = LOGO_SIZE / 2
    return (
        f'<defs><clipPath id="{LOGO_CLIP_ID}">'
        f'<circle cx="{number(LOGO_X + radius)}" cy="{number(LOGO_Y + radius)}" '
        f'r="{number(radius)}"/></clipPath></defs>'
        f'<image width="{LOGO_SIZE}" height="{LOGO_SIZE}" x="{LOGO_X}" '
        f'y="{LOGO_Y}" clip-path="url(#{LOGO_CLIP_ID})" href="{escape(avatar, {chr(34): "&quot;"})}"/>'
    )


def titles(ink: str, avatar: str) -> str:
    return (
        f"{logo(avatar)}"
        f'<text x="50%" y="{TITLE_BASELINE}" '
        f'style="font-size:{TITLE_SIZE}px;font-weight:700;fill:{ink}" '
        f'text-anchor="middle">{escape(TITLE)}</text>'
        f'<text x="50%" y="{number(HEIGHT - 10)}" style="font-size:17px;fill:{ink}" '
        'text-anchor="middle">Date</text>'
        f'<text x="-217" y="20" dy=".75em" style="font-size:17px;fill:{ink}" '
        'text-anchor="end" transform="rotate(-90)">GitHub Stars</text>'
    )


def render(repository: str, timeline: dict, theme: str) -> str:
    points = downsample(timeline["points"])
    if not points:
        raise ChartError(f"no stargazer points to chart for {repository}")

    colors = palette_of(theme)
    start, end = points[0][0], points[-1][0]
    if end <= start:
        end = start + timedelta(days=1)

    maximum = max(timeline["total"], max(count for _, count in points))
    project = projector(start, end, maximum)
    curve = basis_path([project(moment, count) for moment, count in points])

    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" '
        f'height="{number(HEIGHT)}" style="stroke-width:3;'
        f'font-family:{FONT_FAMILY};background:{colors["background"]}">'
        f"<defs><style>{font_face()}</style></defs>"
        '<filter id="xkcdify" width="100%" height="100%" x="-5" y="-5" '
        'filterUnits="userSpaceOnUse">'
        '<feTurbulence baseFrequency=".05" result="noise" type="fractalNoise"/>'
        '<feDisplacementMap in="SourceGraphic" in2="noise" scale="5" '
        'xChannelSelector="R" yChannelSelector="G"/></filter>'
        f'<g pointer-events="all" transform="translate({PLOT_ORIGIN[0]} '
        f'{PLOT_ORIGIN[1]})">'
        f"{x_axis(time_ticks(start, end), project, colors['ink'])}"
        f"{y_axis(value_ticks(maximum), maximum, colors['ink'])}"
        f'<path fill="none" stroke="{colors["series"]}" d="{curve}" '
        'class="xkcd-chart-xyline" filter="url(#xkcdify)"/>'
        f"{legend(repository, colors)}"
        "</g>"
        f"{titles(colors['ink'], timeline.get('avatar', ''))}"
        "</svg>"
    )
