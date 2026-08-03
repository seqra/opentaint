import math
import re
import sys
import xml.etree.ElementTree as ET

from . import ChartError


SVG_NAMESPACE = "http://www.w3.org/2000/svg"
DEFAULT_BACKGROUNDS = {"light": "#ffffff", "dark": "#0d1117"}
DEFAULT_SIZE = (800, 534)

BACKGROUND_RE = re.compile(r"background:\s*(#[0-9a-fA-F]{3,8}|[a-zA-Z]+)")
WIDTH_RE = re.compile(r'\bwidth="([0-9.]+)"')
HEIGHT_RE = re.compile(r'\bheight="([0-9.]+)"')
CSS_URL_RE = re.compile(r"url\(\s*(['\"]?)(.*?)\1\s*\)", re.IGNORECASE | re.DOTALL)
CSS_URL_START_RE = re.compile(r"url\s*\(", re.IGNORECASE)
UNSAFE_CSS_RE = re.compile(
    r"@import|expression\s*\(|behavior\s*:|"
    r"(?:file|ftp|https?|javascript|vbscript)\s*:",
    re.IGNORECASE,
)
SAFE_RASTER_DATA_RE = re.compile(
    r"^data:image/(?:gif|jpeg|png|webp)(?:[;,])", re.IGNORECASE
)
SAFE_FONT_DATA_RE = re.compile(
    r"^data:(?:application/font-woff|font/woff2?)(?:[;,])", re.IGNORECASE
)
DANGEROUS_ELEMENTS = {
    "a",
    "animate",
    "animatemotion",
    "animatetransform",
    "discard",
    "embed",
    "foreignobject",
    "handler",
    "iframe",
    "listener",
    "object",
    "script",
    "set",
}


def split_xml_name(name: str) -> tuple[str, str]:
    if name.startswith("{"):
        namespace, local_name = name[1:].split("}", 1)
        return namespace, local_name
    return "", name


def validate_resource_reference(reference: str, *, allow_font: bool) -> None:
    reference = reference.strip()
    if reference.startswith("#") or SAFE_RASTER_DATA_RE.match(reference):
        return
    if allow_font and SAFE_FONT_DATA_RE.match(reference):
        return
    raise ChartError(f"unsafe SVG resource reference: {reference[:80]!r}")


def validate_css(css: str) -> None:
    if "\\" in css:
        raise ChartError("SVG CSS escapes are not allowed")
    if UNSAFE_CSS_RE.search(css):
        raise ChartError("SVG CSS contains an active or external construct")

    matches = list(CSS_URL_RE.finditer(css))
    if len(matches) != len(CSS_URL_START_RE.findall(css)):
        raise ChartError("SVG CSS contains a malformed url() reference")
    for match in matches:
        validate_resource_reference(match.group(2), allow_font=True)


def sanitize_svg(svg: str) -> str:
    lowered = svg.lower()
    if "<!doctype" in lowered or "<!entity" in lowered:
        raise ChartError("SVG document type and entity declarations are not allowed")

    try:
        root = ET.fromstring(svg)
    except ET.ParseError as error:
        raise ChartError(f"body is not well-formed SVG XML: {error}") from error

    namespace, root_name = split_xml_name(root.tag)
    if namespace != SVG_NAMESPACE or root_name.lower() != "svg":
        raise ChartError("document root is not an SVG element in the SVG namespace")

    for element in root.iter():
        element_namespace, element_name = split_xml_name(element.tag)
        if element_namespace != SVG_NAMESPACE:
            raise ChartError(
                f"foreign XML namespace on <{element_name}> is not allowed"
            )
        if element_name.lower() in DANGEROUS_ELEMENTS:
            raise ChartError(f"active SVG element <{element_name}> is not allowed")

        for attribute_name, value in element.attrib.items():
            _, local_name = split_xml_name(attribute_name)
            lowered_name = local_name.lower()
            if lowered_name.startswith("on"):
                raise ChartError(f"SVG event attribute {local_name!r} is not allowed")
            if lowered_name in {"href", "src"}:
                validate_resource_reference(value, allow_font=False)
            if lowered_name == "style" or CSS_URL_START_RE.search(value):
                validate_css(value)

        if element_name.lower() == "style":
            validate_css(element.text or "")

    ET.register_namespace("", SVG_NAMESPACE)
    return ET.tostring(root, encoding="unicode")


def background_of(svg: str, theme: str) -> str:
    match = BACKGROUND_RE.search(svg[:1024])
    if match:
        return match.group(1)
    print(
        f"::warning::No background declared in the {theme} chart; "
        f"falling back to {DEFAULT_BACKGROUNDS[theme]}",
        file=sys.stderr,
    )
    return DEFAULT_BACKGROUNDS[theme]


def viewport_of(svg: str, theme: str) -> tuple[int, int]:
    root = svg[:1024]
    width, height = WIDTH_RE.search(root), HEIGHT_RE.search(root)
    if width and height:
        return math.ceil(float(width.group(1))), math.ceil(float(height.group(1)))
    print(
        f"::warning::No intrinsic size on the {theme} chart; "
        f"falling back to {DEFAULT_SIZE[0]}x{DEFAULT_SIZE[1]}",
        file=sys.stderr,
    )
    return DEFAULT_SIZE
