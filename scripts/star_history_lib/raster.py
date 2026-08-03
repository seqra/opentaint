import html
import json
import os
import subprocess
import tempfile
from pathlib import Path

from . import ChartError


CSP = (
    "default-src 'none'; img-src 'self' data:; "
    "style-src 'unsafe-inline'; font-src data:"
)


def write_raster_page(
    svg_path: str, background: str, width: int, height: int
) -> str:
    page_path = f"{svg_path}.html"
    image_name = html.escape(os.path.basename(svg_path), quote=True)
    safe_background = html.escape(background, quote=True)
    document = f"""<!doctype html>
<html><head>
<meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="{CSP}">
<style>
html,body{{
  margin:0;
  width:100%;
  height:100%;
  overflow:hidden;
  background:{safe_background};
}}
img{{display:block;width:100%;height:100%;}}
</style>
</head><body>
<img src="{image_name}" width="{width}" height="{height}" alt="">
</body></html>
"""
    with open(page_path, "w", encoding="utf-8") as handle:
        handle.write(document)
    return page_path


def load_manifest(path: str) -> dict:
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def asset_paths(path: str) -> list[str]:
    return load_manifest(path)["assets"]


def rasterize(path: str, chrome: str, scale: str) -> None:
    for chart in load_manifest(path)["charts"]:
        png = Path(chart["png"]).resolve()
        page = Path(chart["raster_page"]).resolve()
        with tempfile.TemporaryDirectory() as profile:
            subprocess.run(
                [
                    chrome,
                    "--headless",
                    "--disable-gpu",
                    "--disable-dev-shm-usage",
                    "--hide-scrollbars",
                    f"--user-data-dir={profile}",
                    f"--force-device-scale-factor={scale}",
                    "--virtual-time-budget=10000",
                    f"--window-size={chart['width']},{chart['height']}",
                    f"--screenshot={png}",
                    page.as_uri(),
                ],
                check=True,
            )
        if not png.is_file() or png.stat().st_size == 0:
            raise ChartError(f"Chrome produced no screenshot for {chart['theme']}")
