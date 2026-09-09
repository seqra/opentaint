package org.opentaint.ir.test.python.tier1

import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

@Tag("tier1")
class BenchmarkTest : BenchmarkTestBase() {

    @Test fun `benchmark - click`() = analyzePkg("click", "3.13", 17, 67, 109)
    @Test fun `benchmark - requests`() = analyzePkg("requests", "3.13", 18, 44, 72)
    @Test fun `benchmark - attrs`() = analyzePkg("attr", "3.13", 13, 35, 91)
    @Test fun `benchmark - typer`() = analyzePkg("typer", "3.13", 16, 36, 86)
    @Test fun `benchmark - rich`() = analyzePkg("rich", "3.13", 100, 173, 93, recursive = true)
    @Test fun `benchmark - pygments`() = analyzePkg("pygments", "3.13", 338, 752, 112, recursive = true)
    @Test fun `benchmark - urllib3`() = analyzePkg("urllib3", "3.13", 36, 96, 91, recursive = true)
    @Test fun `benchmark - packaging`() = analyzePkg("packaging", "3.13", 15, 55, 105)
    @Test fun `benchmark - cryptography`() = analyzePkg("cryptography", "3.13", 72, 262, 102, recursive = true)
    @Test fun `benchmark - more-itertools`() = analyzePkg("more_itertools", "3.13", 3, 12, 172)
    @Test fun `benchmark - idna`() = analyzePkg("idna", "3.13", 8, 9, 110)
    @Test fun `benchmark - charset-normalizer`() = analyzePkg("charset_normalizer", "3.13", 10, 13, 46)
    @Test fun `benchmark - markdown-it`() = analyzePkg("markdown_it", "3.13", 66, 24, 90, recursive = true)
    @Test fun `benchmark - grpc`() = analyzePkg("grpc", "3.13", 56, 203, 206, recursive = true)
    @Test fun `benchmark - google-protobuf`() = analyzePkg("google.protobuf", "3.13", 58, 81, 288, recursive = true)
    @Test fun `benchmark - mypy`() = analyzePkg("mypy", "3.13", 195, 551, 1274, recursive = true)
    @Test fun `benchmark - shellingham`() = analyzePkg("shellingham", "3.13", 3, 2, 7)
    @Test fun `benchmark - mdurl`() = analyzePkg("mdurl", "3.13", 6, 2, 7)
    @Test fun `benchmark - markupsafe`() = analyzePkg("markupsafe", "3.13", 2, 5, 5)

    @Test fun `benchmark - flask`() = analyzePkg("flask", "3.13", 18, 30, 53)
    @Test fun `benchmark - django`() = analyzePkg("django", "3.13", 899, 1907, 1220, recursive = true)
    @Test fun `benchmark - fastapi`() = analyzePkg("fastapi", "3.13", 48, 99, 113, recursive = true)
    @Test fun `benchmark - starlette`() = analyzePkg("starlette", "3.13", 34, 104, 27, recursive = true)
    @Test fun `benchmark - werkzeug`() = analyzePkg("werkzeug", "3.13", 52, 177, 135, recursive = true)
    @Test fun `benchmark - jinja2`() = analyzePkg("jinja2", "3.13", 25, 152, 159, recursive = true)
    @Test fun `benchmark - tornado`() = analyzePkg("tornado", "3.13", 73, 544, 154, recursive = true)
    @Test fun `benchmark - falcon`() = analyzePkg("falcon", "3.13", 102, 223, 156, recursive = true)
    @Test fun `benchmark - bottle`() = analyzePkg("bottle", "3.13", 1, 67, 40)
    @Test fun `benchmark - pyramid`() = analyzePkg("pyramid", "3.13", 61, 288, 174, recursive = true)
    @Test fun `benchmark - sanic`() = analyzePkg("sanic", "3.13", 132, 198, 107, recursive = true)
    @Test fun `benchmark - aiohttp`() = analyzePkg("aiohttp", "3.13", 55, 306, 109, recursive = true)
    @Test fun `benchmark - celery`() = analyzePkg("celery", "3.13", 161, 276, 523, recursive = true)

    @Test fun `benchmark - pydantic`() = analyzePkg("pydantic", "3.13", 105, 359, 537, recursive = true)
    @Test fun `benchmark - sqlalchemy`() = analyzePkg("sqlalchemy", "3.13", 256, 1723, 1058, recursive = true)
    @Test fun `benchmark - marshmallow`() = analyzePkg("marshmallow", "3.13", 14, 63, 31, recursive = true)

    @Test fun `benchmark - httpx`() = analyzePkg("httpx", "3.13", 23, 85, 67, recursive = true)
    @Test fun `benchmark - httpcore`() = analyzePkg("httpcore", "3.13", 31, 85, 19, recursive = true)

    @Test fun `benchmark - yaml`() = analyzePkg("yaml", "3.13", 17, 88, 26, recursive = true)
    @Test fun `benchmark - mako`() = analyzePkg("mako", "3.13", 33, 91, 87, recursive = true)
    @Test fun `benchmark - markdown`() = analyzePkg("markdown", "3.13", 33, 110, 66, recursive = true)
    @Test fun `benchmark - tqdm`() = analyzePkg("tqdm", "3.13", 31, 37, 43, recursive = true)
    @Test fun `benchmark - pycparser`() = analyzePkg("pycparser", "3.13", 17, 83, 44, recursive = true)
    @Test fun `benchmark - pyparsing`() = analyzePkg("pyparsing", "3.13", 17, 87, 62, recursive = true)
    @Test fun `benchmark - pathspec`() = analyzePkg("pathspec", "3.13", 31, 26, 20, recursive = true)
    @Test fun `benchmark - typeguard`() = analyzePkg("typeguard", "3.13", 12, 17, 55, recursive = true)
    @Test fun `benchmark - anyio`() = analyzePkg("anyio", "3.13", 42, 163, 94, recursive = true)
    @Test fun `benchmark - filelock`() = analyzePkg("filelock", "3.13", 10, 18, 4, recursive = true)
    @Test fun `benchmark - lxml`() = analyzePkg("lxml", "3.13", 29, 52, 132, recursive = true)
}
