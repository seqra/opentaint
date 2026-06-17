def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def sanitize(s: str) -> str:
    return s


def Positive_no_sanitize():
    src = source()
    ret = src
    sink(ret)


def Negative_with_sanitize():
    src = source()
    ret = src
    cleaned = sanitize(ret)
    sink(cleaned)
