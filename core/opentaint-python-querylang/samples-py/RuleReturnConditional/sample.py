def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def _conditional_helper(src: str) -> str:
    if src != "":
        ret = src
    else:
        ret = "fallback"
    return ret


def _always_safe_helper(src: str) -> str:
    _ = src
    return "safe"


def Positive_returns_source_or_derived():
    sink(_conditional_helper(source()))


def Negative_always_safe():
    sink(_always_safe_helper(source()))
