def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def clean(data: str) -> str:
    return data


def _nested_src() -> str:
    return source()


def _nested_sink(o: str) -> None:
    sink(o)


def Positive_simple():
    o = source()
    sink(o)


def Positive_clean_after_sink():
    o = source()
    sink(o)
    _ = clean(o)


def Positive_multiple_functions():
    o = _nested_src()
    _nested_sink(o)


def Negative_clean_before_sink():
    o = source()
    cleaned = clean(o)
    sink(cleaned)
