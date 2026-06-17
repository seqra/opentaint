def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def clean(data: str) -> str:
    return data


def Positive_simple():
    o = source()
    sink(o)


def Positive_clean_after_sink():
    o = source()
    sink(o)
    _ = clean(o)


def Negative_clean_before_sink():
    o = source()
    cleaned = clean(o)
    sink(cleaned)
