def source() -> str:
    return "tainted"


def copy(s: str) -> str:
    return s


def sink(a, b) -> None:
    pass


def clean(a: str, b: str) -> str:
    return a + b


def Positive_simple():
    a = source()
    b = copy(a)
    sink(a, b)


def Positive_clean_after_sink():
    a = source()
    b = copy(a)
    sink(a, b)
    _ = clean(a, b)


def Negative_clean_before_sink():
    a = source()
    b = copy(a)
    cleaned = clean(a, b)
    _ = cleaned
