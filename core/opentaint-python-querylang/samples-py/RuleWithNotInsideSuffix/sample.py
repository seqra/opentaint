def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def suffix_clean(s: str) -> str:
    return s


def Positive_simple():
    data = source()
    sink(data)


def Negative_clean_first():
    data = source()
    cleaned = suffix_clean(data)
    sink(cleaned)
