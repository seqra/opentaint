def source() -> str:
    return "tainted"


def clean(data: str) -> str:
    return data


def f(data: str) -> None:
    pass


def Positive_simple():
    data = source()
    f(data)


def Negative_clean_first():
    data = source()
    cleaned = clean(data)
    f(cleaned)
