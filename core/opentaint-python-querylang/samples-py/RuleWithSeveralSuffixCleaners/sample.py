def source() -> str:
    return "tainted"


def clean1(s: str) -> str:
    return s


def clean2(s: str) -> str:
    return s


def f(s: str) -> None:
    pass


def Positive_simple():
    data = source()
    f(data)


def Negative_with_clean1():
    data = source()
    cleaned = clean1(data)
    f(cleaned)


def Negative_with_clean2():
    data = source()
    cleaned = clean2(data)
    f(cleaned)
