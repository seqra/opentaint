def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def other(s: str) -> None:
    pass


def Positive_simple():
    src = source()
    sink(src)


def Negative_other_sink():
    src = source()
    other(src)


def Negative_no_source():
    sink("safe")
