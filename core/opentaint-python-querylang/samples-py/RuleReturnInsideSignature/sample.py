def src(s: str) -> str:
    return s


def sink(data) -> None:
    pass


def Positive_simple():
    a = src("data")
    sink(a)


def Negative_no_src():
    sink("safe")
