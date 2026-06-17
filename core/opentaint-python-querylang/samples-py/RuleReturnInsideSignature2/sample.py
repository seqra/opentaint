def pass_through(s: str) -> str:
    return s


def sink(data) -> None:
    pass


def Positive_simple():
    a = pass_through("data")
    sink(a)


def Negative_no_pass():
    sink("safe")
