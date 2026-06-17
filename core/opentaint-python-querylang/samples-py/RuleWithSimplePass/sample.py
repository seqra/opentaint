def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def pass_through(value: str) -> str:
    return value


def Positive_simple():
    data = source()
    other = pass_through(data)
    sink(other)


def Negative_no_pass():
    data = source()
    _ = data
    sink("constant")
