def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def Positive_simple():
    data = source()
    sink(data)


def Negative_constant():
    sink("Constant")
