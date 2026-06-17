def source() -> str:
    return "tainted"


def sink1(s: str) -> None:
    pass


def sink2(s: str) -> None:
    pass


def Positive_sink1():
    data = source()
    sink1(data)


def Positive_sink2():
    data = source()
    sink2(data)


def Negative_no_source():
    sink1("safe")
