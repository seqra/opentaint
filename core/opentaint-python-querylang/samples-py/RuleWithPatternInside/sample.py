def source() -> str:
    return "tainted"


def source1() -> str:
    return "untainted"


def sink(data) -> None:
    pass


def Positive_simple():
    data = source()
    sink(data)


def Positive_with_ellipsis():
    data = source()
    _ = data + "x"
    sink(data)


def Negative_no_sink():
    data = source()
    _ = data


def Negative_no_source():
    data = source1()
    sink(data)
