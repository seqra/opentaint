def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def clean(data: str) -> str:
    return data


def Positive_simple():
    data = source()
    sink(data)


def Positive_with_ellipsis():
    data = source()
    _ = data + " noop"
    sink(data)


def Negative_cleaned():
    data = source()
    data = clean(data)
    sink(data)
