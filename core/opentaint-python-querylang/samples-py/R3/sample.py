def source() -> str:
    return "tainted"


def bar(data: str) -> str:
    return data


def Positive_simple():
    x = source()
    _ = bar(x)


def Negative_no_source():
    _ = bar("safe")
