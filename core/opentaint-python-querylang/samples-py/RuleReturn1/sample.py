def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def _returned() -> str:
    a = source()
    return a


def _const_returned() -> str:
    _ = source()
    return "safe"


def Positive_simple():
    sink(_returned())


def Negative_constant_return():
    sink(_const_returned())
