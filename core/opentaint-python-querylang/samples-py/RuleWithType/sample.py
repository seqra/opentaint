def make_simple() -> str:
    return "simple"


def make_other() -> str:
    return "other"


def foo_simple(s: str) -> None:
    pass


def foo_other(s: str) -> None:
    pass


def Positive_simple():
    s = make_simple()
    foo_simple(s)


def Negative_other_type():
    s = make_other()
    foo_other(s)
