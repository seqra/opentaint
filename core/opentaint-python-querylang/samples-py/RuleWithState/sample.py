def f() -> str:
    return "fstate"


def g(x: str) -> None:
    pass


def Positive_simple():
    t = f()
    g(t)


def Negative_only_f():
    _ = f()


def Negative_only_g():
    g("safe")
