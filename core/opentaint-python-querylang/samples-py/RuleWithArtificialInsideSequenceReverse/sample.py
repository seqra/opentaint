def f(x: str) -> None:
    pass


def g(x: str) -> None:
    pass


def h(x: str) -> None:
    pass


def clean(x: str) -> None:
    pass


def Positive_both_g_and_h_follow():
    x = "data"
    f(x)
    g(x)
    h(x)


def Negative_only_g_follows():
    x = "data"
    f(x)
    g(x)


def Negative_with_clean():
    x = "data"
    f(x)
    g(x)
    h(x)
    clean(x)
