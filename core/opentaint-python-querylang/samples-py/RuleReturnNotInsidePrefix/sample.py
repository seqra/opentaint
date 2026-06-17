def mk_type2(x: str) -> str:
    return x


def mk_type3(x: str) -> str:
    return x


def mk_type1(x: str) -> str:
    return x


def clean(x: str) -> str:
    return x


def Positive_simple() -> str:
    s = mk_type2("x")
    return mk_type1(mk_type3(s))


def Negative_with_clean() -> str:
    s = mk_type2("x")
    cleaned = clean(s)
    return mk_type1(mk_type3(cleaned))
