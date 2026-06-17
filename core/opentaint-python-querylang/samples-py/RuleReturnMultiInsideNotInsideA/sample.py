def mk_type2(x: str) -> str:
    return x


def mk_type3(x: str) -> str:
    return x


def sanitize_a(x: str) -> str:
    return x


def Positive_simple() -> str:
    v2 = mk_type2("x")
    return mk_type3(v2)


def Negative_with_sanitize() -> str:
    v2 = mk_type2("x")
    cleaned = sanitize_a(v2)
    return mk_type3(cleaned)
