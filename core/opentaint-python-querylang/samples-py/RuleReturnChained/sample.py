def mk_type2(s: str) -> str:
    return s


def mk_type3(s: str) -> str:
    return s


def mk_type1(s: str) -> str:
    return s


def Positive_simple() -> str:
    src = "x"
    v3 = mk_type3(mk_type2(src))
    out = mk_type1(v3)
    return out


def Negative_no_mk_type1() -> str:
    return mk_type3(mk_type2("x"))
