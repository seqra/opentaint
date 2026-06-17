def mk_type2(s: str) -> str:
    return s


def mk_type3(s: str) -> str:
    return s


def mk_type1_from_type3(s: str) -> str:
    return s


def Positive_simple() -> str:
    src = "x"
    v2 = mk_type2(src)
    v3 = mk_type3(v2)
    out = mk_type1_from_type3(v3)
    return out


def Negative_no_mk_type2() -> str:
    return mk_type1_from_type3(mk_type3("x"))
