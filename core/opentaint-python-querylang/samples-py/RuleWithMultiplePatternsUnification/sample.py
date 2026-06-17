def mk_type2(s: str) -> str:
    return s


def new_type3(s: str) -> str:
    return s


def Positive_simple() -> str:
    src = "x"
    v2 = mk_type2(src)
    out = new_type3(v2)
    return out


def Negative_no_mk_type2() -> str:
    src = "x"
    return new_type3(src)
