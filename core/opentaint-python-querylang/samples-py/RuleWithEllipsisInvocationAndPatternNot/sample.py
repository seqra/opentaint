def src() -> str:
    return "tainted"


def get_obj_good(x: str) -> str:
    return x


def get_obj_bad(x: str) -> str:
    return x


def sink(data) -> None:
    pass


def Positive_simple():
    d = src()
    s = get_obj_good(d)
    sink(s)


def Negative_bad_path():
    d = src()
    s = get_obj_bad(d)
    sink(s)
