def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def Positive_tainted():
    data = source()
    sink(data)              # tainted, not the allowed literal -> should fire


def Negative_allowed_constant():
    sink("ok")              # exactly the allowed literal "ok" -> excluded, should NOT fire


def Negative_other_constant():
    sink("nope")            # not tainted (a constant), also not "ok" -> should NOT fire
