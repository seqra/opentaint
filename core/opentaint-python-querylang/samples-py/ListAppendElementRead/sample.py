def source() -> str:
    return "tainted"


def sink(x) -> None:
    pass


def Positive_append_element():
    # `lst.append(source())` routes taint through the unknown-method arg(0)->this default, but it
    # lands at `lst.append.$PIR_SELF.![mark]` (a spurious method-field on the receiver) instead of
    # on `lst`/`lst.[*]`, so the element read `lst[0]` misses it and the sink is (wrongly) not reported.
    lst = []
    lst.append(source())
    bar = lst[0]
    sink(bar)
