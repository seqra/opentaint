def new_object_mapper() -> str:
    return "om"


def enable_default_typing(om: str) -> str:
    return om


def read_value(om: str) -> None:
    pass


def Positive_simple():
    om = new_object_mapper()
    tainted = enable_default_typing(om)
    read_value(tainted)


def Negative_no_enable():
    om = new_object_mapper()
    read_value(om)
