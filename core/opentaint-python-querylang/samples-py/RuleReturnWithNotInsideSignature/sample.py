def source() -> str:
    return "tainted"


def sink(data) -> None:
    pass


def clean(data: str) -> str:
    return data


def _returned() -> str:
    a = source()
    return a


def _cleaned_returned() -> str:
    a = source()
    return clean(a)


def Positive_simple():
    sink(_returned())


def Negative_cleaned():
    sink(_cleaned_returned())
