class StaticConstantStorage:
    FIRST = "first"
    SECOND = "second"


def sink(data) -> None:
    pass


def Positive_first():
    sink(StaticConstantStorage.FIRST)


def Negative_second():
    sink(StaticConstantStorage.SECOND)
