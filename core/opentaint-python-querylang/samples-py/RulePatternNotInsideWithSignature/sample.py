def sink(data):
    pass


def negative_simple_method(src):
    sink(src)


def Negative_simple():
    negative_simple_method("data")


def positive_method(src):
    sink("unsafe")


def Positive_entrypoint():
    positive_method("data")
