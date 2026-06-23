def foo(data):
    return None


def positive_method(arg):
    x = foo(None)
    return x


def Positive_entrypoint():
    positive_method("data")


def negative_method(arg):
    x = foo(arg)
    return x


def Negative_entrypoint():
    negative_method("data")
