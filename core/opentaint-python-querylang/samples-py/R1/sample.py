def foo(x) -> str:
    return str(x)


def Positive_non_object_param(arg: str) -> str:
    x = foo(arg)
    return x


def Negative_object_param(arg: object) -> object:
    x = foo(arg)
    return x
