def f(data):
    pass


def clean(data):
    pass


def Positive_simple():
    data = ""
    f(data)


def Negative_no_f():
    print("Hello!")


def Negative_clean_first():
    data = ""
    clean(data)
    f(data)


def Negative_clean_second():
    data = ""
    f(data)
    clean(data)
