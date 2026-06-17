from typing import List


def sink(data) -> None:
    pass


def Positive_list_str_return(a: str) -> List[str]:
    sink(a)
    return [a]


def Negative_str_return(a: str) -> str:
    sink(a)
    return a
