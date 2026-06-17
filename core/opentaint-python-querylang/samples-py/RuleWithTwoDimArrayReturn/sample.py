from typing import List


def sink(data) -> None:
    pass


def Positive_list_list_str(a: str) -> List[List[str]]:
    sink(a)
    return [[a]]


def Negative_list_str(a: str) -> List[str]:
    sink(a)
    return [a]
