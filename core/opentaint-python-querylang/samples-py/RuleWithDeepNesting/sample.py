from typing import List


def sink(data) -> None:
    pass


def Positive_nested_list(a: str) -> List[List[str]]:
    sink(a)
    return [[a]]


def Negative_flat_list(a: str) -> List[str]:
    sink(a)
    return [a]
