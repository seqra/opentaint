from typing import List


def sink(data) -> None:
    pass


def Positive_list_of_lists(a: str) -> List[List[str]]:
    sink(a)
    return [[a]]


def Negative_plain_list(a: str) -> List[str]:
    sink(a)
    return [a]
