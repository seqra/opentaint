from typing import Dict


def sink(data) -> None:
    pass


def Positive_with_dict_param(m: Dict[str, object], a: str) -> None:
    sink(a)


def Negative_no_dict_param(a: str) -> None:
    sink(a)
