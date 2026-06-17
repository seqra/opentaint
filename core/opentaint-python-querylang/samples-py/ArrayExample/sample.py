from typing import List


def source() -> List[str]:
    return ["tainted"]


def array_sink(data: List[str]) -> None:
    pass


def other_element_sink(data: List[str]) -> None:
    pass


def Positive_annotated_array_sink(param: List[str]) -> None:
    array_sink(param)


def Positive_annotated_other_sink(param: List[str]) -> None:
    other_element_sink(param)


def Positive_source_array_sink():
    param = source()
    array_sink(param)


def Positive_source_other_sink():
    param = source()
    other_element_sink(param)


def Negative_no_annotation_no_source(param) -> None:
    array_sink(param)


def Negative_no_sink():
    param = source()
    _ = param
