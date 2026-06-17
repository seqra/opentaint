class DataObj:
    def to_str(self) -> str:
        return "data"


def source() -> DataObj:
    return DataObj()


def sink(data: str) -> None:
    pass


def Positive_direct_chain():
    a = source()
    b = a.to_str()
    sink(b)


def Positive_intermediate_chain():
    a = source()
    obj = a
    b = obj.to_str()
    sink(b)


def Negative_no_source():
    a = DataObj()
    b = a.to_str()
    sink(b)
