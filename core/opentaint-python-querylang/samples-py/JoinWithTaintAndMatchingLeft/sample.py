def get_untrusted_input() -> str:
    return "untrusted"


def process_input(x: str) -> str:
    return x


def transform_data(x: str) -> str:
    return x


def execute_dangerous(x: str) -> None:
    pass


def Positive_taint_flow():
    untrusted = get_untrusted_input()
    processed = process_input(untrusted)
    result = transform_data(processed)
    execute_dangerous(result)


def Negative_missing_untrusted():
    safe = "safe"
    processed = process_input(safe)
    result = transform_data(processed)
    execute_dangerous(result)
