def new_cookie(name: str, value: str) -> dict:
    return {"name": name, "value": value}


def set_secure(cookie: dict) -> dict:
    cookie["secure"] = True
    return cookie


def add_cookie(cookie: dict) -> None:
    pass


def Positive_insecure_cookie():
    c = new_cookie("sid", "abc")
    add_cookie(c)


def Negative_secure_cookie():
    c = new_cookie("sid", "abc")
    c = set_secure(c)
    add_cookie(c)
