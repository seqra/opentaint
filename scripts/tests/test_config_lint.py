import sys, pathlib, textwrap
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import config_lint as cl


def write(tmp_path, name, body):
    p = tmp_path / name
    p.write_text(textwrap.dedent(body))
    return str(tmp_path)


def test_arity_parses_string_signature():
    assert cl.arity("(java.lang.String, int) void") == 2
    assert cl.arity("() void") == 0
    assert cl.arity("(*) *") is None
    assert cl.arity(None) is None


def test_arg_range_flags_out_of_range_index(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          signature: (java.lang.String) void
          copy:
          - from: arg(0)
            to: this
          - from: arg(1)
            to: this
        """)
    findings = cl.check_arg_range(cl.load_entries(root))
    assert [f.code for f in findings] == ["I5"]
    assert "arg(1)" in findings[0].detail


def test_element_safe_is_lenient_on_object_and_unknown():
    assert cl.is_element_safe(None)
    assert cl.is_element_safe("java.lang.Object")
    assert cl.is_element_safe("byte[]")
    assert cl.is_element_safe("java.util.List")
    assert not cl.is_element_safe("java.lang.String")
    assert not cl.is_element_safe("int")


def test_element_on_scalar_result_is_flagged(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#charAt
          signature: (int) char
          copy:
          - from: this
            to:
            - result
            - '[*]'
        """)
    findings = cl.check_element_targets(cl.load_entries(root))
    assert [f.code for f in findings] == ["I4"]


def test_element_on_array_param_is_allowed(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#getChars
          signature: (char[]) void
          copy:
          - from: this
            to:
            - arg(0)
            - '[*]'
        """)
    assert cl.check_element_targets(cl.load_entries(root)) == []
