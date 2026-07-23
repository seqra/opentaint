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


def test_missing_element_carrier_is_flagged(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#append
          signature: (char[]) p.C
          copy:
          - from: arg(0)
            to: this
        """)
    findings = cl.check_element_carrier(cl.load_entries(root))
    assert [f.code for f in findings] == ["I3"]
    assert "arg(0)" in findings[0].detail


def test_present_element_carrier_passes(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#append
          signature: (char[]) p.C
          copy:
          - from: arg(0)
            to: this
          - from:
            - arg(0)
            - '[*]'
            to: this
        """)
    assert cl.check_element_carrier(cl.load_entries(root)) == []


def test_array_to_array_needs_no_carrier(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#copyOf
          signature: (char[]) char[]
          copy:
          - from: arg(0)
            to: result
        """)
    assert cl.check_element_carrier(cl.load_entries(root)) == []


def test_object_typed_slot_target_needs_no_carrier(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#addAll
          signature: (java.lang.Object[]) void
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#items#java.lang.Object
        """)
    assert cl.check_element_carrier(cl.load_entries(root)) == []


def test_scalar_typed_slot_target_needs_a_carrier(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setNames
          signature: (java.lang.String[]) void
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#name#java.lang.String
        """)
    findings = cl.check_element_carrier(cl.load_entries(root))
    assert [f.code for f in findings] == ["I3"]


def test_property_extraction():
    assert cl.property_of("getResponseBody") == "responsebody"
    assert cl.property_of("setPath") == "path"
    assert cl.property_of("addRequestHeader") == "requestheader"
    assert cl.property_of("toString") is None


ALLOW = {"renderers": ["toString"], "source_fed_slots": []}


def test_shared_slot_across_properties_is_flagged(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#bag#java.lang.Object
        - function: p.C#getResponseBody
          copy:
          - from:
            - this
            - .p.C#bag#java.lang.Object
            to: result
        """)
    findings = cl.check_shared_slot(cl.load_entries(root), ALLOW)
    assert [f.code for f in findings] == ["I1"]
    assert "setPath" in findings[0].detail and "getResponseBody" in findings[0].detail


def test_same_property_through_one_slot_is_fine(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#path#java.lang.Object
        - function: p.C#getPath
          copy:
          - from:
            - this
            - .p.C#path#java.lang.Object
            to: result
        """)
    assert cl.check_shared_slot(cl.load_entries(root), ALLOW) == []


def test_renderer_reading_every_slot_is_exempt(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#path#java.lang.Object
        - function: p.C#toString
          copy:
          - from:
            - this
            - .p.C#path#java.lang.Object
            to: result
        """)
    assert cl.check_shared_slot(cl.load_entries(root), ALLOW) == []


def test_write_only_slot_is_flagged(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """)
    findings = cl.check_orphan_slots(cl.load_entries(root), ALLOW)
    assert [f.code for f in findings] == ["I2"]
    assert "never read" in findings[0].detail


def test_container_role_slot_is_not_a_leak(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#addAll
          copy:
          - from: arg(0)
            to:
            - this
            - .java.lang.Iterable#Element#java.lang.Object
        - function: p.C#getFirst
          copy:
          - from:
            - this
            - .java.lang.Iterable#Element#java.lang.Object
            to: result
        """)
    assert cl.check_shared_slot(cl.load_entries(root), ALLOW) == []


def test_allowlisted_shared_slot_is_not_a_leak(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#bag#java.lang.Object
        - function: p.C#getResponseBody
          copy:
          - from:
            - this
            - .p.C#bag#java.lang.Object
            to: result
        """)
    allow = dict(ALLOW, shared_slots=[".p.C#bag#java.lang.Object"])
    assert cl.check_shared_slot(cl.load_entries(root), allow) == []


def test_capitalised_role_is_shared_by_design(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setBody
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#Body#java.lang.Object
        - function: p.C#getPayload
          copy:
          - from:
            - this
            - .p.C#Body#java.lang.Object
            to: result
        """)
    assert cl.check_shared_slot(cl.load_entries(root), ALLOW) == []


def test_camelcase_role_named_value_is_still_checked(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setValue
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#value#java.lang.Object
        - function: p.C#getPassword
          copy:
          - from:
            - this
            - .p.C#value#java.lang.Object
            to: result
        """)
    findings = cl.check_shared_slot(cl.load_entries(root), ALLOW)
    assert [f.code for f in findings] == ["I1"]


def test_changed_only_splits_failures_from_reports(tmp_path):
    root = write(tmp_path, "touched.yaml", """
        passThrough:
        - function: p.C#m
          signature: () void
          copy:
          - from: arg(0)
            to: this
        """)
    (tmp_path / "untouched.yaml").write_text(
        "passThrough:\n- function: p.D#m\n  signature: () void\n  copy:\n"
        "  - from: arg(0)\n    to: this\n")
    allow = tmp_path / "allow.yaml"
    allow.write_text("renderers: []\nsource_fed_slots: []\n")
    failures, reports = cl.run(root, str(allow), changed={"touched.yaml"}, gate_i6=False)
    assert [f.file for f in failures] == ["touched.yaml"]
    assert [f.file for f in reports] == ["untouched.yaml"]


def test_i6_gate_flags_rule_storage(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#m
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#<rule-storage>#java.lang.Object
        """)
    allow = tmp_path / "allow.yaml"
    allow.write_text("renderers: []\nsource_fed_slots: []\n")
    failures, _ = cl.run(root, str(allow), changed=None, gate_i6=True)
    assert any(f.code == "I6" for f in failures)
