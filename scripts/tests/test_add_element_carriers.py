import sys, pathlib, copy
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import add_element_carriers as ac
import config_lint as cl


def test_adds_the_missing_element_edge_next_to_its_whole_copy():
    doc = {"passThrough": [{
        "function": "java.nio.ByteBuffer#wrap",
        "signature": "(byte[]) java.nio.ByteBuffer",
        "copy": [{"from": "arg(0)", "to": "result"}],
    }]}
    out, added = ac.add_carriers(doc, "x.yaml")
    assert added == 1
    assert out["passThrough"][0]["copy"] == [
        {"from": "arg(0)", "to": "result"},
        {"from": ["arg(0)", "[*]"], "to": "result"},
    ]


def test_is_idempotent():
    doc = {"passThrough": [{
        "function": "java.nio.ByteBuffer#wrap",
        "signature": "(byte[]) java.nio.ByteBuffer",
        "copy": [{"from": "arg(0)", "to": "result"},
                 {"from": ["arg(0)", "[*]"], "to": "result"}],
    }]}
    pristine = copy.deepcopy(doc)
    out, added = ac.add_carriers(copy.deepcopy(doc), "x.yaml")
    assert added == 0
    assert out == pristine


def test_is_idempotent_for_a_list_form_target():
    doc = {"passThrough": [{
        "function": "p.C#m",
        "signature": "(byte[]) void",
        "copy": [{"from": "arg(0)", "to": ["this", ".p.C#v#java.lang.String"]},
                 {"from": ["arg(0)", "[*]"], "to": ["this", ".p.C#v#java.lang.String"]}],
    }]}
    pristine = copy.deepcopy(doc)
    out, added = ac.add_carriers(copy.deepcopy(doc), "x.yaml")
    assert added == 0
    assert out == pristine


def test_leaves_array_to_array_copies_alone():
    doc = {"passThrough": [{
        "function": "p.C#copyOf",
        "signature": "(char[]) char[]",
        "copy": [{"from": "arg(0)", "to": "result"}],
    }]}
    out, added = ac.add_carriers(doc, "x.yaml")
    assert added == 0
    assert out == doc


def test_preserves_a_list_form_target():
    doc = {"passThrough": [{
        "function": "p.C#m",
        "signature": "(byte[]) void",
        "copy": [{"from": "arg(0)", "to": ["this", ".p.C#v#java.lang.String"]}],
    }]}
    out, added = ac.add_carriers(doc, "x.yaml")
    assert added == 1
    assert out["passThrough"][0]["copy"][1] == {
        "from": ["arg(0)", "[*]"], "to": ["this", ".p.C#v#java.lang.String"]}


def test_duplicate_whole_copies_need_only_one_carrier():
    # Two literally identical whole-copies each report their own I3 finding
    # (check_element_carrier does not dedupe by (frm, to)), but a single
    # carrier satisfies the "present" check for both -- added must be 1, not 2.
    doc = {"passThrough": [{
        "function": "java.nio.ByteBuffer#wrap",
        "signature": "(byte[]) java.nio.ByteBuffer",
        "copy": [{"from": "arg(0)", "to": "result"},
                 {"from": "arg(0)", "to": "result"}],
    }]}
    out, added = ac.add_carriers(doc, "x.yaml")
    assert added == 1
    assert out["passThrough"][0]["copy"] == [
        {"from": "arg(0)", "to": "result"},
        {"from": "arg(0)", "to": "result"},
        {"from": ["arg(0)", "[*]"], "to": "result"},
    ]
    e = cl.Entry("x.yaml", "java.nio.ByteBuffer#wrap", "(byte[]) java.nio.ByteBuffer",
                 [cl.Copy(tuple(c["from"]) if isinstance(c["from"], list) else (c["from"],),
                          tuple(c["to"]) if isinstance(c["to"], list) else (c["to"],))
                  for c in out["passThrough"][0]["copy"]])
    assert cl.check_element_carrier([e]) == []
