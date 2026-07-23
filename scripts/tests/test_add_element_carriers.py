import sys, pathlib, copy
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import add_element_carriers as ac


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
