import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import rekey_holder as rh


def test_dump_width_matches_the_config_serialisation():
    # width=80 is what the checked-in config was written at; changing it
    # reflows unrelated `signature:` lines across ~14 files.
    assert rh.DUMP_WIDTH == 80


def test_collapse_rewrites_and_dedupes():
    doc = {"passThrough": [{
        "function": "java.lang.StringBuilder#append",
        "signature": "(char[]) java.lang.StringBuilder",
        "copy": [
            {"from": "arg(0)", "to": "this"},
            {"from": "arg(0)", "to": ["this", ".java.lang.CharSequence#<rule-storage>#java.lang.Object"]},
            {"from": ["arg(0)", "[*]"], "to": "this"},
        ],
    }]}
    out = rh.collapse(doc, {"java.lang.CharSequence"})
    copies = out["passThrough"][0]["copy"]
    assert copies == [
        {"from": "arg(0)", "to": "this"},
        {"from": ["arg(0)", "[*]"], "to": "this"},
    ]


def test_collapse_leaves_other_classes_alone():
    doc = {"passThrough": [{
        "function": "p.C#m",
        "copy": [{"from": "arg(0)", "to": ["this", ".p.D#<rule-storage>#java.lang.Object"]}],
    }]}
    out = rh.collapse(doc, {"p.C"})
    assert out["passThrough"][0]["copy"][0]["to"] == [
        "this", ".p.D#<rule-storage>#java.lang.Object"]


def test_entry_with_no_copies_left_is_dropped():
    doc = {"passThrough": [
        {"function": "p.C#m", "copy": [
            {"from": ["this", ".p.C#<rule-storage>#java.lang.Object"],
             "to": ["result", ".p.C#<rule-storage>#java.lang.Object"]},
            {"from": "this", "to": "result"},
        ]},
        {"function": "p.C#n", "copy": []},
    ]}
    out = rh.collapse(doc, {"p.C"})
    assert len(out["passThrough"]) == 1
    assert out["passThrough"][0]["copy"] == [{"from": "this", "to": "result"}]
