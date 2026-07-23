import subprocess
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


def test_class_scoped_renderer_exempts_only_that_class(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#bag#java.lang.Object
        - function: p.C#getInstance
          copy:
          - from:
            - this
            - .p.C#bag#java.lang.Object
            to: result
        """)
    allow = dict(ALLOW, renderers=["p.C#getInstance"])
    assert cl.check_shared_slot(cl.load_entries(root), allow) == []


def test_class_scoped_renderer_does_not_exempt_other_classes(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.D#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.D#bag#java.lang.Object
        - function: p.D#getInstance
          copy:
          - from:
            - this
            - .p.D#bag#java.lang.Object
            to: result
        """)
    allow = dict(ALLOW, renderers=["p.C#getInstance"])
    findings = cl.check_shared_slot(cl.load_entries(root), allow)
    assert [f.code for f in findings] == ["I1"]


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


def test_orphan_finding_is_attributed_to_every_participating_file(tmp_path):
    # Two files write the same slot and nobody reads it anywhere: the finding
    # must not be pinned to one arbitrary file (e.g. sorted()[0]) -- a
    # --changed run touching either file must catch it.
    a = tmp_path / "a.yaml"
    a.write_text(textwrap.dedent("""
        passThrough:
        - function: p.C#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """))
    b = tmp_path / "b.yaml"
    b.write_text(textwrap.dedent("""
        passThrough:
        - function: p.D#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """))
    findings = cl.check_orphan_slots(cl.load_entries(str(tmp_path)), ALLOW)
    assert sorted(f.file for f in findings) == ["a.yaml", "b.yaml"]
    assert len({f.detail for f in findings}) == 1, "detail text should be identical across files"
    assert all(f.code == "I2" for f in findings)


def test_orphan_finding_attribution_reaches_run_with_changed_scoped_to_one_file(tmp_path):
    # The point of Hole 4: a --changed run naming only the file that is NOT
    # the arbitrary sorted()[0] pick must still see (and enforce) the finding.
    a = tmp_path / "a.yaml"
    a.write_text(textwrap.dedent("""
        passThrough:
        - function: p.C#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """))
    b = tmp_path / "b.yaml"
    b.write_text(textwrap.dedent("""
        passThrough:
        - function: p.D#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """))
    allow_path = tmp_path / "allow.yaml"
    allow_path.write_text("renderers: []\nsource_fed_slots: []\n")
    # "b.yaml" sorts after "a.yaml", so an arbitrary sorted()[0] pick would
    # attribute the finding only to a.yaml and this --changed run would miss it.
    failures, _, _ = cl.run(str(tmp_path), str(allow_path), changed={"b.yaml"}, gate_i6=False)
    assert any(f.code == "I2" for f in failures)


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


def test_map_form_literal_name_participates_in_shared_slot(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#bag#java.lang.Object
        - function:
            package: p
            class: C
            name: getResponseBody
          copy:
          - from:
            - this
            - .p.C#bag#java.lang.Object
            to: result
        """)
    findings = cl.check_shared_slot(cl.load_entries(root), ALLOW)
    assert [f.code for f in findings] == ["I1"]
    assert "setPath" in findings[0].detail and "getResponseBody" in findings[0].detail


def test_map_form_pattern_name_is_not_a_named_property_for_shared_slot(tmp_path):
    # A regex method-name entry must never be paired against a named property
    # as a cross-property leak: the pattern isn't a single property accessor.
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#setPath
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#bag#java.lang.Object
        - function:
            package: p
            class: C
            name:
              pattern: get.*
          copy:
          - from:
            - this
            - .p.C#bag#java.lang.Object
            to: result
        """)
    assert cl.check_shared_slot(cl.load_entries(root), ALLOW) == []


def test_map_form_pattern_name_still_counts_for_orphan(tmp_path):
    # Even though a pattern-name entry is not a "property" for I1 purposes, it
    # is still a real reader/writer for I2 orphan-slot purposes.
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function:
            package: p
            class: C
            name:
              pattern: set.*
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """)
    findings = cl.check_orphan_slots(cl.load_entries(root), ALLOW)
    assert [f.code for f in findings] == ["I2"]
    assert "never read" in findings[0].detail


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
    failures, reports, preexisting = cl.run(root, str(allow), changed={"touched.yaml"}, gate_i6=False)
    assert [f.file for f in failures] == ["touched.yaml"]
    assert [f.file for f in reports] == ["untouched.yaml"]
    assert preexisting == []


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
    failures, _, _ = cl.run(root, str(allow), changed=None, gate_i6=True)
    assert any(f.code == "I6" for f in failures)


def test_dict_signature_has_unknown_arity():
    # A dict signature constrains selected positions; it is not a full
    # parameter list, so no arg index can be proven out of range.
    assert cl.arity({"params": [{"index": 1, "type": "java.lang.String"}]}) is None
    assert cl.arity({"return": "java.lang.String"}) is None


def test_dict_signature_arg_is_not_flagged_out_of_range(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#toJson
          signature:
            params:
            - index: 1
              type: p.Writer
          copy:
          - from: arg(1)
            to: this
        """)
    assert cl.check_arg_range(cl.load_entries(root)) == []


def test_dict_signature_type_is_keyed_by_declared_index(tmp_path):
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#m
          signature:
            params:
            - index: 1
              type: java.lang.String[]
          copy:
          - from: arg(0)
            to: this
        """)
    entry = cl.load_entries(root)[0]
    assert cl.position_type(entry, ("arg(1)",)) == "java.lang.String[]"
    assert cl.position_type(entry, ("arg(0)",)) is None


def test_main_rejects_a_missing_config_root(tmp_path, capsys):
    rc = cl.main(["--root", str(tmp_path / "nope"),
                  "--allowlist", str(tmp_path / "allow.yaml")])
    assert rc == 2
    assert "config root not found" in capsys.readouterr().err


def test_main_rejects_an_empty_changed_list(tmp_path, capsys):
    # --changed with no arguments (nargs="*" -> []) must not silently mean
    # "nothing changed, demote every finding to reported, exit 0" -- a CI
    # file-list glob that expanded to nothing would go green vacuously.
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """)
    allow = tmp_path / "allow.yaml"
    allow.write_text("renderers: []\nsource_fed_slots: []\n")
    rc = cl.main(["--root", root, "--allowlist", str(allow), "--changed"])
    assert rc == 2
    assert "--changed" in capsys.readouterr().err


def test_main_omitting_changed_still_enforces_everything(tmp_path, capsys):
    # Omitting --changed entirely is a different, valid mode: changed is
    # None, meaning "enforce everything", and must still work after the
    # empty-list guard is added.
    root = write(tmp_path, "x.yaml", """
        passThrough:
        - function: p.C#<init>
          copy:
          - from: arg(0)
            to:
            - this
            - .p.C#userName#java.lang.Object
        """)
    allow = tmp_path / "allow.yaml"
    allow.write_text("renderers: []\nsource_fed_slots: []\n")
    rc = cl.main(["--root", root, "--allowlist", str(allow)])
    assert rc == 1
    out = capsys.readouterr().out
    assert "FAIL I2" in out


def test_main_rejects_a_missing_allowlist(tmp_path, capsys):
    (tmp_path / "cfg").mkdir()
    rc = cl.main(["--root", str(tmp_path / "cfg"),
                  "--allowlist", str(tmp_path / "nope.yaml")])
    assert rc == 2
    assert "allowlist not found" in capsys.readouterr().err


# ---- --compare-ref: gate on new findings, not whole files ----

_ORPHAN_ITEM = """
    - function: p.C#<init>
      copy:
      - from: arg(0)
        to:
        - this
        - .p.C#userName#java.lang.Object
    """

_MATCHED_PAIR_ITEM = """
    - function: p.C#getPath
      copy:
      - from:
        - this
        - .p.C#path#java.lang.Object
        to: result
    - function: p.C#setPath
      copy:
      - from: arg(0)
        to:
        - this
        - .p.C#path#java.lang.Object
    """


def yaml_doc(*items):
    """A passThrough YAML document made of one or more dedented list-item blocks."""
    return "passThrough:\n" + "".join(textwrap.dedent(i) for i in items)


def init_git_repo(tmp_path):
    """A throwaway repo under tmp_path; never touches the real project history."""
    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args):
        subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True, text=True)

    git("init", "-q")
    git("config", "user.email", "test@example.com")
    git("config", "user.name", "Test")
    return repo, git


def write_allow(tmp_path):
    allow = tmp_path / "allow.yaml"
    allow.write_text("renderers: []\nsource_fed_slots: []\n")
    return str(allow)


def test_compare_ref_preexisting_finding_is_not_a_failure_but_is_without_it(tmp_path):
    repo, git = init_git_repo(tmp_path)
    (repo / "x.yaml").write_text(yaml_doc(_ORPHAN_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "ref: orphan slot")
    ref_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                              capture_output=True, text=True, check=True).stdout.strip()

    # Touch the file, but keep the original orphan-slot finding byte-identical.
    (repo / "x.yaml").write_text(yaml_doc(_ORPHAN_ITEM, _MATCHED_PAIR_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "unrelated touch")

    allow_path = write_allow(tmp_path)

    failures, reports, preexisting = cl.run(
        str(repo), allow_path, changed={"x.yaml"}, gate_i6=False, compare_ref=ref_sha)
    assert failures == []
    assert [f.code for f in preexisting] == ["I2"]
    assert reports == []

    failures_no_ref, _, _ = cl.run(
        str(repo), allow_path, changed={"x.yaml"}, gate_i6=False, compare_ref=None)
    assert [f.code for f in failures_no_ref] == ["I2"]


def test_compare_ref_new_finding_is_a_failure(tmp_path):
    repo, git = init_git_repo(tmp_path)
    (repo / "x.yaml").write_text(yaml_doc(_MATCHED_PAIR_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "ref: clean")
    ref_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                              capture_output=True, text=True, check=True).stdout.strip()

    (repo / "x.yaml").write_text(yaml_doc(_MATCHED_PAIR_ITEM, _ORPHAN_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "introduce orphan slot")

    allow_path = write_allow(tmp_path)
    failures, _, preexisting = cl.run(
        str(repo), allow_path, changed={"x.yaml"}, gate_i6=False, compare_ref=ref_sha)
    assert [f.code for f in failures] == ["I2"]
    assert preexisting == []


def test_compare_ref_unresolvable_exits_2(tmp_path, capsys):
    repo, git = init_git_repo(tmp_path)
    (repo / "x.yaml").write_text(yaml_doc(_ORPHAN_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "initial")

    allow_path = write_allow(tmp_path)
    rc = cl.main(["--root", str(repo), "--allowlist", allow_path,
                  "--changed", "x.yaml", "--compare-ref", "not-a-real-ref"])
    assert rc == 2
    assert "not-a-real-ref" in capsys.readouterr().err


def test_main_rejects_an_unresolvable_compare_ref_without_changed(tmp_path, capsys):
    repo, git = init_git_repo(tmp_path)
    (repo / "x.yaml").write_text(yaml_doc(_MATCHED_PAIR_ITEM))
    git("add", "x.yaml")
    git("commit", "-q", "-m", "initial")

    allow_path = write_allow(tmp_path)
    rc = cl.main(["--root", str(repo), "--allowlist", allow_path,
                  "--compare-ref", "not-a-real-ref-xyz"])
    assert rc == 2
    assert "not-a-real-ref-xyz" in capsys.readouterr().err
