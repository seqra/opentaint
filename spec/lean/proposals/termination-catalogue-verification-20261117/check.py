#!/usr/bin/env python3
"""Verify catalogue references and run conservative reply controls in Lean 4.35."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROOFS = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent

# Observer mark, freeze a complete receipt after this run, and natural stop.
BOUND = {
    "BoundBody": (1, 5, 9),
    "BoundUniform": (2, 7, 11),
    "BoundOldExact": (2, 5, 9),
    "BoundOldMark": (2, 5, 9),
    "BoundOldField": (2, 7, 11),
    "BoundOldRelevant": (1, 5, 9),
    "BoundOldUnrelated": (2, 7, 11),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies(directory):
    audit = directory / "audit-proofs" / "receipt.json"
    guard = json.loads((directory / "guarded-receipt.json").read_text())
    assert sha(audit) == guard["parentReceiptSha256"]
    assert sha(Path(guard["source"])) == guard["sha256"]
    receipt = json.loads(audit.read_text())
    for model in receipt["models"].values():
        assert sha(Path(model["source"])) == model["sha256"]
    condensed = Path(receipt["parentReceipt"])
    assert sha(condensed) == receipt["parentReceiptSha256"]
    parent = json.loads(condensed.read_text())
    earlier = Path(parent["parentReceipt"])
    assert sha(earlier) == parent["parentReceiptSha256"]
    return [audit.parent, condensed.parent, earlier.parent], guard["auditedDeclarations"]


def audit_axioms(out, env, module, source):
    content = source.read_text()
    code = re.sub(r"/-.*?-/", "", content, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    assert not re.search(r"^\s*(axiom|constant|classical)\b|\b(sorry|admit|native_decide)\b", code, re.M)
    scopes = []
    claims = []
    for keyword, name in re.findall(r"^(namespace|end|theorem) (\w+)", content, re.M):
        if keyword == "namespace":
            scopes.append(name)
        elif keyword == "end" and scopes and scopes[-1] == name:
            scopes.pop()
        elif keyword == "theorem":
            claims.append(".".join([*scopes, name]))
    queries = out / f"{module}Axioms.lean"
    queries.write_text(f"import {module}\n" + "".join(f"#print axioms {name}\n" for name in claims))
    report = run_lean(out, env, f"{module}.axioms.log", str(queries))
    found = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", report)
    assert len(found) == len(claims), report
    for name, axioms in found:
        assert set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound"}, (name, axioms)
    return len(claims)


def run_lean(out, env, log, *args):
    result = subprocess.run(["lean", *args], cwd=out, env=env, text=True, capture_output=True)
    report = result.stdout + result.stderr
    (out / log).write_text(report)
    assert result.returncode == 0 and "warning:" not in report, f"{log}\n{report}"
    return report


def compile_module(out, env, source):
    local = out / source.name
    if local != source:
        local.write_bytes(source.read_bytes())
    run_lean(out, env, f"{source.stem}.log", "-o", str(local.with_suffix(".olean")), local.name)


def bound_control(out, env, name, observer, witness_run, stop):
    source = (PROOFS / "native-bound-reply-service-20261117" / f"{name}.lean").read_text()
    namespace = name + "Conservative"
    source = re.sub(rf"\b{name}\b", namespace, source)
    # Preserve the saved-first packets and the matching/publishing equations.
    # Forward all applicable results when no omission has a certificate.
    start = source.index("  let ready := complete.filter (delivered native)")
    end = source.index("\ndef normalizeContinuation", start)
    source = source[:start] + "  let _ := (enabled, complete, services, closed)\n  packet native\n" + source[end:]
    fold = "  UniformActual.foldValues (!enabled || back) [] (packet vs)"
    assert source.count(fold) == 1, name
    source = source.replace(fold, "  let _ := (enabled, back)\n  packet vs")
    control = out / f"{namespace}.lean"
    control.write_text(source)
    compile_module(out, env, control)

    path = out / f"{name}Root.lean"
    path.write_text(f"""import BoundReplay
import {namespace}

namespace {name}Root
open NonEmptyPolicy NonEmptyRestriction BoundReplay
open {namespace}

local instance : Inhabited State := ⟨initial⟩

def slice : Slice := ⟨originalSource,gen,colors,consumeH⟩
def paths : List (List Hop) := receives slice (fun value => value.ap.mark == some {observer})
def model : TerminalReplay.Model State where
  initial := initial
  step := step false
  required := List.range paths.length
  witnesses run previous current :=
    if !previous.sourceAllowed then [] else
    let view : RunView :=
      ⟨current.data.offers,current.data.raw,views false previous.saved,
        fun actual => candidates run (limit run) false previous.rows previous.saved [actual],
        fun flag edge actual => readBound edge actual flag⟩
    (List.range paths.length).filter fun i => witnessed view paths[i]!
  omitRoot state := {{state with observationActive := false}}

theorem the_inactive_state_never_revives (run : Nat) (s : State)
    (noSource : s.sourceAllowed = false) (noTarget : s.observationActive = false)
    (idle : s = quiet s.report s.saved s.complete s.services) :
    TerminalReplay.advance model run ⟨s,receipts⟩ = ⟨s,receipts.eraseDups⟩ ∨
    TerminalReplay.advance model run ⟨s,receipts⟩ = ⟨s,receipts⟩ := by
  have fixed : model.step run s = s := by
    change step false run s = s
    rw [idle]
    exact quiet_never_restarts false run _ _ _ _
  have same : model.omitRoot s = s := by
    change ({{s with observationActive := false}} : State) = s
    cases s
    simp_all
  have noNew : model.witnesses run s s = [] := by simp [model,noSource]
  simp only [TerminalReplay.advance,fixed,same,noNew,List.append_nil,ite_self]
  split <;> simp

#eval do
  let runs := (List.range {stop}).scanl (fun frame k => TerminalReplay.advance model (k+1) frame)
    ⟨model.initial,[]⟩
  let controls := (List.range {stop+2}).scanl (fun frame k => step false (k+1) frame) initial
  let mut trace := []
  for run in List.range' 1 {stop} do
    let prior := runs[run-1]!.body
    let now := runs[run]!
    let active := if run % 2 == 0 then prior.observationActive else prior.sourceAllowed
    if active && !(decide (round false run (limit run) prior.rows prior.saved prior.complete
        prior.services now.body.data = now.body.data)) then
      throw (IO.userError s!"run-{{run}} did not finish its within-run fixed point")
    if run % 2 == 1 then
      trace := trace ++ [(run, now.witnessed, now.body.rows.length, now.body.observationActive, now.body.report)]
    if stopped run now.body != (run == {stop}) then
      throw (IO.userError s!"unexpected stop at run-{{run}}: {{trace}}")
  let w := runs[{witness_run}]!
  let final := runs[{stop}]!
  if paths.length != 1 || w.witnessed != model.required || !final.body.report ||
      decide (final.body != quiet true final.body.saved final.body.complete final.body.services) then
    throw (IO.userError s!"incomplete service at stop: {{trace}}")
  if !controls[{stop}]!.observationActive then
    throw (IO.userError "conservative control stopped")
  IO.println s!"{name} {{trace}}"

end {name}Root
""")
    compile_module(out, env, path)
    count = audit_axioms(out, env, path.stem, path)
    return name, {"observer": observer, "witnessRun": witness_run, "latestRun": stop, "proofs": count,
                  "controlSha256": sha(control), "checkSha256": sha(path)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    deps, previous_claims = dependencies(args.audit.resolve())
    env = {**os.environ, "ELAN_TOOLCHAIN": "leanprover/lean4:v4.35.0",
           "LEAN_PATH": os.pathsep.join(map(str, [out, *deps]))}
    claims = 0
    for source in sorted(HERE.glob("*.lean"), key=lambda s: (s.name != "TerminalReplay.lean", s.name)):
        compile_module(out, env, source)
        if source.stem != "Catalogue":
            claims += audit_axioms(out, env, source.stem, source)
    with ThreadPoolExecutor(max_workers=3) as pool:
        checked = dict(pool.map(lambda item: bound_control(out, env, item[0], *item[1]), BOUND.items()))
    claims += sum(info["proofs"] for info in checked.values())
    (out / "receipt.json").write_text(json.dumps({
        "status": "PASS", "boundControls": checked, "newClaims": claims, "cumulativeClaims": previous_claims + claims,
        "wholeEngineVerified": False}, indent=2) + "\n")
    print(json.dumps(checked, indent=2))


if __name__ == "__main__":
    main()
