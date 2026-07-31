# /// script
# requires-python = ">=3.9"
# ///
"""
Summarize an OpenTaint test-result.json so the agent never parses it by hand.
Prints pass/fail counts and names every failing sample by verdict.
Exit 0 when all samples pass, 1 when any fail, 2 on a bad/missing file.
Works for both `test rule run` and `test approximation run` outputs (same shape).
"""
import json
import sys
from pathlib import Path

BUCKETS = ["success", "falseNegative", "falsePositive", "skipped", "disabled"]


def one(x):
    # a sample entry is usually {className, methodName, rule:{ruleId}, ...}; the method name alone
    # identifies it — the class and rule are already clear from the batch/unit being tested
    if isinstance(x, dict):
        return x.get("methodName") or x.get("className") or str(x)
    return str(x)


def names(v):
    # a bucket may be a list of sample entries or a bare count; normalize to a printable list
    if isinstance(v, list):
        return [one(x) for x in v]
    if isinstance(v, int):
        return [f"<{v} sample(s)>"] if v else []
    return [one(v)] if v else []


def resolve(arg):
    # accept either a full path to a test-result.json or a shorthand id under
    # .opentaint/test-results/: a rule `<unit>/<side>` or an approximation `<batch>`
    if arg.endswith("test-result.json"):
        return Path(arg)
    return Path(".opentaint/test-results") / arg / "test-result.json"


def main():
    if len(sys.argv) != 2:
        print("usage: check-test-result.py <unit>/<side> | <batch> | <path-to-test-result.json>")
        return 2
    p = resolve(sys.argv[1])
    if not p.is_file():
        print(f"no test-result.json at {p}")
        return 2
    try:
        doc = json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:
        print(f"cannot parse {p}: {e}")
        return 2

    got = {b: names(doc.get(b, [])) for b in BUCKETS}
    passed = len(got["success"])
    failed = sum(len(got[b]) for b in ("falseNegative", "falsePositive", "skipped", "disabled"))
    total = passed + failed

    print(f"{p}: {passed}/{total} passing"
          + (f", {failed} FAILING" if failed else " — all pass"))
    for b in ("falseNegative", "falsePositive", "skipped", "disabled"):
        if got[b]:
            print(f"\n{b} ({len(got[b])}):")
            for n in got[b]:
                print(f"  {n}")
    if not failed:
        print("\nnext: all samples pass — append to build.done and return")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
