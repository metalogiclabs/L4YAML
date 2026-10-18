#!/usr/bin/env python3
"""Source-pinned refute-first verifier of L4YAML headline YAML acceptance claims.

Scientific limits:
- PyYAML and ruamel.yaml are two independent executable reference oracles,
  NOT a formal definition or proof of the normative YAML 1.2.2 language.
- This is not blind bug discovery. The self-reference boundary was already
  documented in L4YAML; other composite cases are independent new probes.
- A passing Lean build proves no universal conformance property.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from io import StringIO

PIN = "bca37392fdcb80481342a186a37ab37a5ede6e46"
ROOT = Path(__file__).resolve().parent
CASE_FILE = ROOT / "cases.json"
REF_PATH = ROOT / "reference.json"
PROBE_PATH = ROOT / "Probe.lean"
NATIVE_OUT = ROOT / "native.out"
SUMMARY = ROOT / "summary.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def classify_oracles(source):
    import yaml
    from ruamel.yaml import YAML
    result = {}
    for name, parse in (
        ("pyyaml", lambda: list(yaml.compose_all(source))),
        ("ruamel", lambda: list(YAML(typ="base", pure=True).compose_all(StringIO(source)))),
    ):
        try:
            parse()
            result[name] = {"verdict": "ACCEPT"}
        except Exception as error:
            result[name] = {"verdict": "REJECT", "error_class": type(error).__name__}
    return result


def load_cases():
    records = json.loads(CASE_FILE.read_text(encoding="utf-8"))
    assert len(records) >= 10
    ids = [record["id"] for record in records]
    assert len(ids) == len(set(ids)) and all(re.fullmatch(r"[a-z0-9_]+", x) for x in ids)
    assert all(isinstance(r["source"], str) and len(r["source"]) < 500 for r in records)
    return records


def prepare():
    import yaml
    import ruamel.yaml
    records = load_cases()
    reports = []
    for record in records:
        oracles = classify_oracles(record["source"])
        agree = oracles["pyyaml"]["verdict"] == oracles["ruamel"]["verdict"]
        reports.append({
            "id": record["id"],
            "source": record["source"],
            "oracles": oracles,
            "oracles_agree": agree,
            "reference_verdict": oracles["pyyaml"]["verdict"] if agree else "UNKNOWN",
        })
    if not all(r["oracles_agree"] for r in reports):
        raise RuntimeError("Oracle disagreement: stop without issuing a comparison verdict")
    evidence = {
        "upstream_pin": PIN,
        "case_sha256": digest(CASE_FILE.read_bytes()),
        "reference_tool_versions": {"pyyaml": yaml.__version__, "ruamel.yaml": ruamel.yaml.__version__},
        "scope": "Finite independent parser-acceptance differential, NOT YAML 1.2.2 completeness",
        "cases": reports,
    }
    REF_PATH.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lean = [
        "module",
        "public import L4YAML.Parser.Composition",
        "public meta import L4YAML.Parser.Composition",
        "@[expose] public section MathGraphRefuteFirst",
        "open L4YAML",
        "",
    ]
    for record in records:
        source_literal = json.dumps(record["source"], ensure_ascii=True)
        prefix = "MG_AUDIT|" + record["id"] + "|"
        lean.append(
            "#eval if (L4YAML.TokenParser.parseYaml " + source_literal +
            ").isOk then " + json.dumps(prefix + "ACCEPT") +
            " else " + json.dumps(prefix + "REJECT")
        )
    lean += ["", "end MathGraphRefuteFirst", ""]
    PROBE_PATH.write_text("\n".join(lean), encoding="utf-8")
    print("PREPARED " + str(len(records)) + " cases, all reference oracles agree")
    print("case SHA256 " + evidence["case_sha256"])


def compare():
    reference = json.loads(REF_PATH.read_text(encoding="utf-8"))
    assert reference["upstream_pin"] == PIN
    assert reference["case_sha256"] == digest(CASE_FILE.read_bytes())
    expected = {record["id"]: record for record in reference["cases"]}
    raw = NATIVE_OUT.read_text(encoding="utf-8")
    native = {}
    for line in raw.splitlines():
        match = re.fullmatch(r"\s*MG_AUDIT\|([a-z0-9_]+)\|(ACCEPT|REJECT)\s*", line)
        if match:
            key, outcome = match.groups()
            if key in native:
                raise RuntimeError("Duplicate native observation: " + key)
            native[key] = outcome
    if set(native) != set(expected):
        missing = sorted(set(expected) - set(native))
        extra = sorted(set(native) - set(expected))
        raise RuntimeError("Missing/extra native observations: " + str((missing, extra)))
    if set(native.values()) != {"ACCEPT", "REJECT"}:
        raise RuntimeError("Native verdict instrument failed polarity control")
    mismatch = []
    matches = []
    for key, native_outcome in native.items():
        record = expected[key]
        verdict = record["reference_verdict"]
        details = {"id": key, "reference": verdict, "native": native_outcome,
                   "source": record["source"]}
        (matches if verdict == native_outcome else mismatch).append(details)
    readme = Path("README.md").read_text(encoding="utf-8")
    headline = (
        "Conformance to the [YAML 1.2.2 specification]" in readme
        and "is established" in readme
    )
    scope_note = "NOT the target: this statement is false" in readme
    label = "COUNTEREXAMPLES_TO_UNQUALIFIED_ACCEPTANCE" if mismatch else "NO_DISAGREEMENT_IN_FINITE_SET"
    summary = {
        "upstream_pin": PIN,
        "branch_parent_pin_verified_by_workflow": True,
        "case_sha256": reference["case_sha256"],
        "scope": "Finite two-reference differential at native L4YAML acceptance boundary",
        "verdict": label,
        "not_new_discovery_warning": "Self-referential alias mismatch is known in upstream documentation",
        "universal_yaml_conformance": "NOT ESTABLISHED BY THIS EXPERIMENT",
        "readme_broad_conformance_headline": headline,
        "readme_acknowledges_false_old_capstone": scope_note,
        "total_cases": len(native),
        "agreement_count": len(matches),
        "difference_count": len(mismatch),
        "differences": sorted(mismatch, key=lambda e: e["id"]),
        "matches": sorted(matches, key=lambda e: e["id"]),
    }
    SUMMARY.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("RESULT " + label)
    print(str(len(matches)) + " matches; " + str(len(mismatch)) + " divergences")
    for entry in sorted(mismatch, key=lambda x: x["id"]):
        print("DIFF " + entry["id"] + " reference=" + entry["reference"] +
              " native=" + entry["native"])
    if headline and scope_note:
        print("CLAIM_SCOPE_WARNING: README headline broad; later section disclaims old biconditional")
    print("Universal normative YAML correctness: UNKNOWN (not implied by finite oracles)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("prepare", "compare"))
    args = parser.parse_args()
    try:
        {"prepare": prepare, "compare": compare}[args.command]()
    except Exception as e:
        print("AUDIT_INSTRUMENT_ERROR: " + str(e), file=sys.stderr)
        sys.exit(2)
