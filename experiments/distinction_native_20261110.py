"""Research-only native distinction audit; never install as an upstream test.

Run against a built, source-pinned L4YAML shared library:
  PYTHONPATH=python L4YAML_LIB=ffi/out/libl4yaml.so python3 experiments/distinction_native_20261110.py

This is a diagnostic: observed violations do not fail the process. Missing
imports, failed controls, and absent observations fail closed.
"""
from __future__ import annotations

import json
import subprocess
import sys
from typing import Any


def report(name: str, **fields: Any) -> None:
    print("DISTINCTION " + json.dumps({"case": name, **fields},
                                      ensure_ascii=True, default=repr), flush=True)


def repr_keys(value: Any) -> list[str]:
    return [f"{type(k).__name__}:{k!r}" for k in value]


def main() -> int:
    import l4yaml
    from l4yaml.compat import safe_dump, safe_load

    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    report("source", sha=head, toolchain=open("lean-toolchain", encoding="utf-8").read().strip())

    control_raw = l4yaml.load("alpha: first\nbeta: second\n")
    control_native = safe_load("alpha: first\nbeta: second\n")
    if len(control_raw) != 2 or control_native != {"alpha": "first", "beta": "second"}:
        report("control-failure", raw_count=len(control_raw), native=repr(control_native))
        return 2
    report("control", raw_count=len(control_raw), native=repr(control_native), passed=True)

    key_pairs = [
        ("bool-vs-int", "true: boolean-value\n1: integer-value\n"),
        ("int-vs-float", "1: integer-value\n1.0: float-value\n"),
        ("core-binary-vs-int", "0b10: string-value\n2: integer-value\n"),
        ("core-underscore-vs-int", "1_000: string-value\n1000: integer-value\n"),
        ("explicit-str-vs-bool", "!!str false: string-value\nfalse: boolean-value\n"),
        ("duplicate-literal-keys", "x: first\nx: second\n"),
    ]
    observed = 0
    for name, source in key_pairs:
        try:
            raw = l4yaml.load(source)
            raw_keys = []
            for k, _ in raw.raw_items():
                raw_keys.append({"content": k.as_str(), "tag": k.tag, "style": k.style})
            native = safe_load(source)
            report(name, raw_count=len(raw), raw_keys=raw_keys,
                   native_count=len(native) if isinstance(native, dict) else None,
                   native_repr=repr(native),
                   native_keys=repr_keys(native) if isinstance(native, dict) else None,
                   count_preserved=isinstance(native, dict) and len(native) == len(raw))
        except Exception as exc:
            report(name, error_type=type(exc).__name__, error=str(exc))
        observed += 1

    bom_cases: list[tuple[str, Any]] = [
        ("bom-root-string", "\ufeffhello"),
        ("bom-root-false", "\ufefffalse"),
        ("bom-first-key", {"\ufeffrole": "admin"}),
        ("bom-later-key-control", {"x": "ok", "\ufeffrole": "admin"}),
    ]
    for name, original in bom_cases:
        try:
            encoded = safe_dump(original)
            decoded = safe_load(encoded)
            report(name, original_repr=repr(original), encoded_repr=repr(encoded),
                   decoded_repr=repr(decoded), equal=decoded == original)
        except Exception as exc:
            report(name, original_repr=repr(original), error_type=type(exc).__name__,
                   error=str(exc))
        observed += 1

    report("diagnostic-summary", cases_observed=observed,
           note="Diagnostic completed; semantic mismatches are intentionally not CI failures")
    return 0 if observed == 10 else 3


if __name__ == "__main__":
    sys.exit(main())
