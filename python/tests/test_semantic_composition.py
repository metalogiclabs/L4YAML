"""Source-pinned experimental composition: PR #300 + PR #370.

The native parse/dump tests need the L4YAML C library; run with
  L4YAML_LIB=/path/to/libl4yaml.so PYTHONPATH=python pytest -q python/tests/test_semantic_composition.py

This is a bounded regression suite, NOT a universal preservation theorem.
A compatibility dict loses YAML key identity, intentionally recorded here as
an observed limitation; the tests do not endorse that as a lossless contract.
"""
import pytest

l4yaml = pytest.importorskip("l4yaml")
from l4yaml.compat import safe_load, safe_dump, to_python


def typed(v):
    """Type-sensitive recursive comparison (bool == int is insufficient)."""
    if type(v) is dict:
        return sorted(((type(k).__name__, repr(k), typed(x)) for k, x in v.items()), key=repr)
    if type(v) is list:
        return [typed(x) for x in v]
    return (type(v).__name__, v)


@pytest.mark.parametrize("source, expected", [
    ("!<tag:yaml.org,2002:str> true", "true"),
    ("!<tag:yaml.org,2002:int> 5", 5),
    ("!!str 42", "42"),
    ("!<tag:yaml.org,2002:seq> [a, b]", ["a", "b"]),
    ("!<tag:yaml.org,2002:map> {k: v}", {"k": "v"}),
    ("%TAG !e! tag:example.com,2000:\n---\n!e!foo bar", "bar"),
])
def test_native_parse_dump_reparse_tags_and_types(source, expected):
    before = l4yaml.load(source)
    rendered = l4yaml.dump_configured(before, config_yaml="plainCoreScalars: false")
    after = l4yaml.load(rendered)
    assert before.tag == after.tag, (source, before.tag, rendered, after.tag)
    assert typed(to_python(before)) == typed(to_python(after))
    assert typed(to_python(after)) == typed(expected)


@pytest.mark.parametrize("source, expected", [
    ("1_000", "1_000"), ("012", 12), ('"42"', "42"),
    ("true", True), ("!<tag:yaml.org,2002:str> true", "true"),
])
def test_python_numeric_and_dump_composition(source, expected):
    value = safe_load(source)
    assert typed(value) == typed(expected)
    output = safe_dump(value)
    assert typed(safe_load(output)) == typed(value)


def test_python_dict_collapses_distinct_yaml_core_key_types():
    source = "true: bool\n1: int\n1.0: float\n"
    raw = l4yaml.load(source)
    assert len(raw.raw_items()) == 3
    native = safe_load(source)
    assert len(native) == 1
    assert next(iter(native)) is True
    assert native[True] == "float"


def test_python_dict_conflates_equivalent_numeric_keys():
    source = "0o13: first\n0xB: second\n"
    raw = l4yaml.load(source)
    assert len(raw.raw_items()) == 2
    native = safe_load(source)
    assert len(native) == 1
    assert native[11] == "second"
