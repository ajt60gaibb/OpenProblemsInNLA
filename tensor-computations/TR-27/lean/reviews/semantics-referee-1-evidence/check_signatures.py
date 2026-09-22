#!/usr/bin/env python3
"""Review aid: textual signatures and hashes, not a Comparator replacement."""
from pathlib import Path
import hashlib
import json
import re


root = Path(__file__).resolve().parents[2]
receipt = json.loads((Path(__file__).parent / 'input-and-signature-receipt.json').read_text())
for path, expected in receipt['sha256'].items():
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    assert actual == expected, (path, expected, actual)

challenge = (root / 'Challenge.lean').read_text()
solution = (root / 'NLA/TR27/Semantics.lean').read_text()
for declaration in receipt['signature_checks']:
    name = declaration.removeprefix('NLA.TR27.')
    pattern = r'\btheorem\s+' + re.escape(name) + r'\b(?P<sig>.*?)\s*:='
    expected = list(re.finditer(pattern, challenge, re.S))
    actual = list(re.finditer(pattern, solution, re.S))
    assert len(expected) == len(actual) == 1, declaration
    assert ' '.join(expected[0]['sig'].split()) == ' '.join(actual[0]['sig'].split()), declaration
assert not re.search(r'(?m)^\s*(axiom|opaque|constant)\b|\b(sorry|admit|native_decide|implemented_by)\b', solution)
assert 'import Challenge' not in solution
print('PASS: all five signatures agree; all input hashes match; forbidden source markers absent.')
