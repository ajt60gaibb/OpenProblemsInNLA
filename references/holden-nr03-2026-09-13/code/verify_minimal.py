#!/usr/bin/env python3
"""A deliberately small, construction-independent check of the n=7 witness."""
import json
from pathlib import Path

path = Path(__file__).resolve().parents[1] / "data" / "factors_n7.json"
c = json.loads(path.read_text())
W, H, d = c["W"], c["H_scaled"], c["denominators"]

def check(condition, message):
    if not condition:
        raise ValueError(message)

check(c["n"] == 7 and c["r"] == 127, "Wrong dimensions in metadata")
check(len(W) == 128 and all(len(row) == 127 for row in W), "Wrong W shape")
check(len(H) == 127 and all(len(row) == 128 for row in H), "Wrong H shape")
check(len(d) == 128 and all(type(x) is int and x > 0 for x in d), "Invalid d")
check(all(type(x) is int and x >= 0 for row in W + H for x in row), "Invalid factors")
for a in range(128):
    for b in range(128):
        actual = sum(W[a][k] * H[k][b] for k in range(127))
        expected = d[b] * (1 - (a & b).bit_count()) ** 2
        check(actual == expected, f"Incorrect entry ({a},{b})")
print("PASS: all 16384 exact entries; C_7 = W (H_scaled diag(1/d)), 127 < 128.")
