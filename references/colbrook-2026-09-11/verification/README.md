# Supporting diagnostics, not independent proof review

`check_results.py` is the script supplied in the preceding conversation. Only its
opening provenance description was clarified for this package; the mathematical
checks were not changed. `previous-results.txt` preserves the supplied run output.
`rerun-results.txt` records the packaging run on 11 September 2026.

Run from this directory in a Python environment with the listed dependencies:

```bash
python3 -m pip install -r requirements.txt
python3 check_results.py
```

The recorded environment used Python 3.13.5. The tests cover an exact symbolic
IS-02 identity, rational SP-04 bounds and numerical stationary values, 84 SP-05
positive-definite pairs, 2,800 KE-04 intervals, and 400 KE-03 shift-geometry cases.
They do not independently validate the universal mathematical claims.

In particular, the KE-03 tests do not implement the full exact-query algorithm
or establish numerical stability. A same-assistant rerun is not independent
mathematical verification.
